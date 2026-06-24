open Soteria_c_lib
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
module Mu = Usable_mucore
open Mu
module Diagnostic = Soteria.Terminal.Diagnostic
module Or_gave_up = Soteria.Symex.Or_gave_up

type error = [ Error.t | Csymex.cons_fail ]

let verif_process ~loc (args : Mu.arguments) return_type labels body =
  let open Csymex in
  let open Syntax in
  let lsubst = Csymex.Value.Expr.Subst.empty in
  let* (csubst, state), lsubst =
    Producer.run ~subst:lsubst (Cn_assert.produce_arguments args)
  in
  let** result, state =
    State.SM.Result.run_with_state ~state
    @@ Minterp.eval_expr ~labels csubst body
    |> Result.map_error (fun ((err, _), _) -> (err :> error))
  in
  let ret = Minterp.ExprM.returned_value result in
  let++ _ =
    Consumer.run ~subst:lsubst
      (Cn_assert.consume_return_type return_type ret csubst state)
    |> Result.map_error (fun err -> (err :> error))
  in
  ()

(* Render a single [error] (either a soteria-c memory error or a logical
   consumption failure coming from the symex engine). *)
let pp_error ft : error -> unit = function
  | #Error.t as e -> Error.pp ft e
  | #Csymex.cons_fail as e -> Csymex.pp_cons_fail ft e

let severity_of_error : error -> Diagnostic.severity = function
  | #Error.t as e -> Error.severity e
  | #Csymex.cons_fail -> Diagnostic.Error

(* Print a [Soteria.Terminal.Diagnostic] for one symbolic-execution outcome.
   A branch that terminated without an error nor a give-up is a successful
   verification of that path, reported as a [Note]. *)
let print_result ((res, _pc) : (_, error Or_gave_up.t, _) Compo_res.t * _) =
  match res with
  | Compo_res.Ok () ->
      Diagnostic.print_diagnostic_simple ~severity:Note "success"
  | Compo_res.Error (Or_gave_up.E err) ->
      Diagnostic.print_diagnostic_simple ~severity:(severity_of_error err)
        (Fmt.to_to_string pp_error err)
  | Compo_res.Error (Or_gave_up.Gave_up msg) ->
      Diagnostic.print_diagnostic_simple ~severity:Warning
        (Fmt.str "Analysis gave up: %s" msg)
  | Compo_res.Missing _ ->
      Diagnostic.print_diagnostic_simple ~severity:Error
        "Missing resource (under-specified)"

(* Verify a single (non-trusted) function, returning every branch outcome. *)
let verify_fn ~fuel:_ ~loc (_name : Sym.t) args return_type labels body =
  [%l.debug
    "@[<v 2>verify_fn:@.arguments: %a@.return_type: %a@]" Mu.pp_arguments args
      Mu.pp_return_type return_type];
  [%l.debug
    "@[<v 2>Specifically within:@ ret: %a@ logic: %a@]" Mu.pp_bt
      (snd return_type.ret) Mu.pp_logical_return return_type.logic];
  let process = verif_process ~loc args return_type labels body in
  Csymex.Result.run ~mode:OX ~stats:Caller process

(* Verify every checked function of [prog], skipping the ones the user marked as
   trusted as well as the bare declarations (which have no body to check), and
   printing a diagnostic for each branch outcome. *)
let verify_prog ~fuel (prog : Mu.file) : (unit, string) Result.t =
  let@ () = Soteria.Stats.As_ctx.with_dumped () in
  Sym.Map.iter
    (fun name decl ->
      match decl with
      | Proc { trusted = Checked; args; return_type; body; labels; loc } ->
          verify_fn ~fuel ~loc name args return_type labels body
          |> List.iter print_result
      | Proc { trusted = Trusted loc; _ } ->
          L.info (fun m ->
              m "Skipping trusted function %a (%a)" Sym.pp name pp_loc loc)
      | ProcDecl _ -> ())
    prog.funs;
  Ok ()
