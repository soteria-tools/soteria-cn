open Soteria_c_lib
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
module Mu = Usable_mucore
open Mu

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
  let** _ =
    Consumer.run ~subst:lsubst
      (Cn_assert.consume_return_type return_type ret csubst state)
    |> Result.map_error (fun err -> (err :> error))
  in
  not_impl "verif_process: not implemented yet"

(* Verify a single (non-trusted) function. *)
let verify_fn ~fuel ~loc (name : Sym.t) args return_type labels body :
    (unit, string) Result.t =
  [%l.debug
    "@[<v 2>verify_fn:@.arguments: %a@.return_type: %a@]" Mu.pp_arguments args
      Mu.pp_return_type return_type];
  [%l.debug
    "@[<v 2>Specifically within:@ ret: %a@ logic: %a@]" Mu.pp_bt
      (snd return_type.ret) Mu.pp_logical_return return_type.logic];
  let process = verif_process ~loc args return_type labels body in
  let _results = Csymex.Result.run ~mode:OX process in
  Result.error "not impl"

(* Verify every checked function of [prog], skipping the ones the user marked as
   trusted as well as the bare declarations (which have no body to check). *)
let verify_prog ~fuel (prog : Mu.file) : (unit, string) Result.t =
  let open Syntaxes.Result in
  Sym.Map.fold
    (fun name decl acc ->
      let* () = acc in
      match decl with
      | Proc { trusted = Checked; args; return_type; body; labels; loc } ->
          verify_fn ~fuel ~loc name args return_type labels body
      | Proc { trusted = Trusted loc; _ } ->
          L.info (fun m ->
              m "Skipping trusted function %a (%a)" Sym.pp name pp_loc loc);
          Ok ()
      | ProcDecl _ -> Ok ())
    prog.funs (Ok ())
