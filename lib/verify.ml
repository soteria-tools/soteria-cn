module State_here = State
open Soteria_c_lib
module State = State_here
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
module Mu = Usable_mucore
open Mu
module Diagnostic = Soteria.Terminal.Diagnostic
module Or_gave_up = Soteria.Symex.Or_gave_up

let with_extra_call_trace ~loc ~msg : 'a Csymex.t -> 'a Csymex.t =
  Csymex.Result.map_error @@ fun (e, tr) ->
  let elem = Soteria.Terminal.Call_trace.mk_element ~loc ~msg () in
  (e, elem :: tr)

let verif_process ~loc (args : Mu.arguments) return_type labels body =
  let open Csymex in
  let open Syntax in
  let@@ () = with_extra_call_trace ~loc ~msg:"Verifying function" in
  [%l.debug "Producing pre-condition"];
  let* subst, state = Cn_assert.produce_arguments args in
  [%l.debug
    "@[<v 2>About to execute function body with:@ @[<v 2>subst: %a@]@ @[<v \
     2>state: %a@]@]"
    Subst.pp subst
      (Fmt.Dump.option @@ Soteria_c_lib.State.pp_pretty ~ignore_freed:true)
      state];
  Csymex.log_solver_state ~level:Trace ();
  let** result, state =
    State.SM.Result.run_with_state ~state
    @@ Minterp.eval_expr ~labels subst body
    |> Result.map_error (fun ((err, tr), _) -> ((err :> Minterp.error), tr))
  in
  let ret = Minterp.ExprM.returned_value result in
  let** _, st =
    Cn_assert.consume_return_type return_type ret subst state
    |> Result.map_error (fun (err, tr) -> ((err :> Minterp.error), tr))
  in
  let fn_call_trace elements =
    elements
    @ [
        Soteria.Terminal.Call_trace.mk_element ~loc
          ~msg:"Memory leftover after this function" ();
      ]
  in
  match State.leaks st with
  | [] -> Result.ok ()
  | leaks ->
      [%l.debug
        "@[<v 2>Memory leak in state:@ %a@]"
          (Fmt.Dump.option @@ Soteria_c_lib.State.pp)
          st];
      let elems =
        List.filter_map
          (Option.map (fun loc ->
               Soteria.Terminal.Call_trace.mk_element ~loc
                 ~msg:"Memory allocated here leaked" ()))
          leaks
      in
      Result.error (`Memory_leak, fn_call_trace elems)

(* Render a single [error] (either a soteria-c memory error or a logical
   consumption failure coming from the symex engine). *)
let pp_error ft : Minterp.error -> unit = function
  | #Error.t as e -> Error.pp ft e
  | #Csymex.cons_fail as e -> Csymex.pp_cons_fail ft e
  | `Missing_resource -> Fmt.pf ft "Missing resource (under-specified)"

let severity_of_error : Minterp.error -> Diagnostic.severity = function
  | #Error.t as e -> Error.severity e
  | #Csymex.cons_fail | `Missing_resource -> Diagnostic.Error

let print_diagnostic ~fid ~call_trace ~error =
  let msg = Fmt.str "%a in %s" pp_error error fid in
  Soteria.Terminal.Diagnostic.print_diagnostic ~call_trace
    ~as_ranges:Error.Diagnostic.as_ranges ~msg
    ~severity:(severity_of_error error)

let print_errors ~entry_point (res : (_, _, _) Compo_res.t) =
  match res with
  | Compo_res.Ok () -> ()
  | Compo_res.Error (Or_gave_up.E (err, trace)) ->
      print_diagnostic ~fid:entry_point ~call_trace:trace ~error:err
  | Compo_res.Error (Or_gave_up.Gave_up msg) ->
      print_diagnostic ~fid:entry_point
        ~call_trace:Soteria.Terminal.Call_trace.empty ~error:(`Gave_up msg)
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
  Csymex.Result.run ~fail_fast:true ~mode:OX ~stats:Caller process

(* Verify every checked function of [prog], skipping the ones the user marked as
   trusted as well as the bare declarations (which have no body to check), and
   printing a diagnostic for each branch outcome. *)
let verify_prog ~fuel (prog : Mu.file) : (unit, string) Result.t =
  let@ () = Soteria.Stats.As_ctx.with_dumped () in
  Sym.Map.iter
    (fun name decl ->
      match decl with
      | Proc { trusted = Checked; args; return_type; body; labels; loc } ->
          Fmt.pr "Verifying function %a...\n" Sym.pp_sym_hum name;
          let name_str = Fmt.str "%a" Sym.pp_sym_hum name in
          let has_bugs = ref false in
          verify_fn ~fuel ~loc name args return_type labels body
          |> List.iter (fun (r, _pc) ->
              print_errors ~entry_point:name_str r;
              if not (Compo_res.is_ok r) then has_bugs := true);
          if not !has_bugs then
            Fmt.pr "%a\n" Soteria.Logs.Printers.pp_ok
              (Fmt.str "Successfully verified %a" Sym.pp_sym_hum name)
      | Proc { trusted = Trusted loc; _ } ->
          L.info (fun m ->
              m "Skipping trusted function %a (%a)" Sym.pp name pp_loc loc)
      | ProcDecl _ -> ())
    prog.funs;
  Ok ()
