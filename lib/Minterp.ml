open Soteria_c_lib
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
open Core_value.Syntax
open Csymex
open Csymex.Syntax
module Mu = Usable_mucore
open Mu

module Subst = struct
  include Symbol_std.Map

  type nonrec t = Core_value.t t

  let assign_pattern subt (pat : pattern) (v : Core_value.t) : t Csymex.t =
    let@@ () = Csymex.with_loc ~loc:pat.loc in
    match pat.node with
    | CaseBase (Some sym, _) -> return (add sym v subt)
    | CaseBase (None, _) -> return subt
    | _ -> not_impl "assign_pattern: unsupported pattern"
end

let sym_is_id sym id =
  let open Cerb_frontend.Symbol in
  match sym with Symbol (_digest, _i, SD_Id id') -> id = id' | _ -> false

let stop_if_unsupported (args : arguments) (trusted : trusted) =
  if List.is_empty args.comp && List.is_empty args.logic && trusted = Checked
  then return ()
  else not_impl "exec_fn: function is either trusted or has arguments."

let eval_impl_call (i : CF.Implementation.implementation_constant)
    (args : Core_value.t list) : (Core_value.t, _, _) Csymex.Result.t =
  match (i, args) with _ -> Fmt.kstr not_impl "unsupported impl call"

let eval_pe_call (sym : Sym.t) (args : Core_value.t list) :
    (Core_value.t, _, _) Result.t =
  match (sym, args) with
  | Symbol (_, _, SD_Id "conv_loaded_int"), [ _; i ] -> Result.ok i
  | _ -> Fmt.kstr not_impl "unsupported pe call: %a" Sym.pp sym

let eval_ctor (ctor : CF.Core.ctor) (v : Core_value.t list) :
    (Core_value.t, _, _) Result.t =
  match (ctor, v) with
  | Cspecified, [ Obj v ] -> Result.ok (Core_value.Loaded (Spec v))
  | _ -> Fmt.kstr not_impl "unsupported ctor"

let rec eval_pexpr (subst : Subst.t) (pexpr : pexpr) =
  let@@ () = Csymex.with_loc ~loc:pexpr.loc in
  match pexpr.node with
  | PEsym sym -> Result.ok (Subst.find sym subst)
  | PEval v -> Result.ok (Core_value.of_mu v)
  | PEundef (_, ub) -> Result.error "UB"
  | PEcall (generic_name, args) -> (
      let** args = Result.map_list ~f:(eval_pexpr subst) args in
      match generic_name with
      | Sym s -> eval_pe_call s args
      | Impl i -> eval_impl_call i args)
  | PEctor (ctor, pes) ->
      let** vs = Result.map_list ~f:(eval_pexpr subst) pes in
      eval_ctor ctor vs
  | PEconstrained _ -> not_impl "PEconstrainted"
  | PEerror _ -> not_impl "PEerror"
  | PEmember_shift _ -> not_impl "PEmember_shift"
  | PEarray_shift _ -> not_impl "PEarray_shift"
  | PEcatch_exceptional_condition _ -> not_impl "PEcatch_exceptional_condition"
  | PEwrapI _ -> not_impl "PEwrapI"
  | PEmemop _ -> not_impl "PEmemop"
  | PEnot _ -> not_impl "PEnot"
  | PEop _ -> not_impl "PEop"
  | PEconv_int _ -> not_impl "PEconv_int"
  | PEstruct _ -> not_impl "PEstruct"
  | PEunion _ -> not_impl "PEunion"
  | PEcfunction _ -> not_impl "PEcfunction"
  | PEmemberof _ -> not_impl "PEmemberof"
  | PElet _ -> not_impl "PElet"
  | PEif _ -> not_impl "PEif"
  | PEare_compatible _ -> not_impl "PEare_compatible"

let rec eval_expr ~(labels : label_def Sym.Map.t) (subst : Subst.t)
    (body : expr) : (Core_value.t, _, _) Csymex.Result.t =
  let@@ () = Csymex.with_loc ~loc:body.loc in
  (* let* () =
    if List.is_empty body.annots then return ()
    else Fmt.kstr not_impl "annotations: %a" 
  in *)
  match body.node with
  | Elet { pat; value; body = body' } ->
      let** v = eval_pexpr subst value in
      let* subst = Subst.assign_pattern subst pat v in
      eval_expr ~labels subst body'
  | Esseq { pat; value; body } ->
      let** v = eval_expr ~labels subst value in
      let* subst = Subst.assign_pattern subst pat v in
      eval_expr ~labels subst body
  | Ebound e -> eval_expr ~labels subst e
  | Epure e -> eval_pexpr subst e
  | Erun (lab, pes) -> (
      let** vs = Result.map_list ~f:(eval_pexpr subst) pes in
      match (Sym.Map.find lab labels, vs) with
      | Return _, [ v ] -> Result.ok v
      | Return _, _ ->
          Fmt.kstr not_impl "Return label with multiple values: %a" Sym.pp lab
      | Non_inlined _, _ -> Fmt.kstr not_impl "Non-inlined label: %a" Sym.pp lab
      | Loop _, _ -> Fmt.kstr not_impl "Loop label: %a" Sym.pp lab)
  | _ -> Fmt.kstr not_impl "Unsupported expr: %a" Mu.pp_expr body

let exec_fun (fn : Mu.fun_map_decl) params =
  [%l.trace "Executing function: %a" Mu.pp_fun_map_decl fn];
  match fn with
  | ProcDecl _ -> Csymex.not_impl "exec_fn: ProcDecl"
  | Proc { loc; args; body; labels; return_type; trusted } ->
      let@@ () = Csymex.with_loc ~loc in
      let* () = stop_if_unsupported args trusted in
      let++ v = eval_expr ~labels Subst.empty body in
      [%l.debug "Function returned: %a" Core_value.pp v];
      Compo_res.Ok ()
