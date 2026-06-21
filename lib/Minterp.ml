open Soteria_c_lib
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
open Core_value.Syntax
open Csymex
open Csymex.Syntax
module Mu = Usable_mucore
open Mu

module ExprM = struct
  type 'a exec_r = Normal of 'a | Returned of Core_value.t
  [@@deriving show { with_path = false }]

  type 'a t = ('a exec_r, string, unit) Result.t

  let bind (f : 'a -> 'b t) (m : 'a t) : 'b t =
    Result.bind
      (function Normal x -> f x | Returned v -> Result.ok (Returned v))
      m

  let map (f : 'a -> 'b) (m : 'a t) : 'b t =
    Result.map
      (function Normal x -> Normal (f x) | Returned v -> Returned v)
      m

  let ok (x : 'a) : 'a t = Result.ok (Normal x)
  let error (msg : string) : 'a t = Result.error msg
  let returned (v : Core_value.t) : 'a t = Result.ok (Returned v)

  let fold_list (xs : 'a list) ~(init : 'b) ~(f : 'b -> 'a -> 'b t) : 'b t =
    Monad.foldM ~init ~return:ok ~bind ~fold:Foldable.List.fold xs ~f

  let map_list (xs : 'a list) ~(f : 'a -> 'b t) : 'b list t =
    fold_list ~init:[] xs ~f:(fun acc a -> map (fun b -> b :: acc) (f a))
    |> map List.rev

  module Syntax = struct
    let ( let*** ) m f = bind f m
    let ( let+++ ) m f = map f m
  end
end

open ExprM
open Syntax

module Subst = struct
  include Symbol_std.Map

  type nonrec t = Core_value.t t

  let rec assign_pattern subst (pat : pattern) (v : Core_value.t) : t Csymex.t =
    let@@ () = Csymex.with_loc ~loc:pat.loc in
    match pat.node with
    | CaseBase (Some sym, _) -> return (add sym v subst)
    | CaseBase (None, _) -> return subst
    | CaseCtor (ctor, pats) -> (
        match (ctor, v, pats) with
        | Cspecified, Loaded (Spec v'), [ p ] -> assign_pattern subst p (Obj v')
        | Ctuple, Tuple vs, pats' when List.compare_lengths vs pats' = 0 ->
            Csymex.fold_list (List.combine pats' vs) ~init:subst
              ~f:(fun acc (p, v) -> assign_pattern acc p v)
        | _ ->
            Fmt.kstr not_impl
              "@[<v 2>assign_pattern: unsupported constructor pattern@ CTOR: \
               %a@ VALUE: %a@ PATTERNS: %a@]"
              Mu.pp_ctor ctor Core_value.pp v
              (Fmt.Dump.list Mu.pp_pattern)
              pats)

  let from_args (args : Mu.arguments) (params : Core_value.t list) : t =
    List.fold_left2
      (fun acc ((arg, _) : Mu.computational_arg * _) param ->
        match arg with
        | Computational (sym, _) -> add sym param acc
        | Ghost _ -> L.failwith "Unsupported ghost arguments")
      empty args.comp params
end

let sym_is_id sym id =
  let open Cerb_frontend.Symbol in
  match sym with Symbol (_digest, _i, SD_Id id') -> id = id' | _ -> false

let stop_if_unsupported (args : arguments) (trusted : trusted) =
  if List.is_empty args.logic && trusted = Checked then return ()
  else not_impl "exec_fn: function is either trusted or has logic arguments."

let eval_impl_call (i : CF.Implementation.implementation_constant)
    (args : Core_value.t list) : (Core_value.t, _, _) Csymex.Result.t =
  match (i, args) with _ -> Fmt.kstr not_impl "unsupported impl call"

let eval_pe_call (sym : Sym.t) (args : Core_value.t list) :
    (Core_value.t, _, _) Result.t =
  match (sym, args) with
  | Symbol (_, _, SD_Id ("conv_loaded_int" | "conv_int")), [ _; i ] ->
      Result.ok i
  | Symbol (_, _, SD_Id "params_length"), [ Tuple l ] ->
      Result.ok @@ Core_value.c_int (List.length l)
  | ( Symbol (_, _, SD_Id "params_nth"),
      [ Tuple l; (Obj (Int i) | Loaded (Spec (Int i))) ] ) ->
      let* i =
        Typed.BitVec.to_z i
        |> Csymex.of_opt_not_impl
             ~msg:"params_nth: index is not a concrete integer"
      in
      let i = Z.to_int i in
      Result.ok @@ List.nth l i
  | _ -> Fmt.kstr not_impl "unsupported pe call: %a" Sym.pp sym

let eval_ctor (ctor : CF.Core.ctor) (v : Core_value.t list) :
    (Core_value.t, _, _) Result.t =
  match (ctor, v) with
  | Cspecified, [ Obj v ] -> Result.ok (Core_value.Loaded (Spec v))
  | Cunspecified, _ -> Result.ok (Core_value.Loaded Unspec)
  | Ctuple, vs -> Result.ok (Core_value.Tuple vs)
  | _ -> Fmt.kstr not_impl "Unsupported constructor: %a" Mu.pp_ctor ctor

let eval_iop ~(int_ty : CF.Ctype.integerType) (iop : CF.Core.iop)
    (lhs : Typed.(T.sint t)) (rhs : Typed.(T.sint t)) :
    (Typed.(T.sint t), _, _) Result.t =
  let open Typed.Infix in
  let signed = Layout.is_int_ty_signed int_ty in
  let arith_op ~check_signed_ovf ~checked_op ~unchecked_op =
    if signed then
      if%sat check_signed_ovf lhs rhs then Result.error "Integer overflow"
      else Result.ok (checked_op lhs rhs)
    else Result.ok (unchecked_op lhs rhs)
  in
  match iop with
  | IOpAdd ->
      arith_op
        ~check_signed_ovf:(Typed.BitVec.add_overflows ~signed:true)
        ~checked_op:( +!!@ ) ~unchecked_op:( +!@ )
  | IOpSub ->
      arith_op
        ~check_signed_ovf:(Typed.BitVec.sub_overflows ~signed:true)
        ~checked_op:( -!!@ ) ~unchecked_op:( -!@ )
  | _ -> Fmt.kstr not_impl "unsupported iop"

let cfunction (v : Core_value.t) =
  let* sym =
    match v with
    | Obj (Fn sym) | Loaded (Spec (Fn sym)) -> Csymex.return sym
    | _ ->
        Fmt.kstr not_impl "cfunction: value is not a function: %a" Core_value.pp
          v
  in
  let prog = Ctx.get_prog () in
  let* fn =
    Sym.Map.find_opt sym prog.call_funinfo
    |> Csymex.of_opt_not_impl ~msg:"cfunction: function not found in program"
  in
  Result.ok (Core_value.cfunction fn)

let eval_op (op : CF.Core.binop) (lhs : Core_value.t) (rhs : Core_value.t) =
  let open Core_value in
  match op with
  | OpEq -> Result.ok (Bool (sem_eq lhs rhs))
  | OpOr -> Result.ok @@ Core_value.Bool.or_ lhs rhs
  | _ -> Fmt.kstr not_impl "eval_op: unsupported operator: %a" Mu.pp_binop op

let rec eval_pexpr (subst : Subst.t) (pexpr : pexpr) =
  [%l.trace "Evaluating pexpr: %a" Mu.pp_pexpr pexpr];
  let@@ () = Csymex.with_loc ~loc:pexpr.loc in
  match pexpr.node with
  | PEsym sym -> Result.ok (Subst.find sym subst)
  | PEval v -> Result.ok (Core_value.of_mu v)
  | PEcfunction pe ->
      let** f = eval_pexpr subst pe in
      cfunction f
  | PEundef (_, ub) -> Result.error "UB"
  | PEcall (generic_name, args) -> (
      let** args = Result.map_list ~f:(eval_pexpr subst) args in
      match generic_name with
      | Sym s -> eval_pe_call s args
      | Impl i -> eval_impl_call i args)
  | PEctor (ctor, pes) ->
      let** vs = Result.map_list ~f:(eval_pexpr subst) pes in
      eval_ctor ctor vs
  | PElet { pat; value; body } ->
      let** v = eval_pexpr subst value in
      let* subst = Subst.assign_pattern subst pat v in
      eval_pexpr subst body
  | PEcatch_exceptional_condition { int_ty; iop; lhs; rhs } ->
      let** lhs = eval_pexpr subst lhs in
      let** rhs = eval_pexpr subst rhs in
      let** lhs = Core_value.cast_int lhs in
      let** rhs = Core_value.cast_int rhs in
      let++ res = eval_iop ~int_ty iop lhs rhs in
      Core_value.Obj (Core_value.Int res)
  | PEnot e ->
      let++ b = eval_pexpr subst e in
      Core_value.Bool.not b
  | PEop { op; lhs; rhs } ->
      let** lhs = eval_pexpr subst lhs in
      let** rhs = eval_pexpr subst rhs in
      eval_op op lhs rhs
  | PEare_compatible { left; right } ->
      (* Deeply uninteresting but I guess we have to implement that... *)
      let** left = eval_pexpr subst left in
      let** left = Core_value.cast_type left in
      let** right = eval_pexpr subst right in
      let** right = Core_value.cast_type right in
      let res =
        CF.AilTypesAux.are_compatible
          (CF.Ctype.no_qualifiers, left)
          (CF.Ctype.no_qualifiers, right)
      in
      Result.ok (Core_value.Bool.of_bool res)
  | PEif { cond; then_; else_ } ->
      let** guard = eval_pexpr subst cond in
      let guard = Core_value.Bool.to_sbool guard in
      if%sat guard then eval_pexpr subst then_ else eval_pexpr subst else_
  | PEconstrained _ -> not_impl "PEconstrainted"
  | PEerror _ -> not_impl "PEerror"
  | PEmember_shift _ -> not_impl "PEmember_shift"
  | PEarray_shift _ -> not_impl "PEarray_shift"
  | PEwrapI _ -> not_impl "PEwrapI"
  | PEmemop _ -> not_impl "PEmemop"
  | PEconv_int _ -> not_impl "PEconv_int"
  | PEstruct _ -> not_impl "PEstruct"
  | PEunion _ -> not_impl "PEunion"
  | PEmemberof _ -> not_impl "PEmemberof"

let eval_action (subst : Subst.t) (action : action) :
    (Core_value.t, _, _) Result.t =
  let@@ () = Csymex.with_loc ~loc:action.loc in
  match action.action with
  | Create { align; ty; prefix = _ } -> Fmt.kstr not_impl "create prefix"
  | _ -> Fmt.kstr not_impl "Unsupported action: %a" Mu.pp_action action

let rec eval_expr ~(labels : label_def Sym.Map.t) (subst : Subst.t)
    (body : expr) : Core_value.t ExprM.t =
  let open ExprM.Syntax in
  [%l.trace "Evaluating expr: %a" Mu.pp_expr body];
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
  | Esseq { pat; value; body } | Ewseq { pat; value; body } ->
      let*** v = eval_expr ~labels subst value in
      let* subst = Subst.assign_pattern subst pat v in
      eval_expr ~labels subst body
  | Eunseq es ->
      let+++ res = ExprM.map_list es ~f:(eval_expr ~labels subst) in
      Core_value.Tuple res
  | Ebound e -> eval_expr ~labels subst e
  | Epure e ->
      let** r = eval_pexpr subst e in
      ExprM.ok r
  | Erun (lab, pes) -> (
      [%l.trace "Running label: %a" Sym.pp lab];
      let** vs = Result.map_list ~f:(eval_pexpr subst) pes in
      match (Sym.Map.find lab labels, vs) with
      | Return _, [ v ] -> ExprM.returned v
      | Return _, _ ->
          Fmt.kstr not_impl "Return label with multiple values: %a" Sym.pp lab
      | Non_inlined _, _ -> Fmt.kstr not_impl "Non-inlined label: %a" Sym.pp lab
      | Loop _, _ -> Fmt.kstr not_impl "Loop label: %a" Sym.pp lab)
  | Eif { cond; then_; else_ } ->
      let** guard = eval_pexpr subst cond in
      let guard = Core_value.Bool.to_sbool guard in
      if%sat guard then eval_expr ~labels subst then_
      else eval_expr ~labels subst else_
  | Eccall { ty; fn; args; specs = _ } -> (
      let** fn = eval_pexpr subst fn in
      let** args = Result.map_list ~f:(eval_pexpr subst) args in
      match fn with
      | Obj (Fn sym) | Loaded (Spec (Fn sym)) ->
          let prog = Ctx.get_prog () in
          let fn = Sym.Map.find sym prog.funs in
          let++ v = exec_fun fn args in
          Normal v
      | _ -> Fmt.kstr not_impl "Dynamic call %a" Core_value.pp fn)
  | Eaction action ->
      let++ v = eval_action subst action in
      Normal v
  | _ -> Fmt.kstr not_impl "Unsupported expr: %a" Mu.pp_expr body

and exec_fun (fn : Mu.fun_map_decl) params =
  [%l.debug "@[Executing function:@ %a@]" Mu.pp_fun_map_decl fn];
  match fn with
  | ProcDecl _ -> Csymex.not_impl "exec_fn: ProcDecl"
  | Proc { loc; args; body; labels; return_type; trusted } -> (
      let@@ () = Csymex.with_loc ~loc in
      let* () = stop_if_unsupported args trusted in
      let subst = Subst.from_args args params in
      let++ v = eval_expr ~labels subst body in
      [%l.debug "Function returned: %a" (ExprM.pp_exec_r Core_value.pp) v];
      match v with Normal v -> Core_value.Unit | Returned v -> v)
