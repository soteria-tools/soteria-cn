open Soteria_c_lib
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
open Core_value.Syntax
open Csymex
module Mu = Usable_mucore
open Mu

module InterpM = struct
  open State.SM
  include Result

  type 'a t = ('a, Error.with_trace, State.syn list) Result.t

  let lift (type a) (m : a Csymex.t) : a t =
    State.SM.lift @@ Csymex.map Compo_res.ok m

  let lift_symex_res (type a)
      (s : (a, Error.with_trace, State.syn list) Csymex.Result.t) : a t =
    State.SM.lift s

  let[@inline] error (err : Error.t) : 'a t =
    lift_symex_res @@ Csymex.Result.error_with_loc err

  let not_impl fmt = Fmt.kstr (fun str -> State.SM.lift @@ not_impl str) fmt

  let of_opt_not_impl ~msg = function
    | Some x -> ok x
    | None -> not_impl "%s" msg

  let with_loc ~loc (f : unit -> 'a t) =
   fun state -> Csymex.with_loc ~loc (f () state)

  module CV = struct
    let cast_int v =
      Core_value.cast_int v
      |> of_opt_not_impl ~msg:"cast_int: value is not an integer"

    let cast_type v =
      Core_value.cast_type v
      |> of_opt_not_impl ~msg:"cast_type: value is not a type"

    let cast_ptr v =
      Core_value.cast_ptr v
      |> of_opt_not_impl ~msg:"cast_ptr: value is not a pointer"
  end

  module Syntax = struct
    let ( let* ) x f = bind f x
    let ( let+ ) x f = map f x
    let ( let*^ ) (x : 'a Csymex.t) (f : 'a -> 'b t) : 'b t = bind f (lift x)

    module Symex_syntax = Syntax.Symex_syntax
  end

  module State = struct
    open Syntax

    let alloc_ty ty = State.alloc_ty (Cn.Sctypes.to_ctype ty)

    let store ptr ty v =
      let* ptr = CV.cast_ptr ptr in
      let ty = Cn.Sctypes.to_ctype ty in
      let v = Core_value.to_agv v in
      State.store ptr ty v

    let load ptr ty =
      let* ptr = CV.cast_ptr ptr in
      let ty = Cn.Sctypes.to_ctype ty in
      let+ v = State.load ptr ty in
      Core_value.of_agv ~ty v

    let free ptr =
      let* ptr = CV.cast_ptr ptr in
      State.free ptr
  end
end

module ExprM = struct
  type 'a exec_r = Normal of 'a | Returned of Core_value.t
  [@@deriving show { with_path = false }]

  type 'a t = 'a exec_r InterpM.t

  let bind (f : 'a -> 'b t) (m : 'a t) : 'b t =
    InterpM.bind
      (function Normal x -> f x | Returned v -> InterpM.ok (Returned v))
      m

  let map (f : 'a -> 'b) (m : 'a t) : 'b t =
    InterpM.map
      (function Normal x -> Normal (f x) | Returned v -> Returned v)
      m

  let ok (x : 'a) : 'a t = InterpM.ok (Normal x)
  let error e : 'a t = InterpM.error e
  let returned (v : Core_value.t) : 'a t = InterpM.ok (Returned v)

  let fold_list (xs : 'a list) ~(init : 'b) ~(f : 'b -> 'a -> 'b t) : 'b t =
    Monad.foldM ~init ~return:ok ~bind ~fold:Foldable.List.fold xs ~f

  let map_list (xs : 'a list) ~(f : 'a -> 'b t) : 'b list t =
    fold_list ~init:[] xs ~f:(fun acc a -> map (fun b -> b :: acc) (f a))
    |> map List.rev

  module Syntax = struct
    let ( let** ) m f = bind f m
    let ( let++ ) m f = map f m
  end
end

open InterpM
open Syntax

module Subst = struct
  include Symbol_std.Map

  type nonrec t = Core_value.t t

  let pp ft t =
    Fmt.iter_bindings ~sep:Fmt.cut iter
      (fun ft (k, v) -> Fmt.pf ft "%a -> %a" Symbol_std.pp k Core_value.pp v)
      ft t

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
            Fmt.kstr Csymex.not_impl
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

let error_of_ub (_ub : CF.Undefined.undefined_behaviour) : Error.t =
  `UBPointerArithmetic

let stop_if_unsupported (args : arguments) (trusted : trusted) =
  if List.is_empty args.logic && trusted = Checked then ok ()
  else not_impl "exec_fn: function is either trusted or has logic arguments."

let eval_impl_call (i : CF.Implementation.implementation_constant)
    (args : Core_value.t list) : Core_value.t InterpM.t =
  match (i, args) with _ -> not_impl "unsupported impl call"

let conv_int ~(ty : CF.Ctype.ctype) v : Typed.(T.sint t) InterpM.t =
  let open Typed.Syntax in
  let open Typed.Infix in
  let* i = CV.cast_int v in
  let* int_ty =
    match ty with
    | Ctype (_, Basic (Integer int_ty)) -> ok int_ty
    | _ ->
        not_impl "conv_int: type argument is not an integer type: %a"
          Mu.pp_ctype ty
  in
  let+ current_size =
    match Typed.get_ty i with
    | TBitVector s -> ok s
    | _ -> not_impl "conv_int: value is not a bitvector: %a" Core_value.pp v
  in
  match int_ty with
  | Bool -> Typed.ite (i ==@ Typed.BitVec.zero current_size) CInt.(0s) CInt.(1s)
  | ity ->
      let new_size = Core_value.bits_of_ity ity in
      let signed = Layout.is_int_ty_signed ity in
      Typed.BitVec.fit_to ~signed new_size i

let eval_pe_call (sym : Sym.t) (args : Core_value.t list) :
    Core_value.t InterpM.t =
  match (sym, args) with
  | Symbol (_, _, SD_Id "conv_loaded_int"), [ ty; i ] -> (
      let* ty = CV.cast_type ty in
      match i with
      | Loaded (Spec _) ->
          let+ i = conv_int ~ty i in
          Core_value.Loaded (Spec (Int i))
      | Loaded Unspec -> ok (Core_value.Loaded Unspec)
      | _ -> L.failwith "Invalid input to conv_loaded_int")
  | Symbol (_, _, SD_Id "conv_int"), [ ty; i ] -> (
      let* ty = CV.cast_type ty in
      match i with
      | Loaded (Spec _) | Obj (Int _) ->
          let+ i = conv_int ~ty i in
          Core_value.Loaded (Spec (Int i))
      | Loaded Unspec -> ok (Core_value.Loaded Unspec)
      | _ -> L.failwith "Invalid input to conv_int %a" Core_value.pp i)
  | Symbol (_, _, SD_Id "params_length"), [ Tuple l ] ->
      ok @@ Core_value.c_int (List.length l)
  | ( Symbol (_, _, SD_Id "params_nth"),
      [ Tuple l; (Obj (Int i) | Loaded (Spec (Int i))) ] ) ->
      let*^ i =
        Typed.BitVec.to_z i
        |> Csymex.of_opt_not_impl
             ~msg:"params_nth: index is not a concrete integer"
      in
      let i = Z.to_int i in
      ok @@ List.nth l i
  | _ -> not_impl "unsupported pe call: %a" Sym.pp sym

let eval_ctor (ctor : CF.Core.ctor) (v : Core_value.t list) :
    Core_value.t InterpM.t =
  match (ctor, v) with
  | Cspecified, [ Obj v ] -> ok (Core_value.Loaded (Spec v))
  | Cunspecified, _ -> ok (Core_value.Loaded Unspec)
  | Ctuple, vs -> ok (Core_value.Tuple vs)
  | _ -> not_impl "Unsupported constructor: %a" Mu.pp_ctor ctor

let eval_iop ~(int_ty : CF.Ctype.integerType) (iop : CF.Core.iop)
    (lhs : Typed.(T.sint t)) (rhs : Typed.(T.sint t)) :
    Typed.(T.sint t) InterpM.t =
  let open Typed.Infix in
  let signed = Layout.is_int_ty_signed int_ty in
  let arith_op ~check_signed_ovf ~checked_op ~unchecked_op =
    if signed then
      if%sat check_signed_ovf lhs rhs then error `Overflow
      else ok (checked_op lhs rhs)
    else ok (unchecked_op lhs rhs)
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
  | _ -> not_impl "unsupported iop"

let cfunction (v : Core_value.t) =
  let* sym =
    match v with
    | Obj (Fn sym) | Loaded (Spec (Fn sym)) -> ok sym
    | _ -> not_impl "cfunction: value is not a function: %a" Core_value.pp v
  in
  let prog = Ctx.get_prog () in
  let* fn =
    Sym.Map.find_opt sym prog.call_funinfo
    |> InterpM.of_opt_not_impl ~msg:"cfunction: function not found in program"
  in
  ok (Core_value.cfunction fn)

let eval_op (op : CF.Core.binop) (lhs : Core_value.t) (rhs : Core_value.t) =
  let open Core_value in
  match op with
  | OpEq -> ok (Bool (sem_eq lhs rhs))
  | OpOr -> ok @@ Core_value.Bool.or_ lhs rhs
  | _ -> not_impl "eval_op: unsupported operator: %a" Mu.pp_binop op

let rec eval_pexpr (subst : Subst.t) (pexpr : pexpr) =
  [%l.trace "Evaluating pexpr: %a" Mu.pp_pexpr pexpr];
  let@ () = with_loc ~loc:pexpr.loc in
  match pexpr.node with
  | PEsym sym -> ok (Subst.find sym subst)
  | PEval v -> ok (Core_value.of_mu v)
  | PEcfunction pe ->
      let* f = eval_pexpr subst pe in
      cfunction f
  | PEundef (_, ub) -> error (error_of_ub ub)
  | PEcall (generic_name, args) -> (
      let* args = map_list ~f:(eval_pexpr subst) args in
      match generic_name with
      | Sym s -> eval_pe_call s args
      | Impl i -> eval_impl_call i args)
  | PEctor (ctor, pes) ->
      let* vs = map_list ~f:(eval_pexpr subst) pes in
      eval_ctor ctor vs
  | PElet { pat; value; body } ->
      let* v = eval_pexpr subst value in
      let*^ subst = Subst.assign_pattern subst pat v in
      eval_pexpr subst body
  | PEcatch_exceptional_condition { int_ty; iop; lhs; rhs } ->
      let* lhs = eval_pexpr subst lhs in
      let* rhs = eval_pexpr subst rhs in
      let* lhs = CV.cast_int lhs in
      let* rhs = CV.cast_int rhs in
      let+ res = eval_iop ~int_ty iop lhs rhs in
      Core_value.Obj (Core_value.Int res)
  | PEnot e ->
      let+ b = eval_pexpr subst e in
      Core_value.Bool.not b
  | PEop { op; lhs; rhs } ->
      let* lhs = eval_pexpr subst lhs in
      let* rhs = eval_pexpr subst rhs in
      eval_op op lhs rhs
  | PEare_compatible { left; right } ->
      (* Deeply uninteresting but I guess we have to implement that... *)
      let* left = eval_pexpr subst left in
      let* left = CV.cast_type left in
      let* right = eval_pexpr subst right in
      let* right = CV.cast_type right in
      let res =
        CF.AilTypesAux.are_compatible
          (CF.Ctype.no_qualifiers, left)
          (CF.Ctype.no_qualifiers, right)
      in
      ok (Core_value.Bool.of_bool res)
  | PEif { cond; then_; else_ } ->
      let* guard = eval_pexpr subst cond in
      let guard = Core_value.Bool.to_sbool guard in
      if%sat guard then eval_pexpr subst then_ else eval_pexpr subst else_
  | PEconv_int { ty; arg } -> (
      let* ty = eval_pexpr subst ty in
      let* i = eval_pexpr subst arg in
      let* ty = CV.cast_type ty in
      match i with
      | Loaded (Spec _) | Obj (Int _) ->
          let+ i = conv_int ~ty i in
          Core_value.Loaded (Spec (Int i))
      | Loaded Unspec -> ok (Core_value.Loaded Unspec)
      | _ -> L.failwith "Invalid input to conv_int %a" Core_value.pp i)
  | PEconstrained _ -> not_impl "PEconstrainted"
  | PEerror _ -> not_impl "PEerror"
  | PEmember_shift _ -> not_impl "PEmember_shift"
  | PEarray_shift _ -> not_impl "PEarray_shift"
  | PEwrapI _ -> not_impl "PEwrapI"
  | PEmemop _ -> not_impl "PEmemop"
  | PEstruct _ -> not_impl "PEstruct"
  | PEunion _ -> not_impl "PEunion"
  | PEmemberof _ -> not_impl "PEmemberof"

let eval_action (subst : Subst.t) (action : action) : Core_value.t InterpM.t =
  let@ () = with_loc ~loc:action.loc in
  match action.action with
  | Create { align; ty; prefix = _ } ->
      let+ ptr = State.alloc_ty ty.node in
      Core_value.Obj (Ptr ptr)
  | Store { ptr; value; ty; _ } ->
      let* ptr = eval_pexpr subst ptr in
      let* value = eval_pexpr subst value in
      let+ () = State.store ptr ty.node value in
      Core_value.Unit
  | Load { ptr; ty; _ } ->
      let* ptr = eval_pexpr subst ptr in
      State.load ptr ty.node
  | Kill (_kind, ptr) ->
      let* ptr = eval_pexpr subst ptr in
      let+ () = State.free ptr in
      Core_value.Unit
  | _ -> not_impl "Unsupported action: %a" Mu.pp_action action

let rec eval_expr ~(labels : label_def Sym.Map.t) (subst : Subst.t)
    (body : expr) : Core_value.t ExprM.t =
  let open ExprM.Syntax in
  [%l.trace "Evaluating expr: %a" Mu.pp_expr body];
  let@ () = with_loc ~loc:body.loc in
  [%l.debug "@[Substitution:@ %a@]" Subst.pp subst];
  (* let* () =
    if List.is_empty body.annots then return ()
    else Fmt.kstr not_impl "annotations: %a" 
  in *)
  match body.node with
  | Elet { pat; value; body = body' } ->
      let* v = eval_pexpr subst value in
      let*^ subst = Subst.assign_pattern subst pat v in
      eval_expr ~labels subst body'
  | Esseq { pat; value; body } | Ewseq { pat; value; body } ->
      let** v = eval_expr ~labels subst value in
      let*^ subst = Subst.assign_pattern subst pat v in
      eval_expr ~labels subst body
  | Eunseq es ->
      let++ res = ExprM.map_list es ~f:(eval_expr ~labels subst) in
      Core_value.Tuple res
  | Ebound e -> eval_expr ~labels subst e
  | Epure e ->
      let+ r = eval_pexpr subst e in
      ExprM.Normal r
  | Erun (lab, pes) -> (
      [%l.trace "Running label: %a" Sym.pp lab];
      let* vs = map_list ~f:(eval_pexpr subst) pes in
      match (Sym.Map.find lab labels, vs) with
      | Return _, [ v ] -> ExprM.returned v
      | Return _, _ ->
          not_impl "Return label with multiple values: %a" Sym.pp lab
      | Non_inlined _, _ -> not_impl "Non-inlined label: %a" Sym.pp lab
      | Loop _, _ -> not_impl "Loop label: %a" Sym.pp lab)
  | Eif { cond; then_; else_ } ->
      let* guard = eval_pexpr subst cond in
      let guard = Core_value.Bool.to_sbool guard in
      if%sat guard then eval_expr ~labels subst then_
      else eval_expr ~labels subst else_
  | Eccall { ty; fn; args; specs = _ } -> (
      let* fn = eval_pexpr subst fn in
      let* args = map_list ~f:(eval_pexpr subst) args in
      match fn with
      | Obj (Fn sym) | Loaded (Spec (Fn sym)) ->
          let prog = Ctx.get_prog () in
          let fn = Sym.Map.find sym prog.funs in
          let+ v = exec_fun fn args in
          ExprM.Normal v
      | _ -> not_impl "Dynamic call %a" Core_value.pp fn)
  | Eaction action ->
      let+ v = eval_action subst action in
      ExprM.Normal v
  | _ -> not_impl "Unsupported expr: %a" Mu.pp_expr body

and exec_fun (fn : Mu.fun_map_decl) params =
  [%l.debug "@[Executing function:@ %a@]" Mu.pp_fun_map_decl fn];
  match fn with
  | ProcDecl _ -> not_impl "exec_fn: ProcDecl"
  | Proc { loc; args; body; labels; return_type; trusted } -> (
      let@ () = with_loc ~loc in
      let* () = stop_if_unsupported args trusted in
      let subst = Subst.from_args args params in
      let+ v = eval_expr ~labels subst body in
      [%l.debug "Function returned: %a" (ExprM.pp_exec_r Core_value.pp) v];
      match v with Normal v -> Core_value.Unit | Returned v -> v)
