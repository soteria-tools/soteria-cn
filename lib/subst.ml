open Soteria.Soteria_std
open Syntaxes.FunctionWrap
open Soteria.Logs.Import
open Soteria_c_lib
open Csymex
module Mu = Usable_mucore
open Mu
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
            "@[<v 2>assign_pattern: unsupported constructor pattern@ CTOR: %a@ \
             VALUE: %a@ PATTERNS: %a@]"
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

type term = Cn.(BaseTypes.t Terms.term)
type annot = Cn.(BaseTypes.t Terms.annot)

(* It's quite annoying but the printer for const isn't exposed, it's 
    inlined in the printer for annot for some reason. So we have to 
    retrieve the const when printing the error *)
exception Not_impl_const
exception Not_implemented of annot

let eval_tconst : Cn.Terms.const -> Core_value.t = function
  | Bits ((_sign, size), v) ->
      let i = Typed.BitVec.mk_masked size v in
      Obj (Core_value.Int i)
  | Z z ->
      (* FIXME: Not sure why Z is necessary here? We're adding integers with non-integers... *)
      (* I'll model those as i128 for now... *)
      let i = Typed.BitVec.mk_masked 128 z in
      Obj (Core_value.Int i)
  | _ -> raise Not_impl_const

let rec eval_annot (subst : t) (annot : annot) : Core_value.t =
  let of_opt_not_impl = function
    | None -> raise (Not_implemented annot)
    | Some x -> x
  in
  let open Typed.Infix in
  let (IT (it, _bt, _loc)) = annot in
  match it with
  | Sym s -> find s subst
  | Const c -> (
      try eval_tconst c with Not_impl_const -> raise (Not_implemented annot))
  | Tuple ts ->
      let vs = List.map (eval_annot subst) ts in
      Core_value.Tuple vs
  | Binop (op, t1, t2) -> (
      let v1 = eval_annot subst t1 in
      let v2 = eval_annot subst t2 in
      match op with
      | LE -> Core_value.leq ~signed:true v1 v2
      | And -> Core_value.Bool.and_ v1 v2
      | EQ ->
          [%l.trace "Sem_eq? %a == %a" Core_value.pp v1 Core_value.pp v2];
          Bool (Core_value.sem_eq v1 v2)
      | Add ->
          let v1 = Core_value.cast_int v1 |> of_opt_not_impl in
          let v2 = Core_value.cast_int v2 |> of_opt_not_impl in
          Obj (Int (v1 +!@ v2))
      | _ -> raise (Not_implemented annot))
  | StructMember (t, memb) ->
      let v = eval_annot subst t in
      let v = Core_value.struct_field v memb |> of_opt_not_impl in
      Loaded v
  | Good (_, _) ->
      (* Are those pointer invariants? I don't think it should be separate from the chunk? *)
      Core_value.true_
  | _ -> raise (Not_implemented annot)

let eval_annot subst term =
  try
    [%l.trace "Evaluating annot: %a" Mu.pp_it term];
    let res = eval_annot subst term in
    [%l.trace "Evaluated to: %a" Core_value.pp res];
    Csymex.return res
  with Not_implemented annot ->
    Fmt.kstr Csymex.not_impl "eval_annot %a" Mu.pp_it annot
