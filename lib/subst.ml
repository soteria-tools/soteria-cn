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

exception Not_implemented of annot

let rec eval_annot (subst : t) (annot : annot) : Core_value.t =
  let (IT (it, _bt, _loc)) = annot in
  match it with
  | Sym s -> find s subst
  | Tuple ts ->
      let vs = List.map (eval_annot subst) ts in
      Core_value.Tuple vs
  | Binop (LE, t1, t2) ->
      let v1 = eval_annot subst t1 in
      let v2 = eval_annot subst t2 in
      Core_value.leq ~signed:true v1 v2
  | Binop (And, t1, t2) ->
      let v1 = eval_annot subst t1 in
      let v2 = eval_annot subst t2 in
      Core_value.Bool.and_ v1 v2
  | _ -> raise (Not_implemented annot)

let eval_annot subst term =
  try Csymex.return (eval_annot subst term)
  with Not_implemented annot ->
    Fmt.kstr Csymex.not_impl "eval_annot %a" Mu.pp_it annot
