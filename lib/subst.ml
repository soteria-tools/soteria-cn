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
