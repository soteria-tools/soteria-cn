module SState = State
open Soteria.Soteria_std
open Soteria.Logs.Import
open Soteria_c_lib
module State = SState
module Mu = Usable_mucore
open Csymex
open Syntax
open Soteria_c_helpers
module InterpM = Interp_monad

(* A [Mu.cn_prog] is a flattened CN proof step: a preamble of hoisted memory
   loads ([let x = *(p : ty)]) followed by a single proof command. The loads are
   evaluated first — extending the substitution — and the command is then
   dispatched. Every expression here is a [Term]/[annot], so it is handled
   exactly like the terms in [Cn_assert]/[Subst]; there is no [cn_expr] to
   handle separately (it was compiled away when the [Usable_mucore] AST was
   built). *)

let execute_load (subst : Subst.t) (load : Mu.cn_load) : Subst.t InterpM.t =
  let open InterpM.Syntax in
  let@ () = InterpM.with_loc ~loc:load.loc in
  let*^ ptr = Subst.eval_annot subst load.pointer in
  let* v = InterpM.State.load ptr load.ct in
  InterpM.ok (Subst.add load.sym v subst)

let execute_statement (_subst : Subst.t) (stmt : Mu.cn_statement) :
    unit InterpM.t =
  match stmt with
  | Mu.Pack_unpack _ -> InterpM.not_impl "cn statement: pack/unpack"
  | Mu.To_from_bytes _ -> InterpM.not_impl "cn statement: to/from bytes"
  | Mu.Have _ -> InterpM.not_impl "cn statement: have"
  | Mu.Instantiate _ -> InterpM.not_impl "cn statement: instantiate"
  | Mu.Split_case _ -> InterpM.not_impl "cn statement: split_case"
  | Mu.Extract _ -> InterpM.not_impl "cn statement: extract"
  | Mu.Unfold _ -> InterpM.not_impl "cn statement: unfold"
  | Mu.Apply _ -> InterpM.not_impl "cn statement: apply"
  | Mu.Assert _ -> InterpM.not_impl "cn statement: assert"
  | Mu.Inline _ -> InterpM.not_impl "cn statement: inline"
  | Mu.Print _ -> InterpM.not_impl "cn statement: print"

let execute_one (subst : Subst.t) (prog : Mu.cn_prog) : unit InterpM.t =
  let open InterpM.Syntax in
  let@ () = InterpM.with_loc ~loc:prog.loc in
  let* subst = InterpM.fold_list ~init:subst ~f:execute_load prog.loads in
  execute_statement subst prog.stmt

let execute_cn_prog (progs : Mu.cn_prog list) (subst : Subst.t) : unit InterpM.t
    =
  InterpM.fold_list ~init:() ~f:(fun () prog -> execute_one subst prog) progs
