open Soteria.Soteria_std
open Soteria.Logs.Import
open Soteria_c_lib
module Mu = Usable_mucore
open Csymex
open Syntax

type term = Cn.(BaseTypes.t Terms.term)
type annot = Cn.(BaseTypes.t Terms.annot)

type cons_fail_with_trace =
  Csymex.cons_fail * Cerb_location.t Soteria.Terminal.Call_trace.t

(* Sound only in OX mode, of course *)
let logic_assert v =
  let*- err = Csymex.assert_or_error v (`Lfail v :> Csymex.cons_fail) in
  let* loc = get_loc () in
  let err =
    ( err,
      Soteria.Terminal.Call_trace.singleton ~loc
        ~msg:"Could not prove this hold" () )
  in
  Result.error err

let produce_computational_arg (subst, state)
    ((arg, _loc) : Mu.computational_arg * Cn.Locations.info) :
    (Subst.t * State.t option) Csymex.t =
  let (Computational (sym, ty) | Ghost (sym, ty)) = arg in
  let+ v = Core_value.nondet_bt ty in
  let subst = Subst.add sym v subst in
  (subst, state)

let produce_pure (subst, state) (annot : annot) :
    (Subst.t * State.t option) Csymex.t =
  let* v = Subst.eval_annot subst annot in
  let* v =
    Core_value.cast_bool v |> of_opt_not_impl ~msg:"produce_pure: not a boolean"
  in
  let+ () = assume [ v ] in
  (subst, state)

let produce_logical_constraint (subst, state) (lc : Cn.LogicalConstraints.t) :
    (Subst.t * State.t option) Csymex.t =
  match lc with
  | T it -> produce_pure (subst, state) it
  | Forall _ -> not_impl "consume_logical_constraint: Forall"

let produce_logical_arg (subst, state)
    ((arg, _loc) : Mu.logical_arg * Cn.Locations.info) :
    (Subst.t * State.t option) Csymex.t =
  match arg with
  | Define (sym, annot) ->
      let+ v = Subst.eval_annot subst annot in
      let subst = Subst.add sym v subst in
      (subst, state)
  | Resource _ -> not_impl "consume_logical_arg: Resource"
  | Constraint lc -> produce_logical_constraint (subst, state) lc

let produce_arguments (args : Mu.arguments) :
    (Subst.t * State.t option) Csymex.t =
  let subst = Subst.empty in
  let state = State.empty in
  let* subst, state =
    fold_list ~init:(subst, state) ~f:produce_computational_arg args.comp
  in
  fold_list ~init:(subst, state) ~f:produce_logical_arg args.logic

let consume_pure (subst, state) (annot : annot) =
  let (IT (_, _, loc)) = annot in
  let@@ () = Csymex.with_loc ~loc in
  let* v = Subst.eval_annot subst annot in
  let* v =
    Core_value.cast_bool v
    |> of_opt_not_impl ~msg:"consume_annot: not a boolean"
  in
  let++ () = logic_assert v in
  (subst, state)

let consume_logical_constraint (subst, state) (lc : Cn.LogicalConstraints.t) :
    ( Subst.t * State.t option,
      cons_fail_with_trace,
      State.syn list )
    Csymex.Result.t =
  match lc with
  | T it -> consume_pure (subst, state) it
  | Forall _ -> not_impl "consume_logical_constraint: Forall"

let consume_logical_arg (subst, state)
    ((arg, (loc, _)) : Mu.logical_arg * Cn.Locations.info) :
    ( Subst.t * State.t option,
      cons_fail_with_trace,
      State.syn list )
    Csymex.Result.t =
  let@@ () = Csymex.with_loc ~loc in
  match arg with
  | Define (sym, annot) ->
      let+ v = Subst.eval_annot subst annot in
      let subst = Subst.add sym v subst in
      Compo_res.Ok (subst, state)
  | Resource _ -> not_impl "consume_logical_arg: Resource"
  | Constraint lc -> consume_logical_constraint (subst, state) lc

let consume_return_type (ty : Mu.return_type) (ret : Core_value.t) subst state :
    ( Subst.t * State.t option,
      cons_fail_with_trace,
      State.syn list )
    Csymex.Result.t =
  [%l.trace "Consuming return type: %a" Mu.pp_return_type ty];
  let subst = Subst.add (fst ty.ret) ret subst in
  Result.fold_list ~init:(subst, state) ~f:consume_logical_arg ty.logic
