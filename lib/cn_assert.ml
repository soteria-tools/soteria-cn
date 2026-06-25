module SState = State
open Soteria.Soteria_std
open Soteria.Logs.Import
open Soteria_c_lib
module State = SState
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

(* This is [Symex.Producer.apply_subst], but re-implemented for the needs of CN. *)
let subst_or_extend ~ty sym subst =
  match Subst.find_opt sym subst with
  | Some v -> return (v, subst)
  | None ->
      let* v = Core_value.nondet_bt ty in
      let subst = Subst.add sym v subst in
      return (v, subst)

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

let produce_p_resource (subst, state) (name : Mu.Request.name) ptr iargs ty =
  match (name, iargs) with
  | Owned (cty, Init), [] ->
      let* ptr = Subst.eval_annot subst ptr in
      let* ptr =
        Core_value.cast_ptr ptr
        |> of_opt_not_impl ~msg:"produce_p_resource: not a pointer"
      in
      let* v = Core_value.nondet_bt ty in
      let+ state = State.produce_owned ptr cty v state in
      (v, (subst, state))
  | Owned _, _ :: _ -> not_impl "produce_p_resource: Owned with iargs"
  | _ -> not_impl "produce_p_resource: not Owned(Init)"

let produce_resource (subst, state) (req : Cn.Request.t) (ty : Cn.BaseTypes.t) :
    (Core_value.t * (Subst.t * State.t option)) Csymex.t =
  match req with
  | P { name; pointer; iargs } ->
      produce_p_resource (subst, state) name pointer iargs ty
  | Q _ -> not_impl "produce_resource: Q"

let produce_logical_arg (subst, state)
    ((arg, _loc) : Mu.logical_arg * Cn.Locations.info) :
    (Subst.t * State.t option) Csymex.t =
  match arg with
  | Define (sym, annot) ->
      let+ v = Subst.eval_annot subst annot in
      let subst = Subst.add sym v subst in
      (subst, state)
  | Resource (sym, (req, ty)) ->
      (* FIXME: Are we allowed to say take `P = ...; take P = ...`
         as a pre-condition to imply that both pointers point to the same data?
         The syntax seems to imply that it's not the case, so I'm assuming
         we can't.  *)
      let+ v, (subst, state) = produce_resource (subst, state) req ty in
      let subst = Subst.add sym v subst in
      (subst, state)
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

let consume_p_resrouce (subst, state) (name : Mu.Request.name) ptr iargs :
    (Core_value.t * (Subst.t * State.t option), _, _) Csymex.Result.t =
  let* loc = Csymex.get_loc () in
  match (name, iargs) with
  | Owned (cty, Init), [] ->
      let* ptr = Subst.eval_annot subst ptr in
      let* ptr =
        Core_value.cast_ptr ptr
        |> of_opt_not_impl ~msg:"consume_p_resource: not a pointer"
      in
      let++ v, state =
        State.consume_owned ptr cty state
        |> Result.map_error (fun (e, _st) ->
            let trace =
              Soteria.Terminal.Call_trace.singleton ~loc
                ~msg:"Could not consume resource" ()
            in
            (e, trace))
      in
      (v, (subst, state))
  | Owned _, _ :: _ -> not_impl "consume_p_resource: Owned with iargs"
  | _ -> not_impl "consume_p_resource: not Owned(Init)"

let consume_resource (subst, state) (req : Cn.Request.t) :
    (Core_value.t * (Subst.t * State.t option), _, _) Csymex.Result.t =
  match req with
  | P { name; pointer; iargs } ->
      consume_p_resrouce (subst, state) name pointer iargs
  | Q _ -> not_impl "consume_resource: Q"

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
  | Resource (sym, (req, _ty)) ->
      let++ v, (subst, state) = consume_resource (subst, state) req in
      let subst = Subst.add sym v subst in
      (subst, state)
  | Constraint lc -> consume_logical_constraint (subst, state) lc

let consume_return_type (ty : Mu.return_type) (ret : Core_value.t) subst state :
    ( Subst.t * State.t option,
      cons_fail_with_trace,
      State.syn list )
    Csymex.Result.t =
  [%l.trace "Consuming return type: %a" Mu.pp_return_type ty];
  let subst = Subst.add (fst ty.ret) ret subst in
  Result.fold_list ~init:(subst, state) ~f:consume_logical_arg ty.logic
