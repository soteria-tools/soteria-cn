open Soteria.Logs.Import
open Soteria_c_lib
module Mu = Usable_mucore
open Csymex

type term = Cn.(BaseTypes.t Terms.term)
type annot = Cn.(BaseTypes.t Terms.annot)

exception Not_implemented of annot

let rec eval_annot (subst : Subst.t) (annot : annot) : Core_value.t =
  let (IT (it, _bt, _loc)) = annot in
  match it with
  | Sym s -> Subst.find s subst
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

let nondet_bt (bt : Cn.BaseTypes.t) : Core_value.t Csymex.t =
  let open Syntax in
  match bt with
  | Bool ->
      let+ b = Csymex.nondet Typed.t_bool in
      Core_value.Bool b
  | Bits (_sign, size_bits) ->
      let+ v = Csymex.nondet (Typed.t_int size_bits) in
      Core_value.(Obj (Int v))
  | Loc _ ->
      let* loc = Csymex.nondet Typed.t_loc in
      let+ ofs = Csymex.nondet Typed.t_usize in
      let ptr = Typed.Ptr.mk loc ofs in
      Core_value.(Obj (Ptr ptr))
  | _ -> Fmt.kstr not_impl "nondet_bt: %a" Mu.pp_bt bt

let produce_computational_arg (subst, state)
    ((arg, _loc) : Mu.computational_arg * Cn.Locations.info) :
    (Subst.t * State.t option) Csymex.Producer.t =
  let open Producer in
  let open Syntax in
  (* let@ () = Producer.with_loc ~loc:(snd loc) in *)
  let (Computational (sym, ty) | Ghost (sym, ty)) = arg in
  let+^ v = nondet_bt ty in
  let subst = Subst.add sym v subst in
  (subst, state)

let produce_logical_arg (_subst, _state)
    ((_arg, _loc) : Mu.logical_arg * Cn.Locations.info) :
    (Subst.t * State.t option) Csymex.Producer.t =
  Producer.lift @@ not_impl "produce_logical_arg: not implemented yet"

let produce_arguments (args : Mu.arguments) :
    (Subst.t * State.t option) Csymex.Producer.t =
  let open Csymex.Producer in
  let open Syntax in
  let subst = Subst.empty in
  let state = State.empty in
  let* subst, state =
    fold_list ~init:(subst, state) ~f:produce_computational_arg args.comp
  in
  fold_list ~init:(subst, state) ~f:produce_logical_arg args.logic

let consume_annot (subst, state) annot =
  let open Csymex.Consumer in
  let open Syntax in
  let*^ v = eval_annot subst annot in
  let*^ v =
    Core_value.cast_bool v
    |> of_opt_not_impl ~msg:"consume_annot: not a boolean"
  in
  let+ () = Csymex.Consumer.assert_pure v in
  (subst, state)

let consume_logical_constraint (subst, state) (lc : Cn.LogicalConstraints.t) :
    (Subst.t * State.t option, _) Csymex.Consumer.t =
  match lc with
  | T it -> consume_annot (subst, state) it
  | Forall _ -> Consumer.lift @@ not_impl "consume_logical_constraint: Forall"

let consume_logical_arg (subst, state)
    ((arg, _loc) : Mu.logical_arg * Cn.Locations.info) :
    (Subst.t * State.t option, _) Csymex.Consumer.t =
  match arg with
  | Define _ -> Consumer.lift @@ not_impl "consume_logical_arg: Define"
  | Resource _ -> Consumer.lift @@ not_impl "consume_logical_arg: Resource"
  | Constraint lc -> consume_logical_constraint (subst, state) lc

let consume_return_type (ty : Mu.return_type) (ret : Core_value.t) subst state :
    (Subst.t * State.t option, State.syn list) Csymex.Consumer.t =
  [%l.trace "Consuming return type: %a" Mu.pp_return_type ty];
  let open Csymex.Consumer in
  let subst = Subst.add (fst ty.ret) ret subst in
  fold_list ~init:(subst, state) ~f:consume_logical_arg ty.logic
