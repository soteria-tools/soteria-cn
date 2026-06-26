open Soteria
open Soteria_std
open Logs.Import

open Sym_states
(** Symbolic state combinator for supporting inductive predicates. *)

(** Defining this here out of convenience but it will be move to the
    Soteria.Sym_states library. *)

module type Name = [%mixins Sigs.Printable + Map.OrderedType]

module M (Symex : Symex.Base) = struct
  module Abstr = Data.Abstr.M (Symex)

  module type V = [%mixins Abstr.S_with_syn + Abstr.Sem_eq]

  (** A VeriFast-like representation of any state as opaque uninterpreted. This
      state model is {b OX-only}! Predicates can always hide unsatisfiable
      states, and are matched against using entailments. *)
  module Uninterpreted (Name : Name) (V : V) = struct
    type pred = Name.t * V.t list * V.t list
    [@@deriving show { with_path = false }]

    type t = pred list [@@deriving show { with_path = false }]

    type syn = Name.t * V.syn list * V.syn list
    [@@deriving show { with_path = false }]

    let of_opt = Option.value ~default:[]
    let to_opt = function [] -> None | x -> Some x

    let to_syn : t -> syn list =
      List.map (fun (name, ins, outs) ->
          (name, List.map V.to_syn ins, List.map V.to_syn outs))

    let ins_outs (_, ins, outs) =
      (List.concat_map V.exprs_syn ins, List.concat_map V.exprs_syn outs)

    let rec sure_list_eq (l1 : V.t list) (l2 : V.t list) : bool Symex.t =
      let open Symex.Syntax in
      match (l1, l2) with
      | [], [] -> Symex.return true
      | x :: xs, y :: ys ->
          if%sure V.sem_eq x y then sure_list_eq xs ys else Symex.return false
      | _, _ -> L.failwith "Predicate parameter lists have different lengths"

    module SM =
      State_monad.Make
        (Symex)
        (struct
          type nonrec t = t option
        end)

    let produce' (name : Name.t) (ins : V.t list) (outs : V.t list)
        (state : t option) : t option Symex.t =
      (* Producing just adds to the list really. *)
      Symex.return (to_opt ((name, ins, outs) :: of_opt state))

    let produce (name, ins, outs) state =
      let open Symex.Producer in
      let open Syntax in
      let* ins = map_list ~f:(apply_subst V.subst) ins in
      let* outs = map_list ~f:(apply_subst V.subst) outs in
      lift (produce' name ins outs state)

    open SM
    open SM.Syntax

    let consume' name ins =
      let* state = get_state () in
      let rec find_and_remove = function
        | [] -> Result.miss_no_fix ~reason:"Missing predicate" ()
        | (n, i, o) :: rest
          when Name.compare n name = 0 && List.compare_lengths i ins = 0 ->
            let*^ eq = sure_list_eq i ins in
            if eq then Result.ok (o, rest) else find_and_remove rest
        | _ :: rest -> find_and_remove rest
      in
      let** outs, new_state = find_and_remove (of_opt state) in
      let+ () = set_state (to_opt new_state) in
      Compo_res.Ok outs

    let consume ((name, ins, outs) : syn) state =
      let open Symex.Consumer in
      let open Syntax in
      let* ins = map_list ~f:(apply_subst V.subst) ins in
      let*^ louts, state = consume' name ins state in
      let* louts =
        (* This is a bit disgusting but ok *)
        lift_res (Symex.return louts)
      in
      let* () =
        iter_iter
          ~f:(fun (x, y) -> V.learn_eq x y)
          (Iter.of_list_combine outs louts)
      in
      ok state
  end

  module With_preds (Name : Name) (V : V) (B : Base.M(Symex).S) = struct
    module Uninterpreted = Uninterpreted (Name) (V)

    type t = { base : B.t option; preds : Uninterpreted.t option }
    [@@deriving sym_state { symex = Symex }]

    open SM
    open SM.Syntax

    let unfold ~produce_def name ins =
      let** outs = with_preds (Uninterpreted.consume' name ins) in
      let* state = get_state () in
      let*^ state = produce_def name ins outs state in
      let+ () = set_state state in
      Compo_res.Ok ()

    let fold ~consume_def name ins =
      let** outs = consume_def name ins in
      with_preds (fun state ->
          let open Symex.Syntax in
          let+ state = Uninterpreted.produce' name ins outs state in
          (Compo_res.Ok (), state))
  end

  module _ (Name : Name) (V : V) : Base.M(Symex).S = Uninterpreted (Name) (V)

  module _ (Name : Name) (V : V) (B : Base.M(Symex).S) :
    Sym_states.Base.M(Symex).S =
    With_preds (Name) (V) (B)
end
