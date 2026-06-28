open Soteria_c_lib
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
open Core_value.Syntax
open Csymex
module Mu = Usable_mucore
open Mu
module Predicates = Predicates.M (Csymex)

module SState = struct
  include Soteria_c_lib.State

  let consume_owned ptr ty : (Core_value.t, _, _) SM.Result.t =
    let open SM.Syntax in
    let ty = Sctypes.to_ctype ty in
    let++ v = consume_aggregate' ptr ty in
    Core_value.of_agv ~ty v

  let consume_uninit ptr ty =
    let open SM.Syntax in
    let*^ len = Layout.size_of_s (Sctypes.to_ctype ty) in
    let loc = Typed.Ptr.loc ptr in
    let ofs = Typed.Ptr.ofs ptr in
    let++ () = consume_uninit' loc ofs len in
    Core_value.Loaded Unspec

  let consume_any ptr ty =
    let open SM.Syntax in
    let*^ len = Layout.size_of_s (Sctypes.to_ctype ty) in
    let loc = Typed.Ptr.loc ptr in
    let ofs = Typed.Ptr.ofs ptr in
    let++ () = consume_any' loc ofs len in
    Core_value.Loaded Unspec

  let produce_owned (ptr : Typed.(T.sptr t)) (ty : Sctypes.t) (v : Core_value.t)
      (t : t option) : t option Csymex.t =
    let ty = Sctypes.to_ctype ty in
    let agv = Core_value.to_agv v in
    produce_aggregate' ptr ty agv t

  let leaks (state : t option) : Cerb_location.t option list =
    let result =
      match state with
      | None | Some Soteria_c_lib.State.{ heap = None; _ } -> []
      | Some { heap = Some heap; _ } ->
          Seq.filter_map
            (fun (_, (block : Block.t)) ->
              if not (Block.is_freed block) then Some block.info else None)
            (Heap.syntactic_bindings heap)
          |> List.of_seq
    in
    List.sort_uniq Stdlib.compare result
end

module PState = Predicates.With_preds (Symbol_std) (Core_value) (State)
include PState

let lift_produce (f : SState.t option -> SState.t option Csymex.t) :
    t option -> t option Csymex.t =
  let open Csymex.Syntax in
  fun state ->
    let { preds; base } = PState.of_opt state in
    let+ base = f base in
    PState.to_opt { preds; base }

let pp_pretty ~ignore_freed ft { base; preds } =
  Fmt.pf ft "@[<v 2>State:@ %a@]@ @[<v 2>Predicates:@ %a@]"
    (Fmt.option ~none:(Fmt.any "Empty Heap") @@ SState.pp_pretty ~ignore_freed)
    base
    (Fmt.option @@ Uninterpreted.pp)
    preds

let produce_owned ptr cty v = lift_produce (SState.produce_owned ptr cty v)
let produce_any' loc ofs len = lift_produce (SState.produce_any' loc ofs len)

let produce_uninit' loc ofs len =
  lift_produce (SState.produce_uninit' loc ofs len)

let consume_owned ptr ty = with_base (SState.consume_owned ptr ty)
let consume_any ptr ty = with_base (SState.consume_any ptr ty)
let consume_uninit ptr ty = with_base (SState.consume_uninit ptr ty)
let alloc_ty ty = with_base (SState.alloc_ty ty)
let alloc size = with_base (SState.alloc size)
let store ptr ty v = with_base (SState.store ptr ty v)
let load ptr ty = with_base (SState.load ptr ty)
let free ptr = with_base (SState.free ptr)

let leaks state =
  let { base; preds } = of_opt state in
  (* FIXME: we can do better! *)
  let pred_leaks = if Option.is_none preds then [] else [ None ] in
  pred_leaks @ SState.leaks base
