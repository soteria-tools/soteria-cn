open Soteria_c_lib
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
open Core_value.Syntax
open Csymex
module Mu = Usable_mucore
open Mu
include State

let consume_owned ptr ty state =
  let open Csymex.Syntax in
  let ty = Sctypes.to_ctype ty in
  let++ v, state =
    SM.Result.run_with_state ~state (consume_aggregate' ptr ty)
  in
  (Core_value.of_agv ~ty v, state)

let consume_uninit ptr ty state =
  let open Csymex.Syntax in
  let* len = Layout.size_of_s (Sctypes.to_ctype ty) in
  let loc = Typed.Ptr.loc ptr in
  let ofs = Typed.Ptr.ofs ptr in
  let++ (), state =
    SM.Result.run_with_state ~state (consume_uninit' loc ofs len)
  in
  (Core_value.Loaded Unspec, state)

let consume_any ptr ty state =
  let open Csymex.Syntax in
  let* len = Layout.size_of_s (Sctypes.to_ctype ty) in
  let loc = Typed.Ptr.loc ptr in
  let ofs = Typed.Ptr.ofs ptr in
  let++ (), state =
    SM.Result.run_with_state ~state (consume_any' loc ofs len)
  in
  (Core_value.Loaded Unspec, state)

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
