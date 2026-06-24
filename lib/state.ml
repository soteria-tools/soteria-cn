open Soteria_c_lib
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
open Core_value.Syntax
open Csymex
module Mu = Usable_mucore
open Mu
include State

let produce_core_value (_ptr : Typed.(T.sptr t)) = ()

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
