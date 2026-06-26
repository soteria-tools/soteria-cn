module SState = State
open Soteria_c_lib
open Soteria.Soteria_std
open Soteria.Logs.Import
open Core_value.Syntax
open Syntaxes.FunctionWrap
open Csymex
module Mu = Usable_mucore
open Mu
open SState.SM
include Result

type 'a t = ('a, Cn_error.with_trace, SState.syn list) Result.t

let lift (type a) (m : a Csymex.t) : a t =
  SState.SM.lift @@ Csymex.map Compo_res.ok m

let lift_symex_res (type a)
    (s : (a, Cn_error.with_trace, SState.syn list) Csymex.Result.t) : a t =
  SState.SM.lift s

let with_extra_call_trace ~loc ~msg : 'a t -> 'a t =
  map_error @@ fun (e, trace) ->
  let elem = Soteria.Terminal.Call_trace.mk_element ~loc ~msg () in
  (e, elem :: trace)

let branches b = SState.SM.branches b

let[@inline] error (err : Cn_error.t) : 'a t =
  lift_symex_res @@ Cn_error.error_with_loc err

let not_impl fmt =
  Fmt.kstr (fun str -> SState.SM.lift @@ Soteria_c_helpers.not_impl str) fmt

let of_opt_not_impl ~msg = function Some x -> ok x | None -> not_impl "%s" msg

let with_loc ~loc (f : unit -> 'a t) =
 fun state -> Csymex.with_loc ~loc (f () state)

module CV = struct
  let cast_int v =
    Core_value.cast_int v
    |> of_opt_not_impl ~msg:"cast_int: value is not an integer"

  let cast_type v =
    Core_value.cast_type v
    |> of_opt_not_impl ~msg:"cast_type: value is not a type"

  let cast_ptr v =
    Core_value.cast_ptr v
    |> of_opt_not_impl ~msg:"cast_ptr: value is not a pointer"
end

module Syntax = struct
  let ( let* ) x f = bind f x
  let ( let+ ) x f = map f x
  let ( let*^ ) (x : 'a Csymex.t) (f : 'a -> 'b t) : 'b t = bind f (lift x)
  let ( let+^ ) (x : 'a Csymex.t) (f : 'a -> 'b) : 'b t = map f (lift x)

  module Symex_syntax = Syntax.Symex_syntax
end

module State = struct
  open Syntax

  let with_miss_as_error :
      'a.
      ('a, Error.with_trace, SState.syn list) Result.t ->
      ('a, Cn_error.with_trace, SState.syn list) Result.t =
   fun m ->
    let*^ loc = Csymex.get_loc () in
    let trace =
      Soteria.Terminal.Call_trace.singleton ~loc
        ~msg:
          "Memory operation requires additional resource (it may be hidden in \
           predicates?)"
        ()
    in
    SState.SM.map
      (function
        | Compo_res.Ok r -> Compo_res.Ok r
        | Error (e, tr) -> Error ((e :> Cn_error.t), tr)
        | Missing _ -> Error (`Missing_resource, trace))
      m

  let alloc_ty ty =
    with_miss_as_error @@ SState.alloc_ty (Cn.Sctypes.to_ctype ty)

  let alloc size =
    let@@ () = with_miss_as_error in
    let* size = CV.cast_int size in
    SState.alloc size

  let store ptr ty v =
    let@@ () = with_miss_as_error in
    let* ptr = CV.cast_ptr ptr in
    let ty = Cn.Sctypes.to_ctype ty in
    let v = Core_value.to_agv v in
    SState.store ptr ty v

  let load ptr ty =
    let@@ () = with_miss_as_error in
    let* ptr = CV.cast_ptr ptr in
    let ty = Cn.Sctypes.to_ctype ty in
    let+ v = SState.load ptr ty in
    Core_value.of_agv ~ty v

  let free ptr =
    let@@ () = with_miss_as_error in
    let* ptr = CV.cast_ptr ptr in
    SState.free ptr
end
