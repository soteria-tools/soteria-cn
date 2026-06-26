module Csymex = Soteria_c_lib.Csymex

type t =
  [ Soteria_c_lib.Error.t | Csymex.cons_fail | `Missing_resource | `No_spec ]

type with_trace = t * Cerb_location.t Soteria.Terminal.Call_trace.t

let error_with_loc ?(msg = "Triggering operation") (err : t) =
  let open Csymex.Syntax in
  let* loc = Csymex.get_loc () in
  let err = (err, Soteria.Terminal.Call_trace.singleton ~loc ~msg ()) in
  Csymex.Result.error err
