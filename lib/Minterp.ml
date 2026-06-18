open Soteria_c_lib
module Mu = Cn.Mucore
module Pp = Cn.Pp
open Pp.Infix
module State = Soteria_c_lib.State

let sym_is_id sym id =
  let open Cerb_frontend.Symbol in
  match sym with Symbol (_digest, _i, SD_Id id') -> id = id' | _ -> false

let exec_fun (_mucore_fn : unit Cn.Mucore.fun_map_decl) args = Csymex.return ()
