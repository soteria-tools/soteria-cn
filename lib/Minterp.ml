open Soteria_c_lib
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
open Csymex
module Mu = Usable_mucore

let sym_is_id sym id =
  let open Cerb_frontend.Symbol in
  match sym with Symbol (_digest, _i, SD_Id id') -> id = id' | _ -> false

let exec_fun (fn : Mu.fun_map_decl) args =
  [%l.trace "Executing function: %a" Mu.pp_fun_map_decl fn];
  match fn with
  | ProcDecl _ -> Csymex.not_impl "exec_fn: ProcDecl"
  | Proc { loc; args_and_body; trusted = _ } ->
      let@@ () = Csymex.with_loc ~loc in
      return ()
