open Soteria.Soteria_std
module CF = Cerb_frontend
module CB = Cerb_backend
open CB.Pipeline
open Cn
open Setup
open Syntaxes.FunctionWrap

module Frontend = struct
  (* Run Cerberus' C frontend and Core elaboration on [filename], then rewrite the
   resulting Core program down to the Milicore representation that
   [Core_to_mucore.normalise_file] expects. This is a trimmed-down copy of
   [cn/bin/common.ml]'s [frontend], keeping only what is needed to obtain the
   Mucore AST (no Coq export, CSV timing, etc.). The CLI knobs are fixed to the
   values CN uses by default. *)
  let frontend ~filename =
    Cerb_global.set_cerb_conf ~backend_name:"Cn" ~exec:false
      (* execution mode *) Random ~concurrency:false (* error verbosity *) Basic
      ~defacto:false ~permissive:false ~agnostic:false ~ignore_bitfields:false;
    CF.Ocaml_implementation.set CF.Ocaml_implementation.HafniumImpl.impl;
    CF.Switches.set [ "inner_arg_temps"; "at_magic_comments" ];
    let return = CF.Exception.except_return in
    let ( let@ ) = CF.Exception.except_bind in
    let@ stdlib = load_core_stdlib () in
    let@ impl = load_core_impl stdlib impl_name in
    let conf =
      Setup.conf "cc" [] [] [] (* disable_linemarkers *) false []
        (* save_cpp *) None
    in
    let cn_init_scope : CF.Cn_desugaring.init_scope =
      {
        predicates = [ Alloc.Predicate.(str, sym, Some loc) ];
        functions =
          List.map (fun (str, sym) -> (str, sym, None)) Builtins.fun_names;
        idents = [ Alloc.History.(str, sym, None) ];
      }
    in
    let@ _cabs_tunit_opt, ail_prog_opt, prog0 =
      c_frontend_and_elaboration ~cn_init_scope (conf, io) (stdlib, impl)
        ~filename
    in
    let@ () =
      if conf.typecheck_core then
        let@ _ = CF.Core_typing.typecheck_program prog0 in
        return ()
      else return ()
    in
    let markers_env, ail_prog = Option.get ail_prog_opt in
    CF.Tags.set_tagDefs prog0.CF.Core.tagDefs;
    (* Mandatory: [Core_to_mucore] has no case for [Ecase], which Core elaboration
     emits around possibly-unspecified values. This pass rewrites them away. *)
    let prog1 = CF.Remove_unspecs.rewrite_file prog0 in
    let prog2 = CF.Milicore.core_to_micore__file Locations.update prog1 in
    let prog3 = CF.Milicore_label_inline.rewrite_file prog2 in
    return (markers_env, ail_prog, prog3)

  let handle_frontend_error = function
    | CF.Exception.Exception err ->
        prerr_endline (CF.Pp_errors.to_string err);
        exit 2
    | CF.Exception.Result result -> result

  (* Load [file] and elaborate it all the way down to CN's Mucore AST, which
   carries the user's CN annotations (function specs, loop invariants, inline
   asserts, ...). *)
  let load_mucore_ast file : unit Mucore.file =
    let markers_env, ail_prog, prog2 =
      handle_frontend_error (frontend ~filename:file)
    in
    match
      Core_to_mucore.normalise_file ~inherit_loc:true
        (markers_env, snd ail_prog)
        prog2
    with
    | Ok prog3 -> prog3
    | Error err ->
        TypeErrors.report_pretty err;
        exit 1
end

(* Helper for all main entry points *)
let initialise ?soteria_config mode config f =
  Option.iter Soteria.Config.set_and_lock soteria_config;
  let@ () = Soteria_c_lib.Config.with_config ~config ~mode in
  Soteria.Stats.As_ctx.with_dumped () f

let exec_main config c_config fuel file =
  let open Soteria_c_lib in
  let open Syntaxes.Result in
  let* file = Option.to_result ~none:"No input file provided" file in
  let fuel = Soteria.Symex.Fuel_gauge.Cli.validate_or_exit fuel in
  let@ () = initialise ~soteria_config:config Whole_program c_config in
  let mucore_file = Frontend.load_mucore_ast file in
  let umucore = Usable_mucore.of_mucore mucore_file in
  let+ main = Option.to_result ~none:"No main function" umucore.main in
  let main = Symbol_std.Map.find main umucore.funs in
  let results =
    let computation = Minterp.exec_fun main [] in
    Csymex.Result.run ~fuel ~mode:OX computation
  in
  Fmt.pr "Execution results: %a\n"
    Fmt.Dump.(
      list
      @@ pair
           (Compo_res.pp ~ok:(Fmt.any "()")
              ~err:(Soteria.Symex.Or_gave_up.pp Fmt.string)
              ~miss:(Fmt.any "miss"))
           (list Csymex.Value.Expr.pp))
    results;
  ()
