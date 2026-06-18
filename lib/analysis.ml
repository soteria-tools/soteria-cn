module Mu = Cn.Mucore
module Pp = Cn.Pp
open Pp.Infix

(* Reconstruct a function's full CN specification (both the [requires] and the
   [ensures] clauses) as an [ArgumentTypes.ft] and print it with CN's own
   pretty-printer. CN's readable Mucore printer folds the postcondition into the
   elaborated return type and elides it, so we surface it here to make every
   user annotation visible. *)
let pp_ft = Cn.Pp_mucore.Pp_typ.pp_ft

let spec_of_fun = function
  | Mu.Proc { args_and_body; _ } ->
    Some (Cn.Core_to_mucore.at_of_arguments (fun (_body, _labels, rt) -> rt) args_and_body)
  | Mu.ProcDecl (_loc, ft_opt) -> ft_opt


let pp_specs funs =
  Pmap.fold
    (fun sym decl acc ->
       match spec_of_fun decl with
       | None -> acc
       | Some ft ->
         acc
         ^^ Cn.Sym.pp sym
         ^^ Pp.colon
         ^^^ Pp.nest 2 (Pp.break 1 ^^ pp_ft ft)
         ^^ Pp.hardline
         ^^ Pp.hardline)
    funs
    Pp.empty


let analyse (mucore_ast : unit Cn.Mucore.file) =
  Pp.print stdout (!^"-- Specifications" ^^ Pp.hardline ^^ Pp.hardline);
  Pp.print stdout (pp_specs mucore_ast.funs);
  Pp.print stdout (!^"-- Mucore" ^^ Pp.hardline);
  Pp.print stdout (Cn.Pp_mucore.pp_file mucore_ast)
  
