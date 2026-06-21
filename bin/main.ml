open Cmdliner
open Soteria.Soteria_std.Cmdliner_helpers

let result_to_int (x : (_, _) result) : int =
  match x with Ok _ -> 0 | Error _ -> 1

module Exec_main = struct
  let file_arg = Arg.(value & pos 0 (some file) None & info ~docv:"FILE" [])

  let entry_point_arg =
    let doc = "Entry point of the program to execute" in
    let docv = "ENTRYPOINT" in
    Arg.(
      value & opt string "main"
      & info
          [ "entry"; "entry-point"; "harness" ]
          ~docs:Sections.frontend ~doc ~docv)

  let term =
    Term.(
      const Soteria_cn.Driver.exec_main
      $ Soteria.Config.cmdliner_term ()
      $ Soteria_c_lib.Config.cmdliner_term ()
      $ Soteria.Symex.Fuel_gauge.Cli.term
          ~default:Soteria.Symex.Fuel_gauge.infinite ()
      $ file_arg)

  let cmd =
    Cmd.v
      (Cmd.info
         ~doc:"Symbolically execute a program starting from the main function."
         "exec")
      (Term.map result_to_int term)
end

let arg = try Sys.argv.(1) with _ -> failwith "No argument provided"
let cmd = Cmd.group (Cmd.info "soteria-cn") [ Exec_main.cmd ]
let () = exit @@ Cmd.eval' cmd
