let arg = try Sys.argv.(1) with _ -> failwith "No argument provided"

let () =
  match Soteria_cn.Driver.exec_main arg with
  | Ok () -> ()
  | Error msg ->
      Printf.eprintf "Error: %s\n" msg;
      exit 1
