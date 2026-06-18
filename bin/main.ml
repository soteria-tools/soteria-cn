let arg =
  try Sys.argv.(1) with
  | _ -> failwith "No argument provided"

let () = Soteria_cn.Driver.analyse_file arg


