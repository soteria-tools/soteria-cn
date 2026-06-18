let pp_to_fmt (pprinter : 'a -> PPrint.document) :
    Format.formatter -> 'a -> unit =
 fun ft a ->
  let buffer = Buffer.create 1023 in
  PPrint.ToBuffer.pretty 0.5 80 buffer (pprinter a);
  Fmt.pf ft "%s" (Buffer.contents buffer)

let pp_file ft file = (pp_to_fmt Cn.Pp_mucore.pp_file) ft file

let pp_fun_map_decl ft fun_map_decl =
  let fake_sym =
    Cerb_frontend.Symbol.Symbol ("Fake", 0, Cerb_frontend.Symbol.SD_None)
  in
  let pmap =
    Pmap.singleton Cerb_frontend.Symbol.compare_sym fake_sym fun_map_decl
  in
  (pp_to_fmt @@ Cn.Pp_mucore.Basic.pp_fun_map None) ft pmap
