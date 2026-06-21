type _ Effect.t += Get_prog : Usable_mucore.file Effect.t

let get_prog () = Effect.perform Get_prog

let run_with_prog (prog : Usable_mucore.file) f =
  try f () with effect Get_prog, k -> Effect.Deep.continue k prog
