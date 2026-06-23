  $ soteria-cn exec simple.c
  Successfully finished with (Loaded (Spec (Int 0x00000000)))
  Finished without errors!

  $ soteria-cn exec call.c
  Successfully finished with (Loaded (Spec (Int 0x0000002a)))
  Finished without errors!

  $ soteria-cn exec if_null.c
  Successfully finished with (Loaded (Spec (Int 0x00000000)))
  Finished without errors!

  $ soteria-cn exec sll.c
  Successfully finished with (Loaded (Spec (Int 0x00000000)))
  Successfully finished with (Loaded (Spec (Int 0x00000000)))
  Successfully finished with (Loaded (Spec (Int 0x00000000)))
  Successfully finished with (Loaded (Spec (Int 0x00000000)))
  Successfully finished with (Loaded (Spec (Int 0x00000000)))
  Finished without errors!

  $ soteria-cn exec many_loops.c --alloc-cannot-fail
  Successfully finished with (Loaded (Spec (Int 0x00001356)))
  Finished without errors!
