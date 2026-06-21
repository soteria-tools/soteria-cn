  $ soteria-cn exec simple.c
  Execution results: [(Ok: (), [])]

  $ soteria-cn exec call.c
  Execution results: [(Error: Gave up: Unsupported: Unsupported expr: unseq(let strong a_524 = pure(Cfunction(f)) in
                          pure(Tuple(a_524, cfunction(a_524))),
                      let weak a_533 = pure(1) in
                      pure(let Specified(a_532) = a_533 in
                           Specified(catch(0 - conv_int_100(signed int, a_532))))),
                       [])]
