  $ soteria-cn simple.c
  -- Specifications
  
  
  main:
    Σ return : i32. I
  
  
  -- Mucore
  
  
  
  
  
  proc main_474 = -> (=
  
    return label ret_477_477
  
    body =
       let strong _: unit =
         let strong _: unit =
          {-#stmt#-} let strong _: unit =
            {-#stmt#-} let strong a_478: loaded integer =
               bound({-#expr#-}{-#type signed int#-} pure( (specified 0))) in
             run ret_477_477( conv_loaded_int( ''signed int'',  a_478)) in
           pure( Unit) in
         pure( Unit) in
      {-#return#-} run ret_477_477( Specified( 0)))
  
  
  $ soteria-cn call.c
  -- Specifications
  
  
  f:
    Π x : i32. Σ return : i32. I
  
  main:
    Σ return : i32. I
  
  
  -- Mucore
  
  
  
  
  
  proc f_475 = (x_498 : i32) -> (=
  
    return label ret_499_499
  
    body =
       let strong _: unit =
         let strong x_474: pointer =
           create( Ivalignof( ''signed int''), signed int) in
         let strong _: unit =  store(signed int,  x_474,  x_498 NA) in
         let strong _: unit =
          {-#stmt#-} let strong _: unit =
            {-#stmt#-} let strong a_506: loaded integer =
               bound({-#expr#-}{-#type signed int#-} let weak (a_500: loaded integer,
                a_501: loaded integer) =
                   unseq({-#expr#-}{-#type signed int#-} let weak a_505: pointer =
                    {-#expr#-} pure( x_474) in
                   load(signed int,  a_505 NA),
                  {-#expr#-}{-#type signed int#-} pure( (specified 1))) in
                 pure( let (Specified(a_502: integer), Specified(a_503: integer)) =  ( a_500,
                 a_501) in
                 Specified( catch_exceptional_condition('signed int', '+',
                 conv_int( ''signed int'',  a_502),
                 conv_int( ''signed int'',  a_503))))) in
             let strong _: unit =  kill(signed int,  x_474) in
             run ret_499_499( conv_loaded_int( ''signed int'',  a_506)) in
           pure( Unit) in
         let strong _: unit =  kill(signed int,  x_474) in
         pure( Unit) in
      {-#return#-} run ret_499_499( undef(<<UB088_reached_end_of_function>>)))
  
  proc main_477 = -> (=
  
    return label ret_480_480
  
    body =
       let strong _: unit =
         let strong _: unit =
          {-#stmt#-} let strong _: unit =
            {-#stmt#-} let strong a_496: loaded integer =
               bound({-#expr#-}{-#type signed int#-} let strong ((a_482: loaded pointer,
                (a_483: ctype, a_484: [ctype], a_485: boolean, a_486: boolean)),
                a_488: loaded integer) =
                   unseq( let strong a_481: loaded pointer =
                    {-#expr#-} pure( (specified Cfunction(f))) in
                   pure( ( a_481,  cfunction( a_481))),
                  {-#expr#-}{-#type signed int#-} let weak a_490: loaded integer =
                    {-#expr#-}{-#type signed int#-} pure( (specified 1)) in
                   pure( let Specified(a_489: integer) =  a_490 in
                   Specified( catch_exceptional_condition('signed int', '-',  0,
                   conv_int( ''signed int'',  a_489))))) in
                 if  not(  params_length( a_484) =  1) then
                   pure( undef(<<UB038_number_of_args>>))
                else
                   if   a_485 \/  not( are_compatible( ''signed int'',  a_483)) then
                     pure( undef(<<UB041_function_not_compatible>>))
                  else
                     ccall(signed int (signed int)*)( a_482,
                     let a_493: ctype =  params_nth( a_484,  0) in
                     if  not( are_compatible( ''signed int'',  a_493)) then
                       undef(<<UB041_function_not_compatible>>)
                    else
                       conv_loaded_int( ''signed int'',  a_488))((empty))) in
             run ret_480_480( conv_loaded_int( ''signed int'',  a_496)) in
           pure( Unit) in
         pure( Unit) in
      {-#return#-} run ret_480_480( Specified( 0)))
  
  
