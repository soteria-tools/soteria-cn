# This document catalogues the limitations of Core/Mucore I have found

## Short circuiting

In code like this, I expect to have only 3 branches of execution, following the
shape of the program (`min3.c` from the CN tutorial):
```c
if (x <= y && x <= z) {
    return x;
}
else if (y <= x && y <= z) {
    return y; // fixed
}
else {
    return z;
}
```

However, the semantics of C is such that, in the first condition for instance,
the comparison `x <= z` isn't computed if `x <= y` doesn't hold (`&&` is
short-circuiting). A direct consequence is that the corresponding Core code
corresponds to the following:
```ocaml
if x <= y then
  if x <= z then 
    ...
  else ...
else ...
```
Because I don't hold a single expression, with the `&&`, it is impossible to
optimise away that additional branching condition, even if the second computation
has no side effect and therefore cannot cause any trouble if evaluated eagerly.

This means that:
1) The execution yields 5 branches instead of 3, and for each branch we have to
unify against the post-condition. That's 1.66x more work that needed, especially
when each post condition unification can be quite expensive in real verification.
2) We have more back-and-forth between the execution engine and the solver, for
trivial queries. In these cases, the IO is more expensive than the sat check
itself.

## Size of the AST

Take the `min3` function from above. The AIL code is:
```c
unsigned int min3(unsigned int x, unsigned int y, unsigned int z)
{
  if (rvalue(x) <= rvalue(y) && rvalue(x) <= rvalue(z)) {
    return rvalue(x);
  }
  else
    if (rvalue(y) <= rvalue(x) && rvalue(y) <= rvalue(z)) {
    return rvalue(y);
  }
  else {
    return rvalue(z);
  }
}
```

It contains 9 statements. This means 9 times the interpreter has to
pattern-match against an OCaml value, decide what to execute etc.
In addition, each of these statements are extremely cheap to execute.
`rvalue(x)` simply loads the value in the store at `x`, `return` statements just
stop execution etc.

In comparison, here's the (Mu)core AST:
```ocaml
let strong x_517 = create(Ivalignof(unsigned int), unsigned int) in
  let strong _ = store(unsigned int, x_517, x_525, na) in
  let strong y_518 = create(Ivalignof(unsigned int), unsigned int) in
  let strong _ = store(unsigned int, y_518, y_524, na) in
  let strong z_519 = create(Ivalignof(unsigned int), unsigned int) in
  let strong _ = store(unsigned int, z_519, z_523, na) in
  let strong a_528 =
    bound(
      let weak Tuple(a_530, a_531) =
        unseq(
          let weak Tuple(a_535, a_536) =
            unseq(
              let weak Tuple(a_540, a_541) =
                unseq(
                  let weak Tuple(a_547, a_548) =
                    unseq(
                      let weak a_545 = pure(x_517) in
                      load(unsigned int, a_545, na),
                      let weak a_546 = pure(y_518) in
                      load(unsigned int, a_546, na)) in
                  let Tuple(Specified(a_549),
                        Specified(a_550)) =
                    Tuple(a_547, a_548) in
                  pure(
                    if (conv_int_100(unsigned int, a_549) <=
                         conv_int_100(unsigned int, a_550)) then
                      Specified(1)
                    else Specified(0)),
                  pure(0)) in
              pure(
                let Tuple(Specified(a_542),
                      Specified(a_543)) =
                  Tuple(a_540, a_541) in
                if (conv_int_100(signed int, a_542) ==
                     conv_int_100(signed int, a_543)) then
                  Specified(1)
                else Specified(0)),
              pure(0)) in
          let strong a_552 =
            pure(
              let Tuple(Specified(a_537),
                    Specified(a_538)) =
                Tuple(a_535, a_536) in
              if (conv_int_100(signed int, a_537) ==
                   conv_int_100(signed int, a_538)) then
                Specified(1)
              else Specified(0)) in
          let Specified(a_553) = a_552 in
          if (a_553 == 0) then
            let strong a_554 = pure(0) in
            pure(conv_loaded_int_102(signed int, a_554))
          else
            let weak Tuple(a_555, a_556) =
              unseq(
                let weak Tuple(a_562, a_563) =
                  unseq(
                    let weak a_560 = pure(x_517) in
                    load(unsigned int, a_560, na),
                    let weak a_561 = pure(z_519) in
                    load(unsigned int, a_561, na)) in
                let Tuple(Specified(a_564),
                      Specified(a_565)) =
                  Tuple(a_562, a_563) in
                pure(
                  if (conv_int_100(unsigned int, a_564) <=
                       conv_int_100(unsigned int, a_565)) then
                    Specified(1)
                  else Specified(0)),
                pure(0)) in
            let strong a_567 =
              pure(
                let Tuple(Specified(a_557),
                      Specified(a_558)) =
                  Tuple(a_555, a_556) in
                if not(
                     (conv_int_100(signed int, a_557) ==
                       conv_int_100(signed int, a_558))) then
                  Specified(1)
                else Specified(0)) in
            pure(conv_loaded_int_102(signed int, a_567)),
          pure(0)) in
      pure(
        let Tuple(Specified(a_532),
              Specified(a_533)) =
          Tuple(a_530, a_531) in
        if (conv_int_100(signed int, a_532) ==
             conv_int_100(signed int, a_533)) then
          Specified(1)
        else Specified(0))) in
  let Specified(a_529) = a_528 in
  let strong a_527 = pure(if not((a_529 == 1)) then true
                          else false) in
  let strong _ =
    if a_527 then
      let strong a_569 =
        bound(let weak a_568 = pure(x_517) in
              load(unsigned int, a_568, na)) in
      let strong _ = kill(unsigned int, x_517) in
      let strong _ = kill(unsigned int, y_518) in
      let strong _ = kill(unsigned int, z_519) in
      let strong _ =
        run ret_526_526(conv_loaded_int_102(unsigned int, a_569)) in
      pure(unit)
    else
      let strong a_571 =
        bound(
          let weak Tuple(a_573, a_574) =
            unseq(
              let weak Tuple(a_578, a_579) =
                unseq(
                  let weak Tuple(a_583, a_584) =
                    unseq(
                      let weak Tuple(a_590, a_591) =
                        unseq(
                          let weak a_588 = pure(y_518) in
                          load(unsigned int, a_588, na),
                          let weak a_589 = pure(x_517) in
                          load(unsigned int, a_589, na)) in
                      let Tuple(Specified(a_592),
                            Specified(a_593)) =
                        Tuple(a_590, a_591) in
                      pure(
                        if (conv_int_100(unsigned int, a_592) <=
                             conv_int_100(unsigned int, a_593)) then
                          Specified(1)
                        else Specified(0)),
                      pure(0)) in
                  pure(
                    let Tuple(Specified(a_585),
                          Specified(a_586)) =
                      Tuple(a_583, a_584) in
                    if (conv_int_100(signed int, a_585) ==
                         conv_int_100(signed int, a_586)) then
                      Specified(1)
                    else Specified(0)),
                  pure(0)) in
              let strong a_595 =
                pure(
                  let Tuple(Specified(a_580),
                        Specified(a_581)) =
                    Tuple(a_578, a_579) in
                  if (conv_int_100(signed int, a_580) ==
                       conv_int_100(signed int, a_581)) then
                    Specified(1)
                  else Specified(0)) in
              let Specified(a_596) = a_595 in
              if (a_596 == 0) then
                let strong a_597 = pure(0) in
                pure(conv_loaded_int_102(signed int, a_597))
              else
                let weak Tuple(a_598, a_599) =
                  unseq(
                    let weak Tuple(a_605, a_606) =
                      unseq(
                        let weak a_603 = pure(y_518) in
                        load(unsigned int, a_603, na),
                        let weak a_604 = pure(z_519) in
                        load(unsigned int, a_604, na)) in
                    let Tuple(Specified(a_607),
                          Specified(a_608)) =
                      Tuple(a_605, a_606) in
                    pure(
                      if (conv_int_100(unsigned int, a_607) <=
                           conv_int_100(unsigned int, a_608)) then
                        Specified(1)
                      else Specified(0)),
                    pure(0)) in
                let strong a_610 =
                  pure(
                    let Tuple(Specified(a_600),
                          Specified(a_601)) =
                      Tuple(a_598, a_599) in
                    if not(
                         (conv_int_100(signed int, a_600) ==
                           conv_int_100(signed int, a_601))) then
                      Specified(1)
                    else Specified(0)) in
                pure(conv_loaded_int_102(signed int, a_610)),
              pure(0)) in
          pure(
            let Tuple(Specified(a_575),
                  Specified(a_576)) =
              Tuple(a_573, a_574) in
            if (conv_int_100(signed int, a_575) ==
                 conv_int_100(signed int, a_576)) then
              Specified(1)
            else Specified(0))) in
      let Specified(a_572) = a_571 in
      let strong a_570 = pure(if not((a_572 == 1)) then true
                              else false) in
      if a_570 then
        let strong a_612 =
          bound(let weak a_611 = pure(y_518) in
                load(unsigned int, a_611, na)) in
        let strong _ = kill(unsigned int, x_517) in
        let strong _ = kill(unsigned int, y_518) in
        let strong _ = kill(unsigned int, z_519) in
        let strong _ =
          run ret_526_526(conv_loaded_int_102(unsigned int, a_612)) in
        pure(unit)
      else
        let strong a_614 =
          bound(let weak a_613 = pure(z_519) in
                load(unsigned int, a_613, na)) in
        let strong _ = kill(unsigned int, x_517) in
        let strong _ = kill(unsigned int, y_518) in
        let strong _ = kill(unsigned int, z_519) in
        let strong _ =
          run ret_526_526(conv_loaded_int_102(unsigned int, a_614)) in
        pure(unit) in
  let strong _ = kill(unsigned int, x_517) in
  let strong _ = kill(unsigned int, y_518) in
  let strong _ = kill(unsigned int, z_519) in
  run ret_526_526(undef(UB088_reached_end_of_function))
```

Here, the `eval_expr` function of the symbolic execution engine is called **267** times.
And some of those are more expensive than any of the statements in the AIL code.
For instance, the Core code already forces allocation and deallocation
(`create` and `kill`) of some heap values. (see Allocations below).

Similarly, the presence of tuples in the language, and the need to implement
pattern-matching as something that decomposes an object into sub-variables
seems unnecessary.

## Best Effort Abstractions & Allocation

When reasoning in Separation Logic, each points-to object in memory can become
make the reasoning harder and harder. Each pointer dereference, especially if
they're symbolic pointers, may need to iterate through the entire heap to find
a match. It is *crucial* to avoid allocating on the heap as much as possible for
performance.

When manipulating an AIL AST, allocation can be done lazily. First, simply keep
values on the "stack" (i.e. a simple map `variable -> value`), and only if needed
(i.e. if reference to the variable is taken), allocated it on the heap at this point.
In C, most variables are temporary, and remain on the stack. For instance, 
in the `min3` example above, no allocation is ever needed.

Core, on the other hand, forces allocation of each variable at the language level:
```ocaml
let strong x_517 = create(Ivalignof(unsigned int), unsigned int) in
let strong _ = store(unsigned int, x_517, x_525, na) in
let strong y_518 = create(Ivalignof(unsigned int), unsigned int) in
let strong _ = store(unsigned int, y_518, y_524, na) in
let strong z_519 = create(Ivalignof(unsigned int), unsigned int) in
let strong _ = store(unsigned int, z_519, z_523, na) in
```

By using Core instead of AIL, I yield control of these choices and prevent
any optimisation.

This ties back to a concept that I call "Best Effort Abstraction" in my thesis.
The way to optimise is usually to create layers of representation for symbolic
objects. We start by implementing the "lowest level" (for instance, allocate
every variable on the heap), and when we optimise, we create a new representation
on top (e.g. a variable store). Most values remain on the happy path (exclusively in
the store), and some values have to be "decayed" to the lower level representation
(e.g. allocated on the heap). The decaying should be done on demand and only
when necessary. We have several examples of best-effort abstraction in C and
Rust in Soteria.

Best-effort abstraction in the interpreter requires the abstraction to exist
in the interpreted language. By using an IL such as that already discarded the
abstraction, such as Core in its current design, I yield the ability to do these
optimisations.

In a sense, the inability to detect short-circuiting is also an example of
missing abstractions in Core.

Best effort abstraction is the 50% of reason why I wanted to create Soteria
and get rid of the "intermediate language to rule them all".
