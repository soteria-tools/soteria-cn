## A prototype for verifying CN specifications with Soteria

After a week of implementation, "Soteria CN" now supports a sufficient subset of Core and of the assertion language of CN to run proofs about singly-linked lists and doubly-linked lists (though I vibe coded the doubly-linked lists and their proofs cause I couldn't be bothered).

Soteria CN is faster than CN, and the gap increases as soon as task at hand get bigger. For instance, the [lists.c](https://github.com/soteria-tools/soteria-cn/blob/main/test/verif.t/lists.c) file of my test suite verifies **44x faster** in Soteria CN than it does in CN, and the [dll.c](https://github.com/soteria-tools/soteria-cn/blob/main/test/verif.t/dll.c) file verifies **54x faster** (measured with `hyperfine` to avoid noise).

Supposing this is the expected improvement on big proofs, that means a proof which runs in an hour would run in 1mn30s with Soteria CN. However, it is to be noted that I don't yet support e.g. quantified predicates so I don't know how that will perform.

### How to read the code

Soteria provides a set of basic tools to do efficient symbolic execution. It provides:
- A core symbolic execution monad
- Symbolic data structures
- Separation-logic-ready state monads

The main goal of Soteria is that it should handle the annoying piping, and the hard abstractions so that the tools implemented using Soteria can be read as if they were definitional interpreters.

This is the first time I write a compositional verifier with Soteria, so I'm also discovering that verification heuristics sometimes need to bubble up to the interpreter, and trying to decide if I like it or not.

In any case, here's the handling of two Core constructs in the Soteria-CN interpreter:
```ocaml
let rec eval_expr ~labels subst body = 
  match body.node with
  | Eif { cond; then_; else_ } ->
      (* Evaluate guard *)
      let* guard = eval_pexpr subst cond in
      (* Optional heuristics *)
      let* () = State.unfold_on_if_else guard in
      (* Cast guard to boolean *)
      let guard = Core_value.Bool.to_sbool guard in
      (* if the guard holds, evaluate else_, else evaluate then_ *)
      if%sat guard then eval_expr ~labels subst then_
      else eval_expr ~labels subst else_
  | Elet { pat; value; body = body' } ->
      (* evaluate RHS of the assignment *)
      let* v = eval_pexpr subst value in
      (* Update substitution *)
      let*^ subst = Subst.assign_pattern subst pat v in
      (* Evaluate body with new subst *)
      eval_expr ~labels subst body'
```
Crucially, the `if%sat` construct is provided directly by Soteria and does a lot of the magic. Its payload (the guard) isn't an OCaml boolean but a symbolic boolean, and it may branch if both the guard and its negation are sat. Similarly, the `let*` operator (and variants like `let*p`) compose smaller symbolic executions.

The interpretation of CN assertions is very similar. For instance, this is how "logical arguments" (assertion atoms such as `take x = R`, which is `Resource (x, R)`) are interpreted (for consumption, i.e. when removing the pre-condition of a function call from the current state):

```ocaml
let consume_logical_arg (arg, (loc, _))
  match arg with
  | Define (sym, annot) ->
      let* v = Subst.eval_annot annot in
      Subst.add sym v
  | Resource (sym, (req, _ty)) ->
      let* v = consume_resource req in
      Subst.add sym v
  | Constraint lc -> consume_logical_constraint lc
```

### Installing locally

If you want to play with the proofs to make sure that, indeed, changing values in asserts or removing assertions correctly make the proof fail, you can just:
```sh
git clone https://github.com/soteria-tools/soteria-cn.git
cd soteria-cn
opam switch create . --deps-only -y
dune build @all
dune exec -- soteria-cn verify test/verif.t/lists.c
# See how cn does
cn verify test/verif.t/lists.c
```

Other useful flags:
- `--stats stdout` show a bunch of statistics about the execution, which can easily be extended programmatically
- `--dump-smt file.smt2` dumps all queries sent to z3
- `-f fn_name` verifies only function `fn_name`, and `-f f1 -f f2` verifies both `f1` and `f2`..


### Limitations and Questions

I've identified a list of "limitations" of the Core intermediate language and of the CN assertion language in the context of performance. I also have a bunch of questions, with the most pressing one: is there a model of malloc/free in CN? The tutorial uses "unsound" specifications for allocation, and I couldn't fine the specs.

## License

Licensed under the Apache License, Version 2.0; see [LICENSE](LICENSE).

Some files are included under different licenses; see [THIRD_PARTY](THIRD_PARTY)
for details. In particular, the example C files under `test/verif.t/` are
extracted from the CN tutorial and are licensed under the CN (Cerberus) license.
