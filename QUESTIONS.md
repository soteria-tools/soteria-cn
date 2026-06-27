## What is Loaded what is Obj?

I'm confused at what is Loaded and what isn't, especially in Cn annotations.
So far I treat both as more-or-less equivalent.

## Allocation

The tutorial only talked about `cn_malloc` and `cn_free`,
which have unsound specifications for malloc and free.

## Semantics of `W<ty>`

What is the return value of `W<ty>`? Is it `Loaded<ty>` or is it just garbage?
Do I need to return an appropriate value? I don't think so, so I haven't,
but this can easily be changed.

## Pack/Unpack?

I don't understand the semantics of pack and unpack. I don't understand
why I can't unpack a predicate that I have in my precondition?

For instance, in the following program:
```
/*@
predicate { u32 P, u32 Q } TakeBoth (pointer p, pointer q)
{
  if (ptr_eq(p,q)) { ... }
  else { ... }
}
@*/

void incr2(unsigned int *p, unsigned int *q)
/*@ requires take PQ = TakeBoth(p,q);
    ensures ...
@*/
{
  /*@ unpack TakeBoth(p, q); @*/ <- Why is this failing with "Cannot unpack resource?"
  ...
}
```


## What's up with the definition of predicates?

```ocaml
type t =
{ name : name;
  pointer : IT.t; (* I *)
  iargs : IT.t list (* I *)
}
```

Why is the first argument special cased? Why isn't it just this:
```ocaml
type t =
{ name : name;
  iargs : IT.t list (* I *)
}
```

-> Fix this in Usable_mucore.ml

## LogicalArgumentType vs arguments_l????

They're the same thing but duplicated?
Literally the exact same definition?