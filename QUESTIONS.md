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

## Folds?

Does CN not support folding predicates? I can't find any example in the CN codebase
or in the tutorial.