# idris2-freer : An efficient, stack-safe implementation of freer monads

This library provides a stack-safe implementation of a *freer* monad,
implemented on to of an efficient type aligned sequence of
monadic bind operations.
It is based on [reflection without remorse](https://okmij.org/ftp/Haskell/Reflection.html),
and was inspired by the [purescript-free](https://github.com/purescript/purescript-free)
library.

## Prerequisites

While this library's implementation of a free monad allows
us to *build* arbitrary monadic computations in a stack
safe manner, we also need the ability to *run* them in
such a way. For this, we need a base monad with an
implementation of `MonadRec` from the
[tailrec](https://github.com/stefan-hoeck/idris2-tailrec)
library, which is based on the article
[Stack Safety for Free](functorial.com/stack-safety-for-free/index.pdf)
and adapted to a language with a totality checker.

The latest commit is daily tested to build against the current
HEAD of the Idris compiler. Since Idris2 releases are happening
rather infrequently at the moment, it is suggested to use
a package manager like [pack](https://github.com/stefan-hoeck/idris2-pack)
to install and maintain matching versions of the Idris compiler
and this library. Pack will also automatically install all
required dependencies.
