||| The submodules of `Data.TypeAligned` provide several
||| efficient implementations of type aligned sequences.
|||
||| Type aligned sequences can be used to hold sequences
||| of computations. The are used to store and manipulate
||| sequences of bind operations for our free monad implementation
||| thus rendering free monads stack safe and efficient even
||| in the face of large series of left-associated monadic
||| binds.
|||
||| See also [reflection without remorse](https://okmij.org/ftp/Haskell/Reflection.html).
module Data.TypeAligned

import public Data.TypeAligned.CatList
import public Data.TypeAligned.List
import public Data.TypeAligned.Ops
import public Data.TypeAligned.Queue
import public Data.TypeAligned.Uncons
import public Data.TypeAligned.Unsnoc
