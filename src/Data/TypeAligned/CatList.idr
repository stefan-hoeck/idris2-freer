||| Type aligned catenable list with O(1) cons, snoc and concatenation
||| operations and amortized O(1) uncons operations.
|||
||| All recursive functions in this module are tail recursive
||| and hence stack safe for backends with tail-call optimization.
module Data.TypeAligned.CatList

import Data.TypeAligned.List
import Data.TypeAligned.Ops
import Data.TypeAligned.Queue
import Data.TypeAligned.Uncons
import Data.TypeAligned.Unsnoc

%default total

||| Type aligned catenable list with O(1) cons, snoc and concatenation
||| operations and amortized O(1) uncons operations.
|||
||| @ arr  the arrow (function) type stored in the list
||| @ a    the computation's input type
||| @ b    the computation's output type
public export
data TCatList : (arr : Type -> Type -> Type) -> (a,b : Type) -> Type where
  CatNil  : TCatList arr a a
  CatCons : arr a b -> TCatQueue (TCatList arr) b c -> TCatList arr a c

||| The empty list. O(1)
public export
empty : TCatList arr a a
empty = CatNil

||| Wraps a single arrow type in a type aligned list. O(1).
public export
singleton : arr a b -> TCatList arr a b
singleton v = CatCons v empty

||| Concatenation of two type aligned lists. O(1)
public export
(++) : TCatList arr a b -> TCatList arr b c -> TCatList arr a c
CatNil        ++ x      = x
x             ++ CatNil = x
(CatCons h t) ++ x      =  CatCons h (snoc t x)

||| Prepends a single arrow to a type aligned list. O(1).
public export
cons : arr a b -> TCatList arr b c -> TCatList arr a c
cons f l = singleton f ++ l

||| Appends a single arrow to a type aligned list. O(1).
public export
snoc : TCatList arr a b -> arr b c -> TCatList arr a c
snoc l f = l ++ singleton f

||| Tries to split a type aligned list into its head and tail.
|||
||| Amortized O(1): A single `uncons` operation might
||| take `n` steps.
public export
uncons : TCatList arr a b -> Uncons TCatList arr a b
uncons CatNil = Empty
uncons (CatCons h t) = h :| go (uncons t)
  where go : Uncons TCatQueue (TCatList arr) x y -> TCatList arr x y
        go Empty              = CatNil
        go v@(CatNil    :| w) = go (assert_smaller v $ uncons w)
        go (CatCons z v :| w) = CatCons z (v ++ w)

||| Applies an arrow morphism to change the arrow type
||| of a type aligned list. O(n).
public export
mapK : (forall u,v . r1 u v -> r2 u v) -> TCatList r1 a b -> TCatList r2 a b
mapK f CatNil        = CatNil
mapK f (CatCons x y) = assert_total $ CatCons (f x) $ mapK (mapK f) y
