||| Type aligned Queue with O(1) cons and snoc
||| operations and amortized O(1) uncons and unsnoc
||| operations.
|||
||| All recursive functions in this module are tail recursive
||| and hence stack safe for backends with tail-call optimization.
module Data.TypeAligned.Queue

import Data.TypeAligned.List
import Data.TypeAligned.Ops
import Data.TypeAligned.Uncons
import Data.TypeAligned.Unsnoc

%default total

||| Type aligned Queue with O(1) cons and snoc
||| operations and amortized O(1) uncons and unsnoc
||| operations.
|||
||| @ arr  the arrow (function) type stored in the list
||| @ a    the computation's input type
||| @ b    the computation's output type
public export
data TCatQueue : (arr : Type -> Type -> Type) -> (a,b : Type) -> Type where
  TCQueue :  {0 x : Type}
          -> (init : TList arr a x)
          -> (last : TSnocList arr x b)
          -> TCatQueue arr a b

||| The empty queue. O(1)
public export
empty : TCatQueue arr a a
empty = TCQueue Nil Lin

||| Wraps a single arrow type in a type aligned queue. O(1).
public export
singleton : arr a b -> TCatQueue arr a b
singleton = TCQueue Nil . singleton

||| Prepends a single arrow to a type aligned queue. O(1).
public export
cons : arr a b -> TCatQueue arr b c -> TCatQueue arr a c
cons f (TCQueue init last) = TCQueue (f :: init) last

||| Appends a single arrow to a type aligned queue. O(1).
public export
snoc : TCatQueue arr a b -> arr b c -> TCatQueue arr a c
snoc (TCQueue init last) y = TCQueue init (last :< y)

||| Applies an arrow morphism to change the arrow type
||| of a type aligned queue. O(n).
public export
mapK : (forall u,v . r1 u v -> r2 u v) -> TCatQueue r1 a b -> TCatQueue r2 a b
mapK f (TCQueue init last) = TCQueue (mapK f init) (mapK f last)

||| Concatenation of two type aligned queues.
||| O(n) w.r.t. the second queue.
public export
(++) : TCatQueue arr a b -> TCatQueue arr b c -> TCatQueue arr a c
TCQueue i1 l1 ++ TCQueue i2 l2 = TCQueue i1 (l1 <>< i2 ++ l2)

||| Tries to split a type aligned list into its head part and tail.
|||
||| Amortized O(1): A single `uncons` operation might
||| take `n` steps.
public export
uncons : TCatQueue arr a b -> Uncons TCatQueue arr a b
uncons (TCQueue (h :: t) last) = h :| TCQueue t last
uncons (TCQueue [] last) = case toList last of
  []       => Empty
  (h :: t) => h :| TCQueue t Lin

||| Tries to split a type aligned list into its initial part and
||| last element.
|||
||| Amortized O(1): A single `uncons` operation might
||| take `n` steps.
public export
unsnoc : TCatQueue arr a b -> Unsnoc TCatQueue arr a b
unsnoc (TCQueue init (x :< last)) = TCQueue init x :|< last
unsnoc (TCQueue init [<])         = case toSnocList init of
  [<]         => Empty
  (x :< last) => TCQueue Nil x :|< last
