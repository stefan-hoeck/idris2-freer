module Data.TypeAligned.Queue

import Data.TypeAligned.List
import Data.TypeAligned.Ops
import Data.TypeAligned.Uncons
import Data.TypeAligned.Unsnoc

%default total

public export
data TCatQueue : (arr : Type -> Type -> Type) -> (a,b : Type) -> Type where
  TCQueue :  {0 x : Type}
          -> (init : TList arr a x)
          -> (last : TSnocList arr x b)
          -> TCatQueue arr a b

public export
empty : TCatQueue arr a a
empty = TCQueue Nil Lin

public export
singleton : arr a b -> TCatQueue arr a b
singleton = TCQueue Nil . singleton

public export
cons : arr a b -> TCatQueue arr b c -> TCatQueue arr a c
cons f (TCQueue init last) = TCQueue (f :: init) last

public export
snoc : TCatQueue arr a b -> arr b c -> TCatQueue arr a c
snoc (TCQueue init last) y = TCQueue init (last :< y)

public export
mapK : (forall u,v . r1 u v -> r2 u v) -> TCatQueue r1 a b -> TCatQueue r2 a b
mapK f (TCQueue init last) = TCQueue (mapK f init) (mapK f last)

public export
(++) : TCatQueue arr a b -> TCatQueue arr b c -> TCatQueue arr a c
TCQueue i1 l1 ++ TCQueue i2 l2 = TCQueue i1 (l1 <>< i2 ++ l2)

public export
uncons : TCatQueue arr a b -> Uncons TCatQueue arr a b
uncons (TCQueue (h :: t) last) = h :| TCQueue t last
uncons (TCQueue [] last) = case toList last of
  []       => Empty
  (h :: t) => h :| TCQueue t Lin

public export
unsnoc : TCatQueue arr a b -> Unsnoc TCatQueue arr a b
unsnoc (TCQueue init (x :< last)) = TCQueue init x :|< last
unsnoc (TCQueue init [<])         = case toSnocList init of
  [<]         => Empty
  (x :< last) => TCQueue Nil x :|< last
