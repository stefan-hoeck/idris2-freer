module Data.TCQueue

%default total

public export
data Tree : (f : Type -> Type) -> (a, b : Type) -> Type where
  Leaf : (a -> f b) -> Tree f a b
  Node : {0 x : _} -> Tree f a x -> Tree f x b -> Tree f a b

public export
data TCQueue : (f : Type -> Type) -> (a, b : Type) -> Type where
  Empty  : TCQueue f a a
  Filled : Tree f a b -> TCQueue f a b

public export %inline
empty : TCQueue f a a
empty = Empty

public export %inline
singleton : (a -> f b) -> TCQueue f a b
singleton = Filled . Leaf

public export
cons : (a -> f x) -> TCQueue f x b -> TCQueue f a b
cons g Empty      = singleton g
cons g (Filled y) = Filled (Node (Leaf g) y)

public export
snoc : TCQueue f a x -> (x -> f b) -> TCQueue f a b
snoc Empty g      = singleton g
snoc (Filled y) g = Filled (Node y (Leaf g))

public export
(++) : TCQueue f a x -> TCQueue f x b -> TCQueue f a b
Empty    ++ w        = w
v        ++ Empty    = v
Filled v ++ Filled w = Filled (Node v w)

export infixr 5 :|

||| Left-edge deconstruction
public export
data ViewL : (f : Type -> Type) ->  (a,b : Type) -> Type where
  EmptyV : ViewL f a a
  (:|)   : {0 x : _} -> (a -> f x) -> (TCQueue f x b) -> ViewL f a b

public export
uncons : TCQueue f a b -> ViewL f a b
uncons Empty               = EmptyV
uncons (Filled $ Leaf g)   = g :| Empty
uncons (Filled $ Node v w) = go v w
  where go : Tree f a x -> Tree f x b -> ViewL f a b
        go (Leaf g) w   = g :| Filled w
        go (Node y z) w = go y (Node z w)
