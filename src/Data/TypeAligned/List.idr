||| Type aligned List and SnocList.
|||
||| All recursive functions in this module are tail recursive
||| and hence stack safe for backends with tail-call optimization.
module Data.TypeAligned.List

import Data.TypeAligned.Ops
import Data.TypeAligned.Uncons
import Data.TypeAligned.Unsnoc

%default total

||| Type aligned linked list.
|||
||| This is used to store a type aligned sequence of
||| computations in a linear data structure with O(1)
||| cons and uncons operations.
|||
||| @ arr  the arrow (function) type stored in the list
||| @ a    the computation's input type
||| @ b    the computation's output type
public export
data TList : (arr : Type -> Type -> Type) -> (a,b : Type) -> Type where
  Nil  : TList arr a a
  (::) : (h : arr a b) -> (t : TList arr b c) -> TList arr a c

||| Type aligned SnocList.
|||
||| This is used to store a type aligned sequence of
||| computations in a linear data structure with O(1)
||| snoc and unsnoc operations.
|||
||| Unlike homogeneous linked lists, we can't just reverse
||| a type aligned lists as the types would no longer align,
||| so we need `TSnocList` as a reversed view of a `TList`
||| and vice verca.
|||
||| @ arr  the arrow (function) type stored in the list
||| @ a    the computation's input type
||| @ b    the computation's output type
public export
data TSnocList : (arr : Type -> Type -> Type) -> (a,b : Type) -> Type where
  Lin  : TSnocList arr a a
  (:<) : (init : TSnocList arr a b) -> (last : arr b c) -> TSnocList arr a c

||| Tail recursive appending of a type aligned list to a snoc list.
||| O(n) w.r.t. to the second list's length.
public export
(<><) : TSnocList arr a b -> TList arr b c -> TSnocList arr a c
sx <>< []       = sx
sx <>< (h :: t) = sx :< h <>< t

||| Tail recursive prepending of a type aligned snoc list a list.
||| O(m) w.r.t. to the snoc list's length.
public export
(<>>) : TSnocList arr a b -> TList arr b c -> TList arr a c
[<]            <>> l = l
(init :< last) <>> l = init <>> last :: l

||| Alias for `(Lin <><)`.
public export %inline
toSnocList : TList arr a b -> TSnocList arr a b
toSnocList = (Lin <><)

||| Alias for `(<>> Nil)`.
public export %inline
toList : TSnocList arr a b -> TList arr a b
toList = (<>> Nil)

namespace TList
  ||| Wraps a single arrow type in a type aligned list. O(1).
  public export %inline
  singleton : arr a b -> TList arr a b
  singleton f = [f]

  ||| Tries to split a type aligned list into its head and tail. O(1).
  public export
  uncons : TList arr a b -> Uncons TList arr a b
  uncons []       = Empty
  uncons (h :: t) = h :| t

  ||| Tries to split a type aligned list into its initial part and
  ||| last element. O(n).
  public export
  unsnoc : TList arr a b -> Unsnoc TList arr a b
  unsnoc xs = case toSnocList xs of
    Lin    => Empty
    i :< l => toList i :|< l

  ||| Concatenation of two type aligned lists.
  ||| O(m) w.r.t. the first list.
  public export
  (++) : TList arr a b -> TList arr b c -> TList arr a c
  xs ++ ys = toSnocList xs <>> ys

  ||| Appends a single arrow to a type aligned list. O(n).
  public export
  snoc : TList arr a b -> arr b c -> TList arr a c
  snoc xs f = xs ++ [f]

  ||| Applies an arrow morphism to change the arrow type
  ||| of a type aligned list.
  public export
  mapK : (forall u,v . r1 u v -> r2 u v) -> TList r1 a b -> TList r2 a b
  mapK f = go Lin
    where go : TSnocList r2 x y -> TList r1 y z -> TList r2 x z
          go sl []       = toList sl
          go sl (h :: t) = go (sl :< f h) t

namespace TSnocList
  ||| Wraps a single arrow type in a type aligned SnocList. O(1).
  public export %inline
  singleton : arr a b -> TSnocList arr a b
  singleton f = Lin :< f

  ||| Tries to split a type aligned SnocList into its head and tail. O(n).
  public export
  uncons : TSnocList arr a b -> Uncons TSnocList arr a b
  uncons sx = case uncons (toList sx) of
    Empty  => Empty
    h :| t => h :| toSnocList t


  ||| Tries to split a type aligned SnocList into its initial part and
  ||| last element. O(1).
  public export
  unsnoc : TSnocList arr a b -> Unsnoc TSnocList arr a b
  unsnoc [<]            = Empty
  unsnoc (init :< last) = init :|< last

  ||| Applies an arrow morphism to change the arrow type
  ||| of a type aligned SnocList.
  public export
  mapK : (forall u,v . r1 u v -> r2 u v) -> TSnocList r1 a b -> TSnocList r2 a b
  mapK f = go Nil
    where go : TList r2 y z -> TSnocList r1 x y -> TSnocList r2 x z
          go l [<]            = toSnocList l
          go l (init :< last) = go (f last :: l) init

  ||| Concatenation of two type aligned SnocLists.
  ||| O(n) w.r.t. the second list.
  public export
  (++) : TSnocList arr a b -> TSnocList arr b c -> TSnocList arr a c
  sx ++ sy = sx <>< toList sy

  ||| Prepends a single arrow to a type aligned list. O(n).
  public export
  cons : arr a b -> TSnocList arr b c -> TSnocList arr a c
  cons f sx = [<f] ++ sx
