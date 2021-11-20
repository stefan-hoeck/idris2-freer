module Data.TypeAligned.Uncons

import Data.TypeAligned.Ops

%default total

||| View on the head and tail of a type aligned sequence.
|||
||| @ seq  the type aligned sequence type
||| @ arr  the arrow (function) type stored in the sequence
||| @ a    the input type
||| @ b    the output type
public export
data Uncons :  (seq : (Type -> Type -> Type) -> Type -> Type -> Type)
            -> (arr : Type -> Type -> Type)
            -> (a : Type)
            -> (b : Type)
            -> Type where
   ||| The empty case
   Empty : Uncons seq arr a a

   ||| The non-empty case
   (:|)  :  {0 x : _}
         -> (head : arr a x)
         -> (tail : seq arr x b)
         -> Uncons seq arr a b
