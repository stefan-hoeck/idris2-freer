module Data.TypeAligned.Unsnoc

import Data.TypeAligned.Ops

%default total

||| View on the initial part and last element of a type aligned sequence.
|||
||| @ seq  the type aligned sequence type
||| @ arr  the arrow (function) type stored in the sequence
||| @ a    the input type
||| @ b    the output type
public export
data Unsnoc :  (seq : (Type -> Type -> Type) -> Type -> Type -> Type)
            -> (arr : Type -> Type -> Type)
            -> (a : Type)
            -> (b : Type)
            -> Type where
   ||| The empty case
   Empty : Unsnoc seq arr a a

   ||| The non-empty case
   (:|<) :  {0 x : _}
         -> (init : seq arr a x)
         -> (last : arr x b)
         -> Unsnoc seq arr a b
