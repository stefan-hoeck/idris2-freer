module Control.Monad.Free

import Control.MonadRec
import Data.Fuel
import Data.TypeAligned

%default total

||| The identity function specialized to `Type`.
public export
I : Type -> Type
I t = t

mutual
  ||| A stack safe free monad implementation
  ||| storing sequences of bind operations in
  ||| an efficient type aligned catenable list.
  public export
  record Free (f : Type -> Type) (a : Type) where
    constructor MkFree
    view : FreeView f t
    arrs : Arrs f t a

  ||| A *view* on a free monad over functor `f`, describing
  ||| it either as a pure value, or a lifted value of
  ||| type `f a` followed by a bind operation.
  public export
  data FreeView : (f : Type -> Type) -> (a : Type) -> Type where
    Pure : (val : a) -> FreeView f a
    Bind : (f b) -> (b -> Free f a) -> FreeView f a

  ||| A type aligned sequence of bind operations
  ||| over `Free f`.
  public export
  0 Arrs : (f : Type -> Type) -> (a,b : Type) -> Type
  Arrs f = TCatList (\x,y => x -> Free f y)

||| Converts a view to the corresponding free monad. O(1).
export %inline
fromView : FreeView f a -> Free f a
fromView f = MkFree f empty

concatF : Free f a -> Arrs f a b -> Free f b
concatF (MkFree v r) l = MkFree v (r ++ l)

||| Converts a free monad to a view representing it.
||| Amortized O(1).
export
toView : Free f a -> FreeView f a
toView (MkFree v s) = case v of
  Pure val => case uncons s of
    Empty    => Pure val
    (h :| t) => assert_total $ toView (concatF (h val) t)

  Bind x k => Bind x (\va => concatF (k va) s)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

bind : Free f a -> (a -> Free f b) -> Free f b
bind (MkFree v r) g = MkFree v $ snoc r g

public export
Functor (Free f) where
  map g fr = bind fr (fromView . Pure . g)

public export
Applicative (Free f) where
  pure = fromView . Pure
  f <*> v = bind f (\f => map (f $) v)

public export %inline
Monad (Free f) where
  (>>=) = bind

public export
MonadRec (Free f) where
  tailRecM seed vst (Access rec) step = do
    Cont s2 prf vst2 <- step seed vst
      | Done v => pure v
    tailRecM s2 vst2 (rec s2 prf) step

||| Lift an arbitrary functor into a free monad.
export
lift : f a -> Free f a
lift v = fromView (Bind v pure)

export
HasIO m => HasIO (Free m) where
  liftIO = lift . liftIO

--------------------------------------------------------------------------------
--          Running Computations
--------------------------------------------------------------------------------

export
wrap : f (Free f a) -> Free f a
wrap x = fromView (Bind x id)

export
substFree : (forall x . f x -> Free g x) -> Free f a -> Free g a
substFree k f = case toView f of
  Pure a   => pure a
  Bind g i => assert_total $ bind (k g) (substFree k . i)

||| Unwraps a single layer of `f`, providing the continuation.
||| Amortized O(1).
export
resume' :  (forall b. f b -> (b -> Free f a) -> r)
        -> (a -> r)
        -> Free f a
        -> r
resume' k j fr = case toView fr of
  Pure a   => j a
  Bind g i => k g i

||| Unwraps a single layer of the functor `f`.
||| Amortized O(1).
export
resume : Functor f => Free f a -> Either (f (Free f a)) a
resume fr = case toView fr of
  Pure a   => Right a
  Bind g i => Left $ map i g

||| Apply a morphism to change a free monad's functor.
export
mapK : (f : forall t . m t -> n t) -> Free m a -> Free n a
mapK f = substFree (lift . f)

||| Run a computation described as a free monad in
||| a stack safe manner.
export
foldMap : MonadRec m => (forall x . f x -> m x) -> Free f a -> m a
foldMap k fr = assert_total $ trSized forever fr $ \fu,frm => case fu of
  More x => case toView frm of
    Pure val => Done <$> pure val
    Bind g i => Cont x (reflexive {rel = LTE}) . i <$> k g
  Dry    => idris_crash "Control.Monad.Free.foldFree: ran out of fuel"

||| Run a pure computation in a stack-safe manner.
export
run : Free I a -> a
run fr = case toView fr of
  Pure a   => a
  Bind v f => run (assert_smaller fr $ f v)

export
runM : Functor m => MonadRec n =>
       (m (Free m a) -> n (Free m a)) -> Free m a -> n a
runM g free = assert_total $ trSized forever free $ \fu,fr => case fu of
  More x => case resume fr of
    Right va => pure (Done va)
    Left  ma => Cont x (reflexive {rel = LTE}) <$> g ma
  Dry    => idris_crash "Control.Monad.Free.runM: ran out of fuel"
