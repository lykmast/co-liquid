{-@ LIQUID "--reflection"   @-}
{-@ LIQUID "--no-adt"       @-}
{-@ LIQUID "--higherorder" @-}

module Paulson where

-- The following come from Section 8 of
-- "Mechanizing Coinduction and Corecursion in Higher-order Logic"
-- by Lawrence C. Paulson, 1996.
-- They are also referenced in "Co-induction Simply".
import LList
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect lmap @-}
lmap :: (a -> b) -> LList a -> LList b
lmap _ Nil = Nil
lmap f (Cons x xs) = f x `Cons` lmap f xs

{-@ theoremLmapAfter :: f:_
                           -> g:_
                           -> xs:LList a
                           -> {lmap (f . g) xs = lmap f (lmap g xs)}
@-}
theoremLmapAfter :: (b -> c) -> (a -> b) -> LList a -> Proof
theoremLmapAfter f g Nil
  =   lmap (f . g) Nil
  === Nil
  === lmap f (lmap g Nil)
  *** QED
theoremLmapAfter f g xxs@(Cons x xs)
  =   lmap (f.g) xxs
  === (f.g) x `Cons` lmap (f.g) xs
    ? theoremLmapAfter f g xs
  === f (g x) `Cons` lmap f (lmap g xs)
  === lmap f (g x `Cons` lmap g xs)
  === lmap f (lmap g xxs)
  *** QED

{-@ reflect iterates @-}
{-@ lazy iterates @-}
iterates :: (a -> a) -> a -> LList a
iterates f m = Cons m (iterates f (f m))

{-@ lazy theoremLmapIterates @-}
{-@ theoremLmapIterates :: f:_ -> m:_ -> {lmap f (iterates f m) = iterates f (f m)} @-}
theoremLmapIterates :: (a -> a) -> a -> Proof
theoremLmapIterates f m
  =   lmap f (iterates f m)
  === lmap f (m `Cons` iterates f (f m))
  === f m `Cons` lmap f (iterates f (f m))
    ? theoremLmapIterates f (f m)
  === f m `Cons` iterates f (f (f m))
  === iterates f (f m)
  *** QED

{-@ theoremLmapIterates' :: f:_ -> m:_ -> {iterates f m = Cons m (lmap f (iterates f m))} @-}
theoremLmapIterates' :: (a -> a) -> a -> Proof
theoremLmapIterates' f m = iterates f m ? theoremLmapIterates f m *** QED

{-@ theoremLmapLinear :: f:_ -> xs:_ -> ys:{ys:_| ys = xs} -> {lmap f xs = lmap f ys} @-}
theoremLmapLinear :: (a -> a) -> LList a -> LList a -> Proof
theoremLmapLinear f xs ys = ()

{-@ theoremLmapAppend :: f:_ -> m:_ -> n:_ -> {lmap f (append m n) = append (lmap f m) (lmap f n) } @-}
theoremLmapAppend :: (a -> b) -> LList a -> LList a -> Proof
theoremLmapAppend f Nil n
  =   lmap f (append Nil n)
  === lmap f n
  === Nil `append` lmap f n
  === lmap f Nil `append` lmap f n
  *** QED
theoremLmapAppend f mms@(Cons m ms) n
  =   lmap f (append mms n)
  === lmap f (m `Cons` append ms n)
  === f m `Cons` lmap f (append ms n)
    ? theoremLmapAppend f ms n
  === f m `Cons` append (lmap f ms) (lmap f n)
  === (f m `Cons` lmap f ms) `append` lmap f n
  === lmap f mms `append` lmap f n
  *** QED

---------------------------------------------------------
-- coinductive to inductive proofs.

{-@ _theoremLmapAfterK :: k:Nat
                       -> f:_
                       -> g:_
                       -> xs:_
                       -> {eqK k (lmap (f . g) xs)
                                 (lmap f (lmap g xs))}
@-}
_theoremLmapAfterK
    :: (Eq a, Eq b, Eq c)
    => Int
    -> (b -> c)
    -> (a -> b)
    -> LList a
    -> Proof
_theoremLmapAfterK 0 f g xs
  =   eqK 0 (lmap (f.g) xs) (lmap f (lmap g xs))
  *** QED
_theoremLmapAfterK k f g xs@Nil | k > 0
  =   eqK k (lmap (f.g) xs) (lmap f (lmap g xs))
  === eqK k xs xs
  *** QED
_theoremLmapAfterK k f g xxs@(Cons x xs) | k > 0
  =   eqK k (lmap (f.g) xxs) (lmap f (lmap g xxs))
  === eqK k ((f.g) x `Cons` lmap (f.g) xs)
            (lmap f (g x `Cons` lmap g xs))
  === eqK k ((f.g) x `Cons` lmap (f.g) xs)
            (f (g x) `Cons` lmap f (lmap g xs))

  -- === ((f.g) x == f (g x) && eqK (k-1) (lmap (f.g) xs)
  --                                (lmap f (lmap g xs)))
    ? _theoremLmapAfterK (k-1) f g xs
  *** QED

{-@ _theoremLmapIteratesK :: k:Nat -> f:_ -> m:_
                          -> {eqK k (lmap f (iterates f m)) (iterates f (f m))}
@-}
_theoremLmapIteratesK :: (Eq a) => Int -> (a -> a) -> a -> Proof
_theoremLmapIteratesK 0 f m
  =   eqK 0 (lmap f (iterates f m)) (iterates f (f m))
  *** QED
_theoremLmapIteratesK k f m
  =   eqK k (lmap f (iterates f m))
            (iterates f (f m))
  === eqK k (lmap f (m `Cons` iterates f (f m)))
            (iterates f (f m))
  === eqK k (f m `Cons` lmap f (iterates f (f m)))
            (f m `Cons` iterates f (f (f m)))

  -- === (f m == f m && eqK (k-1) (lmap f (iterates f (f m)))
  --                              (iterates f (f (f m))))
    ? _theoremLmapIteratesK (k-1) f (f m)
  *** QED

{-@ _theoremLmapLinearK :: k:Nat -> f:_ -> xs:_
                        -> ys:{ys:_| eqK k xs ys}
                        -> {eqK k (lmap f xs) (lmap f ys)}
@-}
_theoremLmapLinearK
    :: Eq a
    => Int
    -> (a -> a)
    -> LList a
    -> LList a
    -> Proof
_theoremLmapLinearK 0 f xs ys
  = eqK 0 (lmap f xs) (lmap f ys) *** QED
_theoremLmapLinearK k f Nil Nil
  = eqK k (lmap f Nil) (lmap f Nil) *** QED
_theoremLmapLinearK k f xxs@(Cons x xs) yys@(Cons y ys)
  =   eqK k xxs yys
  === (x == y && eqK (k-1) xs ys)
    ? _theoremLmapLinearK (k-1) f xs ys
  === (f x == f y && eqK (k-1) (lmap f xs) (lmap f ys))
  === eqK k (f x `Cons` lmap f xs) (f y `Cons` lmap f ys)
  === eqK k (lmap f xxs) (lmap f yys)
  *** QED
_theoremLmapLinearK k f xs ys = eqK k xs ys *** QED

{-@ _theoremLmapIteratesK' :: k:Nat -> f:_ -> m:_
                           -> {eqK k (iterates f m) (Cons m (lmap f (iterates f m)))}
@-}
_theoremLmapIteratesK' :: (Eq a) => Int -> (a -> a) -> a -> Proof
_theoremLmapIteratesK' 0 f m
  =   eqK 0 (iterates f m) (Cons m (lmap f (iterates f m)))
  *** QED
_theoremLmapIteratesK' k f m
  =   eqK k (iterates f m) (m `Cons` lmap f (iterates f m))
  === eqK k (m `Cons` iterates f (f m)) (m `Cons` lmap f (iterates f m))
  === eqK (k-1) (iterates f (f m)) (lmap f (iterates f m))
    ? lemmaEqKCommutative (k-1) (iterates f (f m)) (lmap f (iterates f m))
    ? _theoremLmapIteratesK (k-1) f m
  *** QED

