{-@ LIQUID "--reflection"   @-}
{-@ LIQUID "--no-adt"       @-}
{-@ LIQUID "--higherorder" @-}

module Paulson where

-- The following come from Section 8 of
-- "Mechanizing Coinduction and Corecursion in Higher-order Logic"
-- by Lawrence C. Paulson, 1996.
-- They are also referenced in "Co-induction Simply".
import LList
import Language.Haskell.Liquid.ProofCombinators hiding (QED, (***))

{-@ reflect lmap @-}
lmap :: (a -> b) -> LList a -> LList b
lmap _ Nil = Nil
lmap f (x :| xs) = f x :| lmap f xs

{-@ theoremLmapAfter :: f:_
                     -> g:_
                     -> xs:LList a
                     -> {lmap (f . g) xs = lmap f (lmap g xs)}
@-}
theoremLmapAfter :: (Eq a, Eq b, Eq c)
                 => (b -> c) -> (a -> b)
                 -> LList a -> Proof
-- theoremLmapAfter f g Nil
--   =   lmap (f . g) Nil
--   === Nil
--   === lmap f (lmap g Nil)
--   *** QED
-- theoremLmapAfter f g xxs@(x :| xs)
--   =   lmap (f.g) xxs
--   === (f.g) x :| lmap (f.g) xs
--     ? theoremLmapAfter f g xs
--   === f (g x) :| lmap f (lmap g xs)
--   === lmap f (g x :| lmap g xs)
--   === lmap f (lmap g xxs)
--   *** QED

theoremLmapAfter f g xs =
  dAxiom_eq (lmap (f . g) xs) (lmap f (lmap g xs))
            (\k -> _theoremLmapAfterK k f g xs)


{-@ reflect iterates @-}
{-@ lazy iterates @-}
iterates :: (a -> a) -> a -> LList a
iterates f m = m :| iterates f (f m)


{-@ theoremLmapIterates :: f:_ -> m:_ -> {lmap f (iterates f m) = iterates f (f m)} @-}
theoremLmapIterates :: Eq a => (a -> a) -> a -> Proof
-- theoremLmapIterates f m
--   =   lmap f (iterates f m)
--   === lmap f (m :| iterates f (f m))
--   === f m :| lmap f (iterates f (f m))
--     ? theoremLmapIterates f (f m)
--   === f m :| iterates f (f (f m))
--   === iterates f (f m)
--   *** QED

theoremLmapIterates f m =
  dAxiom_eq (lmap f (iterates f m)) (iterates f (f m))
            (\k -> _theoremLmapIteratesK k f m)

{-@ infix :| @-}
{-@ theoremLmapIterates' :: f:_ -> m:_ -> {iterates f m = m :| lmap f (iterates f m)} @-}
theoremLmapIterates' :: Eq a => (a -> a) -> a -> Proof
theoremLmapIterates' f m = iterates f m ? theoremLmapIterates f m *** QED

{-@ theoremLmapLinear :: f:_ -> xs:_ -> ys:{ys:_| ys = xs} -> {lmap f xs = lmap f ys} @-}
theoremLmapLinear :: (a -> a) -> LList a -> LList a -> Proof
theoremLmapLinear f xs ys = ()

{-@ theoremLmapAppend :: f:_ -> m:_ -> n:_ -> {lmap f (append m n) = append (lmap f m) (lmap f n) } @-}
theoremLmapAppend :: Eq b => (a -> b) -> LList a -> LList a -> Proof
-- theoremLmapAppend f Nil n
--   =   lmap f (append Nil n)
--   === lmap f n
--   === Nil `append` lmap f n
--   === lmap f Nil `append` lmap f n
--   *** QED
-- theoremLmapAppend f mms@(m :| ms) n
--   =   lmap f (append mms n)
--   === lmap f (m :| append ms n)
--   === f m :| lmap f (append ms n)
--     ? theoremLmapAppend f ms n
--   === f m :| append (lmap f ms) (lmap f n)
--   === (f m :| lmap f ms) `append` lmap f n
--   === lmap f mms `append` lmap f n
--   *** QED

theoremLmapAppend f m n
  = dAxiom_eq (lmap f (append m n)) (append (lmap f m) (lmap f n))
              (\k -> _theoremLmapAppendK k f m n)



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
_theoremLmapAfterK k f g xxs@(x :| xs) | k > 0
  =   lmap (f.g) xxs
  === (f.g) x :| lmap (f.g) xs
  === (f.g) x :| lmap (f.g) xs
    ? _theoremLmapAfterK (k-1) f g xs
  =#= k #
      f (g x) :| lmap f (lmap g xs)
  === lmap f (g x :| lmap g xs)
  === lmap f (lmap g xxs)
  *** QED

{-@ _theoremLmapIteratesK :: k:Nat -> f:_ -> m:_
                          -> {eqK k (lmap f (iterates f m)) (iterates f (f m))}
@-}
_theoremLmapIteratesK :: (Eq a) => Int -> (a -> a) -> a -> Proof
_theoremLmapIteratesK 0 f m
  =   eqK 0 (lmap f (iterates f m)) (iterates f (f m))
  *** QED
_theoremLmapIteratesK k f m
  =   lmap f (iterates f m)
  === lmap f (m :| iterates f (f m))
  === f m :| lmap f (iterates f (f m))
    ? _theoremLmapIteratesK (k-1) f (f m)
  =#= k #
      f m :| iterates f (f (f m))
  === iterates f (f m)
  *** QED

{-@ _theoremLmapAppendK :: k:Nat
                        -> f:_
                        -> m:_
                        -> n:_
                        -> {eqK k (lmap f (append m n))
                                  (append (lmap f m) (lmap f n)) }
@-}
_theoremLmapAppendK
    :: Eq b
    => Int
    -> (a -> b)
    -> LList a
    -> LList a
    -> Proof
_theoremLmapAppendK 0 f m n
  =   eqK 0 (lmap f (append m n)) (lmap f m `append` lmap f n)
  *** QED
_theoremLmapAppendK k f m@Nil n
  =   eqK k (lmap f (append m n))
            (lmap f m `append` lmap f n)
  === eqK k (lmap f n) (lmap f n)
    ? lemmaEqKReflexive k (lmap f n)
  *** QED
_theoremLmapAppendK k f mms@(m :| ms) n
  =   lmap f (append mms n)
  === lmap f (m :| append ms n)
  === f m :| lmap f (append ms n)
    ? _theoremLmapAppendK (k-1) f ms n
  =#= k #
       f m :| append (lmap f ms) (lmap f n)
  === (f m :| lmap f ms) `append` lmap f n
  === lmap f mms `append` lmap f n
  *** QED

