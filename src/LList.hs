{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--no-adt"      @-}
module LList where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding(not)

-- lazy lists (possibly infinite)
data LList a = a :| (LList a) | Nil
infixr 5 :|
{-@ infix :| @-}

{-@ reflect append  @-}
Nil `append` ys         = ys
(x :| xs) `append` ys = x :| (xs `append` ys)

{-@ appendIsAssociative :: xs:_ -> ys:_ -> zs:_
     -> {append (append xs ys) zs = append xs (append ys zs)}  @-}
appendIsAssociative :: Eq a => LList a -> LList a -> LList a -> Proof
-- appendIsAssociative Nil ys zs
--   =   (Nil `append` ys) `append` zs
--   === ys `append` zs
--   === Nil `append` (ys `append` zs)
--   *** QED
--
-- appendIsAssociative xxs@(x :| xs) ys zs
--   =   (xxs `append` ys) `append` zs
--   === x :| (xs `append` ys) `append` zs
--     ? appendIsAssociative xs ys zs
--   === xxs `append` (ys `append` zs)
--   *** QED

appendIsAssociative xs ys zs
  = dAxiom_eq (append (append xs ys) zs)
              (append xs (append ys  zs))
              (\k -> _appendIsAssociativeK k xs ys zs)


{-@ reflect isInfiniteLList @-}
isInfiniteLList :: LList a -> Bool
isInfiniteLList Nil         = False
isInfiniteLList (_ :| xs) = isInfiniteLList xs

{-@ reflect isFiniteLList @-}
isFiniteLList :: LList a -> Bool
isFiniteLList = not . isInfiniteLList


---------------------------------------------------------
-- eqK properties for LLists.

{-@ type Nat = {v:Int | v >= 0}@-}


{-@ assume dAxiom_eq :: xs:_ -> ys:_ -> (k:Nat -> {eqK k xs ys})
                     -> {xs = ys} @-}
dAxiom_eq :: Eq a => LList a -> LList a -> (Int -> Proof) -> Proof
dAxiom_eq _ _ _ = ()

{-@ reflect eqK @-}
{-@ eqK :: k: Nat -> _ -> _ -> _ @-}
eqK :: (Eq a) => Int -> LList a -> LList a -> Bool
eqK 0 _ _ = True
eqK k Nil Nil = True
eqK k (a :| as) (b :| bs) = a == b && eqK (k-1) as bs
eqK k Nil (_ :| _) = False
eqK k (_ :| _) Nil = False

{-@ lemmaEqKReflexive :: k:Nat -> xs:_ -> {eqK k xs xs } @-}
lemmaEqKReflexive :: (Eq a) => Int -> LList a -> Proof
lemmaEqKReflexive 0 xs     = eqK 0 xs xs *** QED
lemmaEqKReflexive k xs@Nil = eqK k xs xs *** QED
lemmaEqKReflexive k xxs@(x :| xs)
  =   eqK k xxs xxs
  === ((x == x) && eqK (k-1) xs xs) ? lemmaEqKReflexive (k-1) xs
  *** QED

{-@ lemmaEqKCommutative :: k:Nat -> xs:_ -> ys:_
                        -> {eqK k xs ys = eqK k ys xs }
@-}
lemmaEqKCommutative :: (Eq a) => Int -> LList a -> LList a -> Proof
lemmaEqKCommutative 0 xs ys
  =   eqK 0 xs ys
  === True
  === eqK 0 ys xs
  *** QED
lemmaEqKCommutative k xs@Nil ys@Nil
  =   eqK k xs ys
  === eqK k ys xs
  *** QED
lemmaEqKCommutative k xxs@(x :| xs) yys@(y :| ys)
  =   eqK k xxs yys
  === ((x == y) && eqK (k-1) xs ys)
    ? lemmaEqKCommutative (k-1) xs ys
  === ((y == x) && eqK (k-1) ys xs)
  === eqK k yys xxs
  *** QED
lemmaEqKCommutative k xs ys
  =   eqK k xs ys
  === eqK k ys xs
  *** QED

{-@ lemmaEqKTransitive :: k:Nat -> xs:_
                       -> ys:{ys:_| eqK k xs ys}
                       -> zs:{zs:_| eqK k ys zs}
                       -> {eqK k xs zs}
@-}
lemmaEqKTransitive
    :: (Eq a)
    => Int
    -> LList a
    -> LList a
    -> LList a
    -> Proof
lemmaEqKTransitive 0 xs ys zs
  =   eqK 0 xs zs
  === True
  *** QED
lemmaEqKTransitive k xs@Nil ys@Nil zs@Nil
  =   eqK k xs zs
  === True
  *** QED
lemmaEqKTransitive k xxs@(x :| xs) yys@(y :| ys) zzs@(z :| zs)
  =   (eqK k xxs yys && eqK k yys zzs)
  === ((x == y) && eqK (k-1) xs ys && (y==z) && eqK (k-1) ys zs)
    ? lemmaEqKTransitive (k-1) xs ys zs
  === ((x == z) && eqK (k-1) xs zs)
  === eqK k xxs zzs
  *** QED
lemmaEqKTransitive k xs ys zs = (eqK k xs ys && eqK k ys zs) *** QED


---------------------------------------------------------
-- coinductive to inductive proofs.

{-@ _appendIsAssociativeK :: k: Nat -> xs:_ -> ys:_ -> zs:_
     -> {eqK k (append (append xs ys) zs)
               (append xs (append ys zs))}
@-}
_appendIsAssociativeK
    :: Eq a
    => Int
    -> LList a
    -> LList a
    -> LList a
    -> Proof
_appendIsAssociativeK 0 xs ys zs
  =   eqK 0 ((xs `append` ys) `append` zs)
             (xs `append` (ys `append` zs))
  *** QED
_appendIsAssociativeK k Nil ys zs
  =   eqK k ((Nil `append` ys) `append` zs)
             (Nil `append` (ys `append` zs))
  === eqK k (ys `append` zs) (Nil `append` (ys `append` zs))
  === eqK k (ys `append` zs) (ys `append` zs)
    ? lemmaEqKReflexive k (ys `append` zs)
  *** QED

_appendIsAssociativeK k xxs@(x :| xs) ys zs
  =   eqK k ((xxs `append` ys) `append` zs)
             (xxs `append` (ys `append` zs))
  === eqK k ((x :| xs `append` ys) `append` zs)
            (x :| xs `append` (ys `append` zs))
  === eqK k (x :| xs `append` ys `append` zs)
            (x :| xs `append` (ys `append` zs))
  -- Mind that the rhs must also advance so that
  --    a is :| available at both sides and eqK can be applied.
  -- The line below is automatically derived.
  -- === (x == x && eqK (k-1) (xs `append`  ys `append` zs)
  --                          (xs `append` (ys `append` zs)))
    ? _appendIsAssociativeK (k-1) xs ys zs
  *** QED

{-@ reflect _isInfiniteK @-}
{-@ _isInfiniteK :: Nat -> _ -> _ @-}
_isInfiniteK :: Int -> LList a -> Bool
_isInfiniteK 0 _           = True
_isInfiniteK _ Nil         = False
_isInfiniteK k (_ :| xs) = _isInfiniteK (k-1) xs
---------------------------------------------------------
{-@ reflect not @-}
not :: Bool -> Bool
not False = True
not True  = False
