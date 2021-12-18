{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--no-adt"      @-}
module LList where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding(not)

-- lazy lists (possibly infinite)
data LList a = Cons a (LList a) | Nil


{-@ reflect append  @-}
Nil `append` ys         = ys
(Cons x xs) `append` ys = Cons x (xs `append` ys)

{-@ appendIsAssociative :: xs:_ -> ys:_ -> zs:_ 
     -> {append (append xs ys) zs = append xs (append ys zs)}  @-}
appendIsAssociative :: LList a -> LList a -> LList a -> Proof
appendIsAssociative Nil ys zs
  =   (Nil `append` ys) `append` zs
  === ys `append` zs
  === Nil `append` (ys `append` zs)
  *** QED

appendIsAssociative xxs@(Cons x xs) ys zs
  =   (xxs `append` ys) `append` zs
  === Cons x (xs `append` ys) `append` zs
    ? appendIsAssociative xs ys zs
  === xxs `append` (ys `append` zs)
  *** QED 


---------------------------------------------------------
-- coinductive to inductive proofs.

{-@ type Nat = {v:Int | v >= 0}@-}

{-@ reflect eqK @-}
{-@ eqK :: k: Nat -> _ -> _ -> _ @-}
eqK :: (Eq a) => Int -> LList a -> LList a -> Bool
eqK 0 _ _ = True
eqK k Nil Nil = True
eqK k (Cons a as) (Cons b bs) = a == b && eqK (k-1) as bs
eqK k Nil (Cons _ _) = False
eqK k (Cons _ _) Nil = False

{-@ lemmaSameEqK :: k:Nat -> xs:_ -> {eqK k xs xs } @-}
lemmaSameEqK :: (Eq a) => Int -> LList a -> Proof
lemmaSameEqK 0 xs     = eqK 0 xs xs *** QED 
lemmaSameEqK k xs@Nil = eqK k xs xs *** QED
lemmaSameEqK k xxs@(Cons x xs)
  =   eqK k xxs xxs
  === ((x == x) && eqK (k-1) xs xs) ? lemmaSameEqK (k-1) xs
  *** QED

    
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
    ? lemmaSameEqK k (ys `append` zs) 
  *** QED

_appendIsAssociativeK k xxs@(Cons x xs) ys zs
  =   eqK k ((xxs `append` ys) `append` zs) 
             (xxs `append` (ys `append` zs))
  === eqK k (Cons x (xs `append` ys) `append` zs)
            (Cons x xs `append` (ys `append` zs))
  === eqK k (Cons x (xs `append` ys `append` zs))
            (Cons x (xs `append` (ys `append` zs)))
    ? _appendIsAssociativeK (k-1) xs ys zs
  *** QED

---------------------------------------------------------
{-@ reflect not @-}
not :: Bool -> Bool
not False = True
not True  = False
