{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--reflection" @-}

module ListIndexed where

import Language.Haskell.Liquid.ProofCombinators hiding ((***), QED)

import Prelude hiding(map, infinite)
import List

{-@ infixr :| @-}
{-@ infixr . @-}

-- | Predicates
{-@ reflect eqK @-}
{-@ eqK :: k: Nat -> _ -> _ -> _ @-}
eqK :: (Eq a) => Int -> List a -> List a -> Bool
eqK 0 _ _  = True
eqK _ Nil Nil  = True
eqK k (a :| as) (b :| bs) = a == b && eqK (k-1) as bs
eqK _ _ _ = False

{-@ assume eqLemma :: xs:_ -> ys:_
                   -> (k:Nat -> {eqK k xs ys}) -> {xs = ys} @-}
eqLemma :: Eq a => List a -> List a -> (Int -> Proof) -> Proof
eqLemma xs ys p = ()

{-@ reflect isInfiniteK @-}
{-@ isInfiniteK :: Nat -> _ -> _ @-}
isInfiniteK :: Int -> List a -> Bool
isInfiniteK 0 _           = True
isInfiniteK _ Nil         = False
isInfiniteK k (_ :| xs)   = isInfiniteK (k-1) xs

{-@ assume infLemma :: xs:_ -> (k:Nat -> {isInfiniteK k xs})
                    -> {infinite xs} @-}
infLemma :: List a -> (Int -> Proof) -> Proof
infLemma xs p = ()
------------------------------------------
-- | Proofs

{-@ lemmaEqKReflexive :: xs:_ -> k:Nat -> {eqK k xs xs } @-}
lemmaEqKReflexive :: (Eq a) => List a -> Int -> Proof
lemmaEqKReflexive xs     0 = eqK 0 xs xs *** QED
lemmaEqKReflexive xs@Nil k = eqK k xs xs *** QED
lemmaEqKReflexive xxs@(x :| xs) k
  =   eqK k xxs xxs
  === ((x == x) && eqK (k-1) xs xs) ? lemmaEqKReflexive xs (k-1)
  *** QED

{-@ mapFusionK :: f:_ -> g:_ -> xs:_ -> k:Nat
                -> {eqK k (map (f . g) xs) (map f (map g xs))} @-}
mapFusionK :: (Eq a, Eq b, Eq c)
            => (b -> c) -> (a -> b) -> List a -> Int -> Proof
mapFusionK f g xs 0
  =   eqK 0 (map (f.g) xs) (map f (map g xs))
  *** QED
mapFusionK f g xs@Nil k | k > 0
  =   eqK k (map (f.g) xs) (map f (map g xs))
  === eqK k xs xs
  *** QED
mapFusionK f g xxs@(x :| xs) k | k > 0
  =   map (f.g) xxs
  === (f.g) x :| map (f.g) xs
  === (f.g) x :| map (f.g) xs
    ? mapFusionK f g xs (k-1)
  =#= k #
      f (g x) :| map f (map g xs)
  === map f (g x :| map g xs)
  === map f (map g xxs)
  *** QED

{-@ mapInfiniteK :: f:_ -> {xs:_ | infinite xs} -> k:Nat
                     -> {isInfiniteK k (map f xs)} @-}
mapInfiniteK :: (a -> b) -> List a -> Int -> Proof
mapInfiniteK f xs 0 = isInfiniteK 0 (map f xs) *** QED
mapInfiniteK f xs@Nil k = infinite xs *** QED
mapInfiniteK f xxs@(x :| xs) k
  =   isInfiniteK k (map f xxs)
  === isInfiniteK k (f x :| map f xs)
    ? (infinite xxs === infinite xs *** QED)
    ? mapInfiniteK f xs (k-1)
  *** QED

-- | Original theorems.
{-@ mapInfinite :: f:_ -> {xs:_| infinite xs}
                     -> {infinite (map f xs)} @-}
mapInfinite f xs = infLemma (map f xs) (mapInfiniteK f xs)

{-@ mapFusion :: f:_ -> g:_ -> xs:_
               -> {map f (map g xs) = map (f . g) xs} @-}
mapFusion f g xs =
  eqLemma (map (f . g) xs) (map f (map g xs)) (mapFusionK f g xs)
------------------------------------------------------------

infix 0 ***

data QED = QED
_ *** QED = ()

infixr 1 #
(#) = ($)

infix 2 =#=
{-@ (=#=) :: Eq a => x:ListNE a -> k:{Nat | 0 < k }
          -> y:{ListNE a | eqK (k-1) (ltail x) (ltail y)
                          && lhead x == lhead y }
          -> {v:ListNE a | eqK k x y && v == x } @-}
(=#=) :: Eq a => List a -> Int -> List a -> List a
(=#=)  xxs@(x :| xs) k yys@(y :| ys) =
  xxs ? (eqK k xxs yys === (x == y && eqK (k-1) xs ys) *** QED)
