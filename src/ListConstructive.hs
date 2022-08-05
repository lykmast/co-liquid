{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--reflection" @-}

{-# LANGUAGE GADTs #-}
module ListConstructive where

import Prelude hiding(map, infinite)
import Language.Haskell.Liquid.ProofCombinators

import List

{-@ infixr :| @-}
{-@ infixr . @-}

-- Coinductive predicates

data Proposition a = Bisimilar Int (List a) (List a)
                   | Infinite  Int (List a)

data Bisimilar a where
      BisimNil :: Int
               -> Bisimilar a
      Bisim :: Int -> a -> List a -> List a
            -> (Int -> Bisimilar a)
            -> Bisimilar a
{-@ data Bisimilar a where
          BisimNil :: i:Nat
                   -> Prop (Bisimilar i Nil Nil)
          Bisim :: i:Nat -> x:a -> xs:List a -> ys:List a
                -> (j:{j:Nat | j < i} ->  Prop (Bisimilar j xs ys))
                -> Prop (Bisimilar i (x :| xs) (x :| ys)) @-}


{-@
assume bisimLemma :: x:List a -> y:List a
                  -> (i:Nat -> Prop (Bisimilar i x y))
                  -> { x = y } @-}
bisimLemma :: List a -> List a -> (Int -> Bisimilar a) -> Proof
bisimLemma x y p = ()

data Infinite a where
  Inf :: Int
      -> a
      -> List a
      -> (Int -> Infinite a)
      -> Infinite a

{-@ data Infinite a where
         Inf :: i:Nat -> x:a -> xs:List a
             -> (j:{j:Nat | j < i} ->  Prop (Infinite j xs))
             -> Prop (Infinite i (x :| xs)) @-}

{-@
assume infLemma :: x:List a
                -> (i:Nat -> Prop (Infinite i x))
                -> { infinite x } @-}
infLemma :: List a -> (Int -> Infinite a) -> Proof
infLemma x p = ()

------------------------------------------
-- | Proofs
{-@ bisimRefl :: xs:_ -> i:Nat -> Prop (Bisimilar i xs xs) @-}
bisimRefl xs@Nil i = BisimNil i
bisimRefl xxs@(x:|xs) i = Bisim i x xs xs (bisimRefl xs)

{-@ mapInfiniteS :: f:_ -> {xs:_| infinite xs} -> i:Nat
                      -> Prop (Infinite i (map f xs))@-}
mapInfiniteS f xs@Nil _ =
  absurd (xs ? (infinite xs === False *** QED))
mapInfiniteS f xxs@(x :| xs) i =
  Inf i (f x) (map f xs) (mapInfiniteS f (xs ?infTail)) ? expand
  where expand =  map f xxs
              === f x :| map f xs
              *** QED
        infTail = infinite xxs
               === infinite xs
               *** QED

{-@ mapFusionS :: f:_ -> g:_ -> xs:_ -> i:Nat
                -> Prop (Bisimilar i (map f (map g xs))
                                     (map (f . g) xs)) @-}
mapFusionS f g xs@Nil i = BisimNil i ? (map f (map g Nil) === Nil *** QED)
                                     ? (map (f . g) Nil   === Nil *** QED)
mapFusionS f g xxs@(x :| xs) i =
  Bisim i ((f . g) x) (map f (map g xs)) (map (f . g) xs)
        (mapFusionS f g xs) ? expandL ? expandR
  where expandL
          =  map f (map g xxs)
         === map f (g x :| map g xs)
         === (f (g x)) :| map f (map g xs)
         *** QED
        expandR
          =  map (f . g) xxs
         === (f . g) x :| map (f . g) xs
         *** QED


-- | Original theorems.

{-@ mapInfinite :: f:_ -> {xs:_| infinite xs}
                     -> {infinite (map f xs)} @-}
mapInfinite f xs = infLemma (map f xs) (mapInfiniteS f xs)

{-@ mapFusion :: f:_ -> g:_ -> xs:_
               -> {map f (map g xs) = map (f . g) xs} @-}
mapFusion f g xs =
  bisimLemma (map f (map g xs)) (map (f . g) xs) (mapFusionS f g xs)
------------------------------------------
--
-- | Utility functions

{-@ reflect bottom @-}
{-@ lazy bottom @-}
bottom :: a
bottom = bottom

{-@ reflect absurd @-}
{-@ absurd :: {v:_|false} -> a @-}
absurd v = bottom

