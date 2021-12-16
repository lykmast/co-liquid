{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
module IStream where

import Language.Haskell.Liquid.ProofCombinators

data IStream a = ICons a (IStream a)

{-@ measure ihead @-}
ihead (ICons x _)  = x 

{-@ measure itail @-}
itail (ICons _ xs) = xs


{-@ reflect nneg @-}
nneg :: IStream Int -> Bool
nneg (ICons x xs) = x >= 0 && nneg xs

-- pointwise product of streams
{-@ reflect mult @-}
mult :: IStream Int -> IStream Int -> IStream Int
mult (ICons a as) (ICons b bs) = ICons (a * b) (mult as bs)

{-@ theoremNNegSquare :: a:IStream Int -> {nneg (mult a a)}@-}
theoremNNegSquare :: IStream Int -> ()
theoremNNegSquare (ICons a as)
  =   nneg (mult (ICons a as) (ICons a as))
  === nneg (ICons (a * a) (mult as as))
  === (a * a >= 0 && nneg (mult as as))
    ? theoremNNegSquare as
  *** QED


{-@ reflect below @-}
below :: Ord a => IStream a -> IStream a -> Bool 
below (ICons x xs) (ICons y ys)
  = x <= y && ((x == y) `implies` below xs ys ) 

{-@ theoremBelowMult :: a:IStream Int -> {below a (mult a a)}@-}
theoremBelowMult :: IStream Int -> ()
theoremBelowMult (ICons a as)
  =   below (ICons a as) (mult (ICons a as) (ICons a as))
  === below (ICons a as) (ICons (a * a) (mult as as))
  === (a <= a*a && ( (a == a*a) `implies` below as (mult as as))) 
      ? theoremBelowMult as
  *** QED


{-@ reflect merge @-}
merge :: IStream a -> IStream a -> IStream a
merge (ICons x xs) ys = ICons x (merge ys xs)

{-@ reflect odds @-}
odds  :: IStream a -> IStream a
odds (ICons x xs) = ICons x (odds (itail xs))

{-@ reflect evens @-}
evens :: IStream a -> IStream a
evens = odds . itail

{-@ lemmaEvenOdd :: xs:_ -> {merge (odds xs) (evens xs) = xs} @-}
lemmaEvenOdd :: IStream a -> Proof
lemmaEvenOdd (ICons x xs) 
  =   merge (odds (ICons x xs)) (evens (ICons x xs))
  === merge (ICons x (odds (itail xs))) ((odds . itail) (ICons x xs))
  === merge (ICons x ((odds . itail) xs)) (odds xs)
  === ICons x (merge (odds xs) (evens xs))
      ? lemmaEvenOdd xs
  === ICons x xs
  *** QED

-----------------------------------------------

{-@ reflect implies @-}
{-@ implies :: p:Bool -> q:Bool -> {v:_| v <=> (p => q)} @-}
implies False _ = True
implies _ True = True
implies _ _ = False
