{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

module SizedStreamProofs where

import IStream(IStream(..), mult, evens, odds, merge, ihead, itail)
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.Prelude

data BS = Bool :&& BS | Bool :|| BS

infixr 3 :&&
infixr 2 :||


-- evalBS is not terminating/productive but we need(?) something to
-- convert a BS to a Bool in order to use in proofs. However, as we
-- see at the end, this allows as to prove {false}.
-- Can we somehow restrict evalBS in order to be sound?
{-@ reflect evalBS @-}
evalBS :: BS -> Bool
evalBS (b :&& rest) = b && evalBS rest
evalBS (b :|| rest) = b || evalBS rest


{-@ reflect belowS @-}
belowS :: Ord a => IStream a -> IStream a -> BS
belowS (ICons x xs) (ICons y ys)
  = x <= y :&& (x < y :|| belowS xs ys)

{-@ theoremBelowMult :: a:IStream Int -> {evalBS (belowS a (mult a a))}@-}
theoremBelowMult :: IStream Int -> ()
theoremBelowMult (ICons a as)
  = evalBS (
      belowS (ICons a as) (mult (ICons a as) (ICons a as))
  === belowS (ICons a as) (ICons (a * a) (mult as as))
  === (a <= a*a :&& ( a < a*a :|| belowS as (mult as as))))
  ===
    evalBS (a < a*a :|| (belowS as (mult as as) ? theoremBelowMult as))
  *** QED

{-@ reflect eqS @-}
eqS :: Eq a => IStream a -> IStream a -> BS
eqS (ICons x xs) (ICons y ys) = x == y :&& xs `eqS` ys
infix 4 `eqS`


{-@ lemmaEvenOddS :: xs:_ -> { evalBS (eqS (merge (odds xs) (evens xs))  xs)} @-}
lemmaEvenOddS :: Eq a => IStream a -> Proof
lemmaEvenOddS xxs@(ICons x xs)
  = evalBS (
      merge (odds xxs) (evens xxs)                         `eqS` xxs
  === merge (odds xxs) (evens xxs)                            `eqS` xxs
  === merge (ICons x (odds (itail xs))) ((odds . itail) xxs)  `eqS` xxs
  === merge (ICons x ((odds . itail) xs)) (evens xxs)         `eqS` xxs
  === ICons x (merge (odds xs) (evens xs))                    `eqS` xxs
  === (x == x :&& merge (odds xs) (evens xs)                  `eqS` xs)
  === (True :&& (merge (odds xs) (evens xs)                   `eqS` xs

  -- the recursive call is guarded by :&& (a coinductive constructor)
    ? lemmaEvenOddS xs)))
  *** QED


-- {evalBS (eqS xs ys) ==> evalBS (eqS ys xs)} cannot be proven safely.
-- In order to prove we need to apply evalBS and then recurse unguarded
-- by :&&.
{-@ assume eqSymmetric :: xs:_
                -> {ys:_| evalBS (eqS xs ys)}
                -> { evalBS (eqS ys xs)}
@-}
eqSymmetric :: Eq a => IStream a -> IStream a -> Proof
eqSymmetric _ _ = ()

{-@ eqReflexive :: xs:_ -> {evalBS (eqS xs xs)} @-}
eqReflexive :: Eq a => IStream a -> Proof
eqReflexive xxs@(ICons x xs)
  = evalBS (
      eqS xxs xxs
  === (x == x :&& (eqS xs xs ? eqReflexive xs)))
  *** QED

-- Transitivity (like symmetry) cannot be safely proven.
{-@ assume eqTransitive :: xs:_
                   -> {ys:_| evalBS (eqS xs ys)}
                   -> {zs:_| evalBS (eqS ys zs)}
                   -> {evalBS (eqS xs zs)}
@-}
eqTransitive :: Eq a => IStream a -> IStream a -> IStream a -> Proof
eqTransitive _ _ _ = ()

-- Unfortunately using this implementation we can prove {false}
-- while following productivity rules (recursing inside constructor).
{-@ reflect falsesOr @-}
falsesOr = False :|| falsesOr

{-@ lemmaFalse :: _ -> {false} @-}
lemmaFalse (ICons x xs)
  =   evalBS falsesOr
  === evalBS (False :|| (falsesOr ? lemmaFalse xs))
  *** QED

