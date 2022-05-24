{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--short-names" @-}
module Dup where

import Prelude hiding(map, not)
import Stream
import Language.Haskell.Liquid.ProofCombinators hiding((***), QED)

{-@ reflect dup @-}
dup (x :> x' :> xs) = x == x' && dup xs

{-@ reflect dupK @-}
{-@ dupK :: Nat -> _ -> _ @-}
dupK :: Eq a => Int -> Stream a -> Bool
dupK 0 _ = True
dupK k (x :> x' :> xs) = x == x' && dupK (k-1) xs

{-@ assume dupAxiom :: xs:_ -> (k:Nat -> {dupK k xs}) -> {dup xs} @-}
dupAxiom :: Stream a -> (Int -> Proof) -> Proof
dupAxiom _ _ = ()

{-@ mergeSelfDup :: xs:_ -> {dup (merge xs xs)} @-}
mergeSelfDup xs = dupAxiom (merge xs xs) (mergeSelfDupK xs)

{-@ mergeSelfDupK :: xs:_ -> k:Nat -> {dupK k (merge xs xs)} @-}
mergeSelfDupK xs 0 = dupK 0 (merge xs xs) *** QED
mergeSelfDupK xxs@(x :> xs) k =
  dupK k (   merge xxs xxs
         === x :> merge xxs xs
         === x :> x :> merge xs xs
         )
  === dupK (k-1) (merge xs xs)
    ? mergeSelfDupK xs (k-1)
  *** QED
