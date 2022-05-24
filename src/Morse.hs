{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--short-names" @-}
module Morse where

import Prelude hiding(map, not)
import Stream
import Language.Haskell.Liquid.ProofCombinators hiding((***), QED)

-- | f morse == morse
-- This example is from `Durel and Lucanu 2009`

{-@ reflect map @-}
map :: (a -> b) -> Stream a -> Stream b
map f xs = f (hd xs) :> map f (tl xs)

{-@ reflect morse @-}
morse :: Stream Bool
morse = False :> True :> merge (tl morse) (map not (tl morse))

{-@ reflect f @-}
f :: Stream Bool -> Stream Bool
f xs = hd xs :> not (hd xs) :> f (tl xs)

{-@ reflect not @-}
not True = False
not False = True

-- | Note that `theoremFMorse` does not use coinduction (no self call)
-- so there is no need to use `bisim`.
{-@ theoremFMorse :: {f morse = morse} @-}
theoremFMorse
  =   f morse
  === hd morse :> not (hd morse) :> f (tl morse)
    ? theoremFMerge (tl morse)
  === False :> True :> merge (tl morse) (map not (tl morse))
  === morse
  *** QED

{-@ theoremFMerge :: xs:_ -> {f xs = merge xs (map not xs)} @-}
theoremFMerge :: Stream Bool -> Proof
theoremFMerge xs =
  dAxiom_eq (f xs) (merge xs (map not xs)) (\k -> theoremFMergeK k xs)

{-@ theoremFMergeK :: k:Nat -> xs:_
                   -> {eqK k (f xs) (merge xs (map not xs))}
@-}
theoremFMergeK :: Int -> Stream Bool -> Proof
theoremFMergeK 0 xs = eqK 0 (f xs) (merge xs (map not xs)) *** QED
theoremFMergeK 1 xxs@(x :> xs)
  =   f xxs
  === x :> not x :> f xs
    ? (eqK 0 (not x :> f xs) (not x :> merge xs (map not xs)) *** QED)
  =#= 1 #
      x :> not x :> merge xs (map not xs)
  === x :> merge (not x :> map not xs) xs
  === merge xxs (map not xxs)
  *** QED
theoremFMergeK k xxs@(x :> xs)
  =   f xxs
  === x :> (
               not x :> f xs
             ? theoremFMergeK (k-2) xs
           =#= k-1 #
               not x :> merge xs (map not xs)
           )
  =#= k #
      x :> not x :> merge xs (map not xs)
  === x :> merge (not x :> map not xs) xs
  === merge xxs (map not xxs)
  *** QED


{-@ theoremNotF :: xs:_ -> {map not (f xs) = f (map not xs)} @-}
theoremNotF :: Stream Bool -> Proof
theoremNotF xs =
  dAxiom_eq (map not (f xs)) (f (map not xs)) (\k -> theoremNotFK k xs)

{-@ theoremNotFK :: k:Nat -> xs:_ -> {eqK k (map not (f xs))
                                            (f (map not xs))}
@-}
theoremNotFK :: Int -> Stream Bool -> Proof
theoremNotFK 0 xs = eqK 0 (map not (f xs)) (f (map not xs)) *** QED
theoremNotFK 1 xxs@(x :> xs)
  =   map not (f xxs)
  === map not (x :> not x :> f xs)
  === not x :> map not (not x :> f xs)
    ? (eqK 0 (map not (not x :> f xs))
             (not (not x) :> f (map not xs))
       *** QED
      )
  =#= 1 #
      not x :> not (not x) :> f (map not xs)
  === f (not x :> map not xs)
  === f (map not xxs)
  *** QED
theoremNotFK k xxs@(x :> xs) | k > 1
  =   map not (f xxs)
  === map not (x :> not x :> f xs)
  === not x :> map not (not x :> f xs)
  === not x :> (   not (not x) :> map not (f xs)
               ?   theoremNotFK (k-2) xs
               =#= k-1 #
                    not (not x) :> f (map not xs)
               )
  =#= k #
      not x :> not (not x) :> f (map not xs)
  === f (not x :> map not xs)
  === f (map not xxs)
  *** QED
