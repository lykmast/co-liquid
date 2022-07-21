{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Paper.Section4.EqLemma where

import Prelude hiding (take, map)

import Language.Haskell.Liquid.ProofCombinators

{-@ infixr :> @-}
infixr :>
data Stream a = a :> Stream a

data Proposition a = Bisimilar Int (Stream a) (Stream a)

data Bisimilar a where
      Bisim :: Int -> a -> Stream a -> Stream a
            -> (Int -> Bisimilar a)
            -> Bisimilar a
{-@ data Bisimilar a where
          Bisim :: i:Nat -> x:a -> xs:Stream a -> ys:Stream a
                -> (j:{j:Nat | j < i} ->  Prop (Bisimilar j xs ys))
                -> Prop (Bisimilar i (x :> xs) (x :> ys)) @-}

{-@ reflect take @-}
{-@ take :: Nat -> Stream a -> [a] @-}
take :: Int -> Stream a -> [a]
take 0 _ = []
take i (x :> xs) = x:take (i-1) xs

{-@ ple eqKLemma @-}
eqKLemma :: (Eq a) => Stream a -> Stream a -> Int -> Bisimilar a -> ()
{-@ eqKLemma :: x:Stream a -> y:Stream a
                  -> i:Nat -> (Prop (Bisimilar i x y))
                  ->  {take i x = take i y} @-}
eqKLemma _x _ 0 _ = ()
eqKLemma _x _ _i (Bisim i x xs ys p)
  = eqKLemma xs ys (i-1) (p (i-1))

