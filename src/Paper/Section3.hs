{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Paper.Section4 where

import Prelude hiding (take, map)

import Language.Haskell.Liquid.ProofCombinators

{-@ infixr .  @-}
{-@ infixr :> @-}

-- | 4.1 Constructive Equality

data EqC1 a where
      EqRefl1 :: a -> Stream a -> Stream a
              -> EqC1 a
              -> EqC1 a
{-@ data EqC1 a where
          EqRefl1 :: x:a -> xs:Stream a -> ys:Stream a
                  -> Prop (EqC1 xs ys)
                  -> Prop (EqC1 (x :> xs) (x :> ys)) @-}

data Proposition a = EqC1 (Stream a) (Stream a)
                   | EqC Int (Stream a) (Stream a)


-- | The problem: no guardedness condition.

falseProp :: Stream a -> Stream a ->  EqC1 a -> ()
{-@ falseProp :: x:Stream a -> y:Stream a -> Prop (EqC1 x y) -> {false} @-}
falseProp _ _ (EqRefl1 a x y p)
  = falseProp x y p

-- | Indices to the rescue.
data EqC a where
      EqRefl :: Int -> a -> Stream a -> Stream a
             -> (Int -> EqC a)
             -> EqC a
{-@ data EqC a where
          EqRefl :: i:Nat -> x:a -> xs:Stream a -> ys:Stream a
                 -> (j:{j:Nat | j < i} ->  Prop (EqC j xs ys))
                 -> Prop (EqC i (x :> xs) (x :> ys)) @-}


{-@ ignore imposProp@-}
{-@ ple imposProp@-}
imposProp :: Int -> Stream a -> Stream a -> EqC a -> ()
{-@ imposProp :: i:Nat  -> x:Stream a -> y:Stream a
               -> Prop (EqC i x y) -> {v:() | false}  @-}
imposProp 0 _ _ _ = ()
imposProp _ _ _ (EqRefl i a x y p)
  = imposProp (i-1) x y (p (i-1))



-- | 4.2 Proof by Constructive Coinduction

{-@ mapFusionC :: f:(b -> c) -> g:(a -> b) -> xs:Stream a
                  -> i:Nat -> Prop (EqC i (smap f (smap g xs)) (smap (f . g) xs) ) @-}
mapFusionC :: (Eq c) => (b -> c) -> (a -> b) -> Stream a ->  Int -> EqC c
mapFusionC f g (x :> xs)  i
  = EqRefl i ((f . g) x) (smap f (smap g xs)) (smap (f . g) xs) (mapFusionC f g xs)
  ? (   ((f . g) x) :> (smap (f . g) xs)
    === smap (f. g) (x :> xs)
    *** QED
    )
  ? (   ((f . g) x) :> (smap f (smap g xs))
    === (f (g x)) :> (smap f (smap g xs))
    ===  smap f (g x :> smap g xs)
    ===  smap f (smap g (x :> xs))
    *** QED
    )



-- | 4.3 Did we prove Equality?

{-@ ple eqCLemma @-}
eqCLemma :: (Eq a) => Stream a -> Stream a -> Int -> EqC a -> ()
{-@ eqCLemma :: x:Stream a -> y:Stream a
                  -> i:Nat -> (Prop (EqC i x y))
                  ->  {take i x = take i y} @-}
eqCLemma _x _ 0 _ = ()
eqCLemma _x _ _i (EqRefl i x xs ys p)
  = eqCLemma xs ys (i-1) (p (i-1))

approx :: (Eq a) => Stream a -> Stream a -> (Int -> EqC a) -> ()
{-@ approx :: x:Stream a -> y:Stream a
                  -> (i:Nat -> Prop (EqC i x y))
                  -> { x = y } @-}
approx x y p = takeLemma x y (\i -> eqCLemma x y i (p i))

{-@ mapFusion :: f:(b -> c) -> g:(a -> b) -> xs:Stream a
            -> { smap f (smap g xs) == smap (f . g) xs } @-}
mapFusion :: Eq c => (b -> c) -> (a -> b) -> Stream a -> ()
mapFusion f g xs
  = approx (smap f (smap g xs)) (smap (f . g) xs) (mapFusionC f g xs)











-- | As in Section 2 without boxes or Section 3
infixr :>
data Stream a =  a :> Stream a

{-@ reflect smap @-}
smap :: (a -> b) -> Stream a -> Stream b
smap f (x :> xs) = f x :> smap f xs
{-@ measure shead @-}
{-@ measure stail @-}

shead :: Stream a -> a
stail :: Stream a -> Stream a
shead (x :> _ ) = x
stail (_ :> xs) = xs


{-@ reflect take @-}
{-@ take :: Nat -> Stream a -> [a] @-}
take :: Int -> Stream a -> [a]
take 0 _ = []
take i (x :> xs) = x:take (i-1) xs


{-@ assume takeLemma :: x:Stream a -> y:Stream a
                     -> (n:Nat -> {v:() | take n x = take n y}) -> {x = y} @-}
takeLemma :: Stream a -> Stream a -> (Int -> ()) -> ()
takeLemma _ _ _ = ()
