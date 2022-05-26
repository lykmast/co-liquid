{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Section4 where 

import Prelude hiding (take)

import Language.Haskell.Liquid.ProofCombinators 

{-@ infixr :> @-}
infixr :>
data Stream a = a :> Stream a

-- Sadly, infix constructor does not play well with GADTs

-- Without Guardedness we can prove false :(
data PropositionNG a = BisimilarNG (Stream a) (Stream a)


-- 
data BisimilarNG a where 
      BisimNG :: a -> Stream a -> Stream a 
            -> BisimilarNG a 
            -> BisimilarNG a 
{-@ data BisimilarNG a where 
          BisimNG :: x:a -> xs:Stream a -> ys:Stream a 
                -> Prop (BisimilarNG xs ys) 
                -> Prop (BisimilarNG (x :> xs) (x :> ys)) @-}

falseProp :: Stream a -> Stream a ->  BisimilarNG a -> ()
{-@ falseProp :: x:Stream a -> y:Stream a -> Prop (BisimilarNG x y) -> {false} @-}
falseProp _ _ (BisimNG a x y p)
  = falseProp x y p 

-- Let's Guard it! 
data Proposition a = Bisimilar Int (Stream a) (Stream a)
data Bisimilar a where 
      Bisim :: Int -> a -> Stream a -> Stream a 
            -> (Int -> Bisimilar a) 
            -> Bisimilar a 
{-@ data Bisimilar a where 
          Bisim :: i:Nat -> x:a -> xs:Stream a -> ys:Stream a 
                -> (j:{j:Nat | j < i} ->  Prop (Bisimilar j xs ys)) 
                -> Prop (Bisimilar i (x :> xs) (x :> ys)) @-}




odds :: Stream a -> Stream a
odds (x :> xs) = x :> (odds (stail xs)) 

evens :: Stream a -> Stream a
evens xs = odds (stail xs) 

merge :: Stream a -> Stream a -> Stream a 
merge (x :> xs) ys = x :> (merge ys xs)  

{-@ reflect odds  @-}
{-@ reflect evens @-}
{-@ reflect merge @-}




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

{-@ assume takeLemma :: x:Stream a -> y:Stream a -> n:Nat 
                     -> {x = y <=> take n x = take n y} @-}
takeLemma :: Stream a -> Stream a -> Int -> () 
takeLemma _ _ _ = () 


{-@ theorem :: xs:Stream a 
            -> i:Nat ->  Prop (Bisimilar i  (merge (odds xs) (evens xs)) (xs)) @-}
theorem :: (Eq a, Eq (Stream a)) => Stream a -> Int -> Bisimilar a   
theorem (x :> xs) i 
  = Bisim i x (merge (odds xs) (evens xs)) xs (theorem xs)
  ? lhs
  where lhs =  merge (odds (x :> xs)) (evens (x :> xs))
           === merge (x :> odds (stail xs)) (odds (stail (x :> xs))) 
           === x :> merge (odds (stail (x :> xs))) (odds (stail xs))
           === x :> merge (odds xs) (evens xs)
           *** QED 


{-@ ple eqKLemma @-}
eqKLemma :: (Eq (Stream a), Eq a) => Stream a -> Stream a -> Int -> Bisimilar a -> () 
{-@ eqKLemma :: x:Stream a -> y:Stream a 
                  -> i:Nat -> (Prop (Bisimilar i x y)) 
                  ->  {take i x = take i y} @-}
eqKLemma _x _ 0 _ = () 
eqKLemma _x _ _i (Bisim i x xs ys p)
  = eqKLemma xs ys (i-1) (p (i-1))


{-@ assert :: b:{Bool | b } -> {b} @-} 
assert :: Bool -> () 
assert _ = ()


approx :: (Eq (Stream a), Eq a) => Stream a -> Stream a -> Int -> Bisimilar a -> () 
{-@ approx :: x:Stream a -> y:Stream a 
                  -> i:Nat -> Prop (Bisimilar i x y) 
                  -> { x = y } @-}
approx x y i p = eqKLemma x y i p ? takeLemma x y i  