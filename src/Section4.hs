{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Section4 where 

import Prelude hiding (take, map)

import Language.Haskell.Liquid.ProofCombinators 

{-@ infixr :> @-}
infixr :>
data Stream a = a :> Stream a

-- Sadly, infix constructor does not play well with GADTs

-- Without Guardedness we can prove false :(
data Proposition a = BisimilarNG (Stream a) (Stream a) | Bisimilar Int (Stream a) (Stream a)


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
-- data Proposition a = Bisimilar Int (Stream a) (Stream a)
data Bisimilar a where 
      Bisim :: Int -> a -> Stream a -> Stream a 
            -> (Int -> Bisimilar a) 
            -> Bisimilar a 
{-@ data Bisimilar a where 
          Bisim :: i:Nat -> x:a -> xs:Stream a -> ys:Stream a 
                -> (j:{j:Nat | j < i} ->  Prop (Bisimilar j xs ys)) 
                -> Prop (Bisimilar i (x :> xs) (x :> ys)) @-}

{- 
{-@ ple falseProp'@-}
falseProp' :: Int -> Stream a -> Stream a -> Bisimilar a -> ()
{-@ falseProp' :: i:Nat  -> x:Stream a -> y:Stream a 
               -> Prop (Bisimilar i x y) -> {v:() | false}  @-}
falseProp' 0 _ _ _ = () 
falseProp' _ _ _ (Bisim i a x y p)
  = falseProp' (i-1) x y (p (i-1)) 
-} 

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



{-@ reflect map @-}
map :: (a -> b) -> Stream a -> Stream b 
map f (x :> xs) = f x :> map f xs 
{-@ assume takeLemma :: x:Stream a -> y:Stream a 
                     -> (n:Nat -> {v:() | take n x = take n y}) -> {x = y} @-}
takeLemma :: Stream a -> Stream a -> (Int -> ()) -> ()
takeLemma _ _ _ = () 


{-@ theorem :: xs:Stream a 
            -> { merge (odds xs) (evens xs) = (xs)} @-}
theorem :: (Eq a) => Stream a -> ()   
theorem xs  
  = approx (merge (odds xs) (evens xs)) xs (theoremA xs)

{-@ infixr . @-}

{-@ stream_fusion :: xs:Stream a -> f:(a -> a) -> g:(a -> a) 
                  -> i:Nat ->  Prop (Bisimilar i (map (f . g) xs) (map f (map g xs))) @-}
stream_fusion :: (Eq a) => Stream a -> (a -> a) -> (a -> a) ->  Int -> Bisimilar a   
stream_fusion (x :> xs) f g i 
  = Bisim i ((f . g) x) (map (f . g) xs) (map f (map g xs)) (stream_fusion xs f g)
  ? (   ((f . g) x) :> (map (f . g) xs)
    === map (f. g) (x :> xs)
    *** QED 
    )
  ? (   ((f . g) x) :> (map f (map g xs))
    === (f (g x)) :> (map f (map g xs))
    ===  map f (g x :> map g xs)
    ===  map f (map g (x :> xs))
    *** QED 
    )
    -- I want (map (f . g) xs) = (map f (map g xs))


{-@ theoremA :: xs:Stream a 
            -> i:Nat ->  Prop (Bisimilar i  (merge (odds xs) (evens xs)) (xs)) @-}
theoremA :: (Eq a) => Stream a -> Int -> Bisimilar a   
theoremA (x :> xs) i 
  = Bisim i x (merge (odds xs) (evens xs)) xs (foo xs)
  ? lhs
  where lhs =  merge (odds (x :> xs)) (evens (x :> xs))
           === merge (x :> odds (stail xs)) (odds (stail (x :> xs))) 
           === x :> merge (odds (stail (x :> xs))) (odds (stail xs))
           === x :> merge (odds xs) (evens xs)
           *** QED 
        foo :: Eq a => Stream a -> Int -> Bisimilar a 
        {-@ foo :: Stream a -> j:{Nat | j < i } -> _ @-}
        foo xs j = theoremA xs j 


{-@ ple eqKLemma @-}
eqKLemma :: (Eq a) => Stream a -> Stream a -> Int -> Bisimilar a -> () 
{-@ eqKLemma :: x:Stream a -> y:Stream a 
                  -> i:Nat -> (Prop (Bisimilar i x y)) 
                  ->  {take i x = take i y} @-}
eqKLemma _x _ 0 _ = () 
eqKLemma _x _ _i (Bisim i x xs ys p)
  = eqKLemma xs ys (i-1) (p (i-1))


{-@ assert :: b:{Bool | b } -> {b} @-} 
assert :: Bool -> () 
assert _ = ()


approx :: (Eq a) => Stream a -> Stream a -> (Int -> Bisimilar a) -> () 
{-@ approx :: x:Stream a -> y:Stream a 
                  -> (i:Nat -> Prop (Bisimilar i x y)) 
                  -> { x = y } @-}
approx x y p = takeLemma x y (\i -> eqKLemma x y i (p i))  