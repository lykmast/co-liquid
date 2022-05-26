{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-structural-termination" @-}
{-@ LIQUID "--no-adt" @-}

{-# LANGUAGE GADTs #-}
module Section4 where 

import Prelude hiding (take)

import Language.Haskell.Liquid.ProofCombinators 

infixr :>
data Stream a =  a :> Stream a 


{-@ measure eq :: Stream a -> Stream a -> Bool @-}
{-@ type RBisimilar a X Y = {v:Bisimilar a | eq X Y } @-}

data Bisimilar a where 
      Bisim :: a -> Stream a -> Stream a -> Bisimilar a -> Bisimilar a 
{-@ data Bisimilar a where 
          Bisim :: x:a -> xs:Stream a -> ys:Stream a 
                -> RBisimilar a xs ys 
                -> RBisimilar a {(scons x xs)} {(scons x ys)} @-}

-- you cannot put infix above, so defining cons 
{-@ reflect scons @-}
scons :: a -> Stream a -> Stream a 
scons x xs = x :> xs 


odds :: Stream a -> Stream a
odds (x :> xs) = x :> odds (stail xs) 

evens :: Stream a -> Stream a
evens xs = odds (stail xs) 

merge :: Stream a -> Stream a -> Stream a 
merge (x :> xs) ys = x :> merge ys xs  

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


{-@ measure eqK :: Stream a -> Stream a -> Nat -> Bool @-}

eqKAxiom :: Int -> Stream a -> Stream a -> () 
        -> (Int -> ())
        -> () 

{-@ assume eqKAxiom :: i:Nat -> x:Stream a -> y:Stream a 
                   -> {v:() | shead x == shead y} 
                   -> (j:{Nat | j < i} -> {v:() | eqK (stail x) (stail y) j})
                   -> {eqK x y i}  @-}     
eqKAxiom _ _ _ _ _ = ()    


eqKAxiomREV1 :: Int -> Stream a -> Stream a -> () 
        -> () 
eqKAxiomREV2 :: Int -> Stream a -> Stream a -> () 
        -> (Int -> ())
{-@ assume eqKAxiomREV1 :: i:Nat -> x:Stream a -> y:Stream a 
                   -> {v:() |eqK x y i}    
                   -> {v:() | shead x == shead y}  @-}  
eqKAxiomREV1 _ _ _ _ = () 


{-@ assume eqKAxiomREV2 :: i:Nat -> x:Stream a -> y:Stream a 
                   -> {v:() |eqK x y i}    
                   -> (j:{Nat | j < i} -> {v:() | eqK (stail x) (stail y) j})
                   @-}  
eqKAxiomREV2 _ _ _ _ _ = () 


{-@ theorem :: xs:Stream a 
            -> i:Nat -> {v : () | eqK (merge (odds xs) (evens xs)) xs i } @-}
theorem :: Eq a => Stream a -> Int -> ()  
theorem ys@(x :> xs) i 
  = eqKAxiom i (merge (odds (x :> xs)) (evens (x :> xs))) (x :> xs)
            lhs rhs
  where lhs =  shead (merge (odds (x :> xs)) (evens (x :> xs)))
           === shead (merge (x :> odds (stail xs)) (odds (stail (x :> xs)))) 
           === shead (x :> merge (odds (stail (x :> xs))) (odds (stail xs)))
           === shead (x :> xs)  
           *** QED 
        rhs j =  theorem (stail (x :> xs)) j 
              ?   ( stail (merge (odds (x :> xs)) (evens (x :> xs)))
               === merge (odds xs) (evens xs)
               *** QED) 

eqKLemma :: Eq a => Stream a -> Stream a -> Int -> () -> () 
{-@ eqKLemma :: x:Stream a -> y:Stream a 
                  -> i:Nat -> { v:() | eqK x y i} 
                  ->  {take i x = take i y} @-}
eqKLemma x y 0 _ = take 0 x === take 0 y *** QED 
eqKLemma (x :> xs) (y :> ys) i p 
  = (take i (x :> xs) == take i (y :> ys)) 
  ? (x == y && take (i-1) xs == take (i-1) ys)
  ? eqKAxiomREV1 i (x :> xs) (y :> ys) p 
  ? eqKLemma xs ys (i-1) (eqKAxiomREV2 i (x :> xs) (y :> ys) p (i-1))
  *** QED 


approx :: Eq a => Stream a -> Stream a -> Int -> () -> () 
{-@ approx :: x:Stream a -> y:Stream a 
                  -> i:Nat -> {v:() | eqK x y i} -> { x = y } @-}
approx x y i p = eqKLemma x y i p ? takeLemma x y i  