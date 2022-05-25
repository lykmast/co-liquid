{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-structural-termination" @-}
{-@ LIQUID "--no-adt" @-}

module Section4 where 

import Prelude hiding (take)

import Language.Haskell.Liquid.ProofCombinators 

infixr :>
data Stream a =  a :> Stream a 

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

eqKLemma :: Stream a -> Stream a -> Int -> () 
{-@ assume eqKLemma :: x:Stream a -> y:Stream a 
                  -> i:Nat -> { eqK x y i => (take i x = take i y)} @-}
eqKLemma x y 0 = take 0 x === take 0 y *** QED 
eqKLemma x y i = undefined  


approx :: Stream a -> Stream a -> Int -> () -> () 
{-@ approx :: x:Stream a -> y:Stream a 
                  -> i:Nat -> {v:() | eqK x y i} -> { x = y } @-}
approx x y i p = eqKLemma x y i ? takeLemma x y i  