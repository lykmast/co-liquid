{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Overview where 

import Language.Haskell.Liquid.ProofCombinators

infixr :>
data Stream a =  a :> Stream a | E 

odds :: Stream a -> Stream a
odds E                = E 
odds (x :> E)         = x :> E
odds (x :> xs)        = x :> odds (ltail xs) 

{-@ evens :: NEStream a -> Stream a @-}
evens :: Stream a -> Stream a
evens xs = odds (ltail xs) 

merge :: Stream a -> Stream a -> Stream a 
{-@ merge :: xs:Stream a -> ys:Stream a -> Stream a 
           / [llen xs + llen ys] @-} 
merge E _           = E
merge (x :> xs) ys = x :> merge ys xs  



{-@ reflect odds  @-}
{-@ reflect evens @-}
{-@ reflect merge @-}


{-@ theorem :: xs:Stream a 
            -> {merge (odds xs) (evens xs) == xs } @-}
theorem :: Stream a -> () 
theorem E = () 
theorem (x :> E) = ()
theorem (x :> xs)
  =   merge (odds (x :> xs)) (evens (x :> xs))
  === merge (x :> odds (ltail xs)) (odds (ltail (x :> xs))) 
  === x :> merge (odds (ltail (x :> xs))) (odds (ltail xs))
  === x :> merge (odds xs) (evens xs)  
      ? theorem xs 
  === x :> xs
  *** QED 

{-@ measure llen @-}
llen :: Stream a -> Int 
{-@ llen :: Stream a -> Nat @-}
llen E = 0 
llen (_ :> xs) = 1 + llen xs 


{-@ measure lhead @-}
{-@ measure ltail @-}
{-@ measure notEmpty @-}
notEmpty :: Stream a -> Bool 
notEmpty E = False 
notEmpty _ = True 
{-@ lhead :: NEStream a -> a @-}
{-@ ltail :: NEStream a -> Stream a @-}
{-@ type NEStream a = {x:Stream a | notEmpty x} @-}
lhead :: Stream a -> a 
ltail :: Stream a -> Stream a 
lhead (x :> _ ) = x 
ltail (_ :> xs) = xs 

-- bar :: Stream a -> a 
-- bar x = lhead x 


falseStream :: Stream a -> () 
{-@ falseStream :: Stream a -> {false} @-}
falseStream (_ :> xs) = falseStream xs  
falseStream _ = undefined 