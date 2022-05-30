{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-structural-termination" @-}
{-@ LIQUID "--no-adt" @-}

module Section3 where 

import Prelude hiding (take, map)

import Language.Haskell.Liquid.ProofCombinators hiding (QED, (***))


-- "monotonicity"
-- Good q: Figure 7 
-- end of 3. q ~~> p 
{-@ assume axiom :: p:(Stream a -> Stream a -> Int -> Bool) 
                 -> q:(Stream a -> Stream a -> Bool)
                 -> x:Stream a -> y:Stream a
                 -> (k:Nat -> {v:() | p x y k} )
                 -> {q x y} @-} -- Correct Syntactic rules 
axiom :: (Stream a -> Stream a -> Int -> Bool) -> (Stream a -> Stream a -> Bool) ->  Stream a -> Stream a -> (Int -> ()) -> () 
axiom _ _ _ _ _ = () 


{-@ reflect lift @-}
lift :: (a -> a -> Bool) 
     -> Stream a -> Stream a -> Int -> Bool 
{-@ lift :: (a -> a -> Bool) 
         -> Stream a -> Stream a -> i:Nat -> Bool /[i] @-}
lift p _ _ 0 = True 
lift p (x:>xs) (y:>ys) k = p x y && lift p xs ys (k-1)

{-@ reflect eq @-}
eq :: Eq a => a -> a -> Bool 
eq x y = x == y 

{-@ reflect map @-}
map :: (a -> b) -> Stream a -> Stream b 
map f (x :> xs) = f x :> map f xs 


{-@ stream_fusion :: xs:Stream a -> f:(a -> a) -> g:(a -> a)
            -> k:Nat -> {v : () | lift eq (map (f . g) xs) (map f (map g xs))  k } @-}
stream_fusion :: Eq a => Stream a -> (a -> a) -> (a -> a) -> Int -> ()  
stream_fusion xs f g 0 = lift eq (map (f . g) xs) (map f (map g xs))  0 *** QED  
stream_fusion (x :> xs) f g k 
  =   map (f . g) (x :> xs)
  === (f . g) x :> map (f . g) xs
  === f (g x) :> map (f . g) xs
      ? stream_fusion xs f g (k-1) -- lift eq (merge (odds xs) (evens xs)) (xs) k
  =#=  k # 
      f (g x) :> map f (map g xs)
  === map f (g x :> map g xs)
  === map f (map g (x :> xs))
  *** QED 


{-@ theorem :: xs:Stream a 
            -> k:Nat -> {v : () | lift eq (merge (odds xs) (evens xs)) (xs) k } @-}
theorem :: Eq a => Stream a -> Int -> ()  
theorem xs 0 = lift eq (merge (odds xs) (evens xs)) (xs) 0 *** QED  
theorem (x :> xs) k 
  =   merge (odds (x :> xs)) (evens (x :> xs))
  === merge (x :> odds (ltail xs)) (odds (ltail (x :> xs))) 
  === x :> merge (odds (ltail (x :> xs))) (odds (ltail xs))
  === x :> merge (odds xs) (evens xs)  
      ? theorem xs (k-1) -- lift eq (merge (odds xs) (evens xs)) (xs) k
  =#=  k # 
      x :> xs
  *** QED 




infix 0 ***

data QED = QED
_ *** QED = ()

infixr 1 #
(#) = ($)

infix 2 =#=
{-@ (=#=) :: Eq a => x:Stream a -> k:{Nat | 0 < k } 
          -> y:{Stream a | lift eq (ltail x) (ltail y) (k-1)  && lhead x == lhead y } 
          -> {v:Stream a | lift eq x y k && v == x } @-}
(=#=) :: Eq a => Stream a -> Int -> Stream a -> Stream a
(=#=)  xxs@(x :> xs) k yys@(y :> ys) =
   xxs ? (lift eq xxs yys k === (eq x y && lift eq xs ys (k-1)) *** QED)






infixr :>
data Stream a =  a :> Stream a 

odds :: Stream a -> Stream a
odds (x :> xs) = x :> odds (ltail xs) 

evens :: Stream a -> Stream a
evens xs = odds (ltail xs) 

merge :: Stream a -> Stream a -> Stream a 
merge (x :> xs) ys = x :> merge ys xs  

{-@ reflect odds  @-}
{-@ reflect evens @-}
{-@ reflect merge @-}




{-@ measure lhead @-}
{-@ measure ltail @-}

lhead :: Stream a -> a 
ltail :: Stream a -> Stream a 
lhead (x :> _ ) = x 
ltail (_ :> xs) = xs 

{-@ reflect take @-}
{-@ take :: Nat -> Stream a -> [a] @-}
take :: Int -> Stream a -> [a]
take 0 _ = [] 
take i (x :> xs) = x:take (i-1) xs 

{-@ assume takeLemma :: x:Stream a -> y:Stream a 
                     -> (n:Nat -> {v:() | take n x = take n y})
                     -> {x = y} @-}
takeLemma :: Stream a -> Stream a -> (Int -> ()) -> ()  
takeLemma _ _ _ = () 

{-@ approx :: x:Stream a -> y:Stream a 
           -> (n:Nat -> {v:() | eqK x y n })
           -> { x = y } @-}
approx :: Eq a => Stream a -> Stream a -> (Int -> ()) -> ()  
approx xs ys p =  takeLemma xs ys (\n -> (p n ? eqLemma xs ys n))  


{-@ eqLemma :: x:Stream a -> y:Stream a -> n:Nat 
                     -> {(take n x = take n y) <=> eqK x y n} @-}
eqLemma :: Eq a => Stream a -> Stream a -> Int -> () 
eqLemma xs ys 0 
  = eqK xs ys 0 ? take 0 xs ? take 0 ys  *** QED 
eqLemma (x :> xs) (y :> ys) i 
  =   take i (x :> xs) == take i (y :> ys)
  === (x:take (i-1)xs == y:take (i-1) ys)
  === (x == y && take (i-1) xs == take (i-1) ys)
       ? eqLemma xs ys (i-1)
  === (x == y && eqK xs ys (i-1))
  === eqK (x :> xs) (y :> ys) i 
  *** QED 


{-@ reflect eqK @-}
{-@ eqK :: Stream a -> Stream a -> Nat -> Bool @-}
eqK :: Eq a => Stream a -> Stream a -> Int -> Bool 
eqK _ _ 0 = True 
eqK (x :> xs) (y :> ys) i = x == y && eqK xs ys (i-1)