{-@ LIQUID "--reflection" @-}
{- LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt" @-}
{-@ infix === @-}

{-# LANGUAGE   FlexibleContexts #-}


module ISTR where 
infixl 3 ===
infixl 3 ***

data IStream a = ICons a (IStream a)

{-@ measure ihead @-}
ihead (ICons x _)  = x

{-@ measure itail @-}
itail (ICons _ xs) = xs

{-@ (===) :: x:a -> y:{a | x == y} -> {v:a | v == x && v == y} @-}
(===) :: a -> a -> a   
v === _ = v



data At a b = At a b 

{-@ measure at  @-}
at :: At a b -> a 
at (At a b) = a 

{-@ measure atVal @-}
atVal :: At a b -> b 
atVal (At a b) = b 


{-@ reflect eqK @-}
eqK :: Eq a => Int -> IStream a -> IStream a -> Bool 
eqK 0  _ _ = True 
eqK i (ICons x xs) (ICons y ys) = x == y && eqK (i-1) xs ys 

{-@ reflect merge @-}
merge :: IStream a -> IStream a -> IStream a
merge (ICons x xs) ys = ICons x (merge ys xs)

{-@ reflect odds @-}
odds  :: IStream a -> IStream a
odds (ICons x xs) = ICons x (odds (itail xs))

{-@ reflect evens @-}
evens :: IStream a -> IStream a
evens xs = odds (itail xs)


{-@ eeqq :: k:Nat -> x:IStream a ->  y:{IStream a | eqK k x y } -> {v:IStream a | eqK k x y } @-}
eeqq :: Int -> IStream a ->  IStream a -> IStream a
eeqq  = undefined 

{-@ eeqUn :: x:IStream a -> k:{Nat | 0 < k } -> y:{IStream a | eqK (k-1) (itail x) (itail y) } -> {v:IStream a | eqK k x y && v == x } @-}
eeqUn :: IStream a -> Int -> IStream a -> IStream a
eeqUn  = undefined 

{-@ eeq :: x:IStream a -> k:Nat -> y:{IStream a | x == y } -> {v:IStream a | eqK k x y && v == x  && v == y } @-}
eeq :: IStream a -> Int -> IStream a -> IStream a
eeq  = undefined 


{-@ _lemmaEvenOddK :: k: Nat -> xs:_ -> {eqK k (merge (odds xs) (evens xs)) xs} @-}
_lemmaEvenOddK :: (Eq a, Eq (IStream a)) => Int -> IStream a -> ()
_lemmaEvenOddK 0 _ = undefined 


_lemmaEvenOddK k (x `ICons` xs)
  =   
  
  ((merge (odds (x `ICons` xs)) (evens (x `ICons` xs))
  
  === 
  merge (ICons x (odds (itail xs))) ((odds . itail) (x `ICons` xs))
  
  === 
  ICons x (merge (odds (itail (x `ICons` xs)))  (odds (itail xs)))

  === 
  ICons x (merge (odds xs) (evens xs))
  )
  `eeqUn` k) 
  (x `ICons` xs 
       
       ? _lemmaEvenOddK (k-1) xs) -- eqK (k-1) (merge (odds xs) (evens xs)) xs
       -- itail (x `ICons` xs) == xs 
       -- itail (merge (odds (x `ICons` xs)) (evens (x `ICons` xs))) == merge (odds xs) (evens xs))
       -- 
       -- eqK k (merge (odds (x `ICons` xs)) (evens (x `ICons` xs))) 
       --       (x `ICons` merge (odds xs) (evens xs))) 
  *** QED 


{-
  =  eeqUn (((merge (odds (x `ICons` xs)) (evens (x `ICons` xs))) 
   `eeq` k)
       (x `ICons` merge (odds xs) (evens xs)))
   k 
       (x `ICons` xs 
       
       ? (eeq (merge (odds xs) (evens xs)) (k-1) (xs ? _lemmaEvenOddK (k-1) xs)) )
  *** QED 

-}


{-@ assertSTR :: x:IStream a -> y:{IStream a | x == y} -> {x == y } @-}
assertSTR :: IStream a -> IStream a -> () 
assertSTR _ _ = () 

x ? y = x 

{-@ assert :: b:{Bool | b} -> {b} @-}
assert :: Bool -> ()
assert _ = () 

data QED = QED  
_ *** QED = () 