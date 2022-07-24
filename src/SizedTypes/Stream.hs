{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

module SizedTypes.Stream where

import Prelude hiding (repeat, zipWith, map)
import Language.Haskell.Liquid.Prelude (liquidAssert)

-- will be hidden.
data Stream a = a :> Stream a
infixr 5 :>

{-@ measure inf :: Stream a -> Bool @-}

{-@ measure size :: Stream a -> Nat @-}

{-@ type StreamS a S = {v:Stream a| size v  = S } @-}
{-@ type StreamG a S = {v:Stream a| size v >= S || inf v} @-}
{-@ type StreamI a   = {v:Stream a| inf  v      } @-}

{-@ shead :: s:Nat -> {xs:_| s < size xs || inf xs} -> _ @-}
shead :: Int -> Stream a -> a
shead i (x :> _) = x

{-@ ihead :: StreamI _ -> _ @-}
ihead :: Stream a -> a
ihead = shead 0

{-@ itail :: StreamI _ -> StreamI _ @-}
itail :: Stream a -> Stream a
itail = stail 0

{-@ assume stail :: s:Nat
              -> {xs: Stream a| s < size xs || inf xs}
              -> {v: Stream a| (size v = s) && (inf xs ==> inf v)} @-}
stail :: Int -> Stream a -> Stream a
stail _ (_ :> xs) = xs

{-@ assume cons :: {i:Nat | i>=0}
                    -> ({j:Nat|j<i} -> a)
                    -> ({j:Nat|j<i} -> StreamG a j)
                    -> {v:Stream a|size v = i}
@-}
cons :: Int -> (Int -> a) -> (Int -> Stream a) -> Stream a
cons _ fx fxs = fx 0 :> fxs 0

{-@ assume toInf :: (i:Nat -> StreamG _ i) -> StreamI _ @-}
toInf :: (Int -> Stream a) -> Stream a
toInf f = f 0

{-@ lazy bad @-}
{-@ bad :: _ -> {v:_ | True == False} @-}
bad x = x :> bad (x+1)

{-@ repeat :: i:Nat -> _ -> StreamG _ i @-}
repeat i x = cons i (const x) (\j -> repeat j x)

{-@ zipWith :: i:Nat -> _
            -> StreamG _ i
            -> StreamG _ i
            -> StreamG _ i
@-}
zipWith :: Int -> (a -> a -> a) -> Stream a -> Stream a -> Stream a
zipWith i f xs ys = cons i
                      (\j -> shead j xs `f` shead j ys)
                      $ \j -> zipWith j f (stail j xs) (stail j ys)

{-@ fib :: i:Nat -> StreamG _ i @-}
fib :: Num a => Int -> Stream a
fib i = cons i (const 0)
          $ \j -> cons j (const 1)
          $ \k -> zipWith k (+) (fib k) (stail k (fib j))

-- The definition below is wrong and it (correctly) does not typecheck
--  unless we use fail.
{-@ fail zipWith' @-}
{-@ zipWith' :: i:Nat -> _
             -> StreamG _ i
             -> StreamG _ i
             -> StreamG _ i
@-}
zipWith' :: Int -> (a -> a -> a) -> Stream a -> Stream a -> Stream a
zipWith' i f xs ys = cons i
                       (\j ->    (shead j (stail j xs))
                              `f` shead j (stail j ys))
                       $ \j -> zipWith j f (stail j xs) (stail j ys)

{-@ odds :: i:Nat -> StreamI _ -> StreamG _ i @-}
odds :: Int -> Stream a -> Stream a
odds i xs = cons i (const $ ihead xs) (\j -> odds j $ itail . itail $ xs)

{-@ evens :: i:Nat -> StreamI _ -> StreamG _ i @-}
evens :: Int -> Stream a -> Stream a
evens i = odds i . itail


{-@ merge :: i:Nat -> StreamG _ i -> StreamG _ i -> StreamG _ i @-}
merge :: Int -> Stream a -> Stream a -> Stream a
merge i xs ys = cons i (\j -> shead j xs) (\j -> merge j ys (stail j xs))


{-@ toggle :: i:Nat -> StreamG _ i @-}
toggle :: Num a => Int -> Stream a
toggle i = cons i (const 0) $ \j ->
           cons j (const 1) toggle


-- In paperfolds one unfolding of merge is necessary
--    to prove termination of paperfolds.
-- The original definition is
-- paperfolds = merge toggle paperfolds
{-@ paperfolds :: i:Nat -> StreamG _ i @-}
paperfolds :: Num a =>  Int -> Stream a
paperfolds i = cons i (\j -> ihead (toInf toggle)) $
                           \j -> merge j (paperfolds j) (itail (toInf toggle))

{-@ fivesUp :: i:Nat -> n:_
            -> StreamG {v:_ | v >= n} i / [i, fivesUpTerm n]
@-}
fivesUp :: Int -> Int -> Stream Int
-- the first clause has i<j (guarded by coinductive constructor)
fivesUp i n | n `mod` 5 == 0
            = cons i (const n) $ \j -> fivesUp j (n+1)
-- the second clause has decreasing fivesUpTerm n.
            | otherwise = fivesUp i (n+1)

{-@ inline fivesUpTerm @-}
fivesUpTerm :: Int -> Int
fivesUpTerm n = 4 - ((n-1) `mod` 5)
