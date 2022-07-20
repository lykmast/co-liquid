{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

module SizedTypes.Stream where

import Prelude hiding (repeat, zipWith, map)
import Language.Haskell.Liquid.Prelude (liquidAssert)
import SizedTypes.Size

-- will be hidden.
data Stream a = a :> Stream a
infixr 5 :>

{-@ measure inf :: Stream a -> Bool @-}

{-@ measure size :: Stream a -> Size @-}

{-@ type StreamS a S = {v:Stream a| size v  = S } @-}
{-@ type StreamG a S = {v:Stream a| size v >= S || inf v} @-}
{-@ type StreamI a   = {v:Stream a| inf  v      } @-}

{-@ hd :: s:Size -> {xs:_| s < size xs || inf xs} -> _ @-}
hd :: Size -> Stream a -> a
hd i (x :> _) = x

{-@ hdi :: StreamI _ -> _ @-}
hdi :: Stream a -> a
hdi = hd 0

{-@ tli :: StreamI _ -> StreamI _ @-}
tli :: Stream a -> Stream a
tli = tl 0

{-@ assume tl :: s:Size
              -> {xs: Stream a| s < size xs || inf xs}
              -> {v: Stream a| (size v = s) && (inf xs ==> inf v)} @-}
tl :: Size -> Stream a -> Stream a
tl _ (_ :> xs) = xs

{-@ assume mkStream :: {i:Size | i>=0}
                    -> ({j:Size|j<i} -> a)
                    -> ({j:Size|j<i} -> StreamG a j)
                    -> {v:Stream a|size v = i}
@-}
mkStream :: Size -> (Size -> a) -> (Size -> Stream a) -> Stream a
mkStream _ fx fxs = fx 0 :> fxs 0

{-@ assume toInf :: (i:Size -> StreamG _ i) -> StreamI _ @-}
toInf :: (Size -> Stream a) -> Stream a
toInf f = f 0

{-@ lazy bad @-}
{-@ bad :: _ -> {v:_ | True == False} @-}
bad x = x :> bad (x+1)

{-@ repeat :: i:Size -> _ -> StreamG _ i @-}
repeat i x = mkStream i (const x) (\j -> repeat j x)

{-@ zipWith :: i:Size -> _
            -> StreamG _ i
            -> StreamG _ i
            -> StreamG _ i
@-}
zipWith :: Size -> (a -> a -> a) -> Stream a -> Stream a -> Stream a
zipWith i f xs ys = mkStream i
                      (\j -> hd j xs `f` hd j ys)
                      $ \j -> zipWith j f (tl j xs) (tl j ys)

{-@ fib :: i:Size -> StreamG _ i @-}
fib :: Num a => Size -> Stream a
fib i = mkStream i (const 0)
          $ \j -> mkStream j (const 1)
          $ \k -> zipWith k (+) (fib k) (tl k (fib j))

-- The definition below is wrong and it (correctly) does not typecheck
--  unless we use fail.
{-@ fail zipWith' @-}
{-@ zipWith' :: i:Size -> _
             -> StreamG _ i
             -> StreamG _ i
             -> StreamG _ i
@-}
zipWith' :: Size -> (a -> a -> a) -> Stream a -> Stream a -> Stream a
zipWith' i f xs ys = mkStream i
                       (\j ->    (hd j (tl j xs))
                              `f` hd j (tl j ys))
                       $ \j -> zipWith j f (tl j xs) (tl j ys)

{-@ odds :: i:Size -> StreamI _ -> StreamG _ i @-}
odds :: Size -> Stream a -> Stream a
odds i xs = mkStream i (const $ hdi xs) (\j -> odds j $ tli . tli $ xs)

{-@ evens :: i:Size -> StreamI _ -> StreamG _ i @-}
evens :: Size -> Stream a -> Stream a
evens i = odds i . tli


{-@ merge :: i:Size -> StreamG _ i -> StreamG _ i -> StreamG _ i @-}
merge :: Size -> Stream a -> Stream a -> Stream a
merge i xs ys = mkStream i (\j -> hd j xs) (\j -> merge j ys (tl j xs))


{-@ toggle :: i:Size -> StreamG _ i @-}
toggle :: Num a => Size -> Stream a
toggle i = mkStream i (const 0) $ \j ->
           mkStream j (const 1) toggle


-- In paperfolds one unfolding of merge is necessary
--    to prove termination of paperfolds.
-- The original definition is
-- paperfolds = merge toggle paperfolds
{-@ paperfolds :: i:Size -> StreamG _ i @-}
paperfolds :: Num a =>  Size -> Stream a
paperfolds i = mkStream i (\j -> hdi (toInf toggle)) $
                           \j -> merge j (paperfolds j) (tli (toInf toggle))

{-@ fivesUp :: i:Size -> n:_
            -> StreamG {v:_ | v >= n} i / [i, fivesUpTerm n]
@-}
fivesUp :: Size -> Int -> Stream Int
-- the first clause has i<j (guarded by coinductive constructor)
fivesUp i n | n `mod` 5 == 0
            = mkStream i (const n) $ \j -> fivesUp j (n+1)
-- the second clause has decreasing fivesUpTerm n.
            | otherwise = fivesUp i (n+1)

{-@ inline fivesUpTerm @-}
fivesUpTerm :: Int -> Int
fivesUpTerm n = 4 - ((n-1) `mod` 5)
