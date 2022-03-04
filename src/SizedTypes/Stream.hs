{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

module SizedTypes.Stream where

import Prelude hiding (repeat, zipWith, map)
import Language.Haskell.Liquid.Prelude (liquidAssert)
import SizedTypes.Size

-- will be hidden.
data Stream a = Cons a (Stream a)

{-@ measure inf :: Stream a -> Bool @-}

{-@ measure size :: Stream a -> Size @-}

{-@ type StreamS a S = {v:Stream a| size v  = S } @-}
{-@ type StreamG a S = {v:Stream a| size   v >= S } @-}
{-@ type StreamI a   = {v:Stream a| inf  v      } @-}

{-@ hd :: s:Size -> {xs:_| s < size xs || inf xs} -> _ @-}
hd :: Size -> Stream a -> a
hd i (Cons x _) = x

{-@ hdi :: StreamI _ -> _ @-}
hdi :: Stream a -> a
hdi = hd 0

{-@ tli :: StreamI _ -> StreamI _ @-}
tli :: Stream a -> Stream a
tli = tl 0

{-@ assume tl :: forall <p::a -> Bool>. s:Size
              -> {xs: Stream a<p>| s < size xs || inf xs}
              -> {v: Stream a<p>| (size v = s) && (inf xs ==> inf v)} @-}
tl :: Size -> Stream a -> Stream a
tl _ (Cons _ xs) = xs

{-@ mkIStream :: _ -> StreamI _ -> StreamI _ @-}
mkIStream :: a -> Stream a -> Stream a
mkIStream x xs = mkStream 0 (const x) (const xs)

{-@ assume mkStream :: forall <p::a->Bool, q::Stream a -> Bool>
                     . {i:Size | i>=0}
                    -> ({j:Size|j<i} -> a<p>)
                    -> ({j:Size|j<i} -> {xs:Stream<q> a<p>| size xs >= j})
                    -> {v:Stream<q> a<p>|size v = i}
@-}
mkStream :: Size -> (Size -> a) -> (Size -> Stream a) -> Stream a
mkStream i fx fxs | i >= 0    = let j = newSize i
                                in  Cons (fx j) (fxs j)
                  | otherwise = undefined

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
--  unless we use newSize.
{-@ zipWith' :: i:Size -> _
             -> StreamG _ i
             -> StreamG _ i
             -> StreamG _ i
@-}
zipWith' :: Size -> (a -> a -> a) -> Stream a -> Stream a -> Stream a
zipWith' i f xs ys = mkStream i
                       (\j ->    (hd (newSize j) (tl j xs))
                              `f` hd (newSize j) (tl j ys))
                       $ \j -> zipWith j f (tl j xs) (tl j ys)

{-@ odds :: StreamI _ -> StreamI _ @-}
odds :: Stream a -> Stream a
odds xs = mkIStream (hdi xs) (tli (tli xs))

{-@ evens :: StreamI _ -> StreamI _ @-}
evens :: Stream a -> Stream a
evens = odds . tli


{-@ merge :: i:Size -> StreamG _ i -> StreamG _ i -> StreamG _ i @-}
merge :: Size -> Stream a -> Stream a -> Stream a
merge i xs ys = mkStream i (\j -> hd j xs) (\j -> merge j ys (tl j xs))


{-@ toggle :: i:Size -> StreamG _ i @-}
toggle :: Num a => Size -> Stream a
toggle i = mkStream i (const 0) $ \j ->
           mkStream j (const 1) toggle


-- In paperfolds one unfolding of merge is necessary
--    to prove termination of paperfolds.
{-@ paperfolds :: i:Size -> StreamG _ i @-}
paperfolds :: Num a =>  Size -> Stream a
paperfolds i = mkStream i (\j -> hd j (toggle i)) $
                           \j -> merge j (paperfolds j) (tl j (toggle i))

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
