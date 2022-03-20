{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--prune-unsorted" @-} -- or else weird errors :/

module SizedTypes.ReflectedStream where

import Prelude hiding (repeat, zipWith, map, const)
import Language.Haskell.Liquid.Prelude (liquidAssert)
import Language.Haskell.Liquid.ProofCombinators
import SizedTypes.Size

-- will be hidden.
data Stream a = Cons a (Stream a)

{-@ reflect _hd @-}
_hd (Cons x xs) = x

{-@ reflect _tl @-}
_tl (Cons x xs) = xs

{-@ measure inf :: Stream a -> Bool @-}

{-@ measure size :: Stream a -> Size @-}

{-@ type StreamS a S = {v:Stream a| size v  = S } @-}
{-@ type StreamG a S = {v:Stream a| size   v >= S } @-}
{-@ type StreamI a   = {v:Stream a| inf  v      } @-}
-- Streams for proofs need to be either a StreamI (for hdi,tli)
--   or a StreamP(roof) for (hd 0, tl 0).
{-@ type StreamP a   = {v:Stream a| size v >= 0} @-}

{-@ reflect hd @-}
{-@ hd :: s:Size -> {xs:_| s < size xs || inf xs} -> _ @-}
hd :: Size -> Stream a -> a
hd i (Cons x _) = x

{-@ reflect hdi @-}
{-@ hdi :: StreamI _ -> _ @-}
hdi :: Stream a -> a
hdi = hd 0

{-@ reflect tli @-}
{-@ tli :: StreamI _ -> StreamI _ @-}
tli :: Stream a -> Stream a
tli = tl 0

{-@ measure SizedTypes.ReflectedStream.tl :: Size -> Stream a -> Stream a @-}
{-@ assume tl :: forall <p::a -> Bool>. s:Size
              -> {xs: Stream a<p>| s < size xs || inf xs}
              -> {v: Stream a<p>| (size v = s) && (inf xs ==> inf v)
                                  && v = _tl xs && v = tl s xs} @-}
tl :: Size -> Stream a -> Stream a
tl _ xs = _tl xs

{-@ reflect const @-}
const x _ = x

{-@ reflect mkIStream @-}
{-@ mkIStream :: _ -> StreamI _ -> StreamI _ @-}
mkIStream :: a -> Stream a -> Stream a
mkIStream x xs = mkStream 0 (const x) (const xs)

{-@ measure SizedTypes.ReflectedStream.mkStream :: Size
                                                -> (Size -> a)
                                                -> (Size -> Stream a)
                                                -> Stream a
@-}
{-@ assume mkStream :: forall <p::a->Bool, q::Stream a -> Bool>
                     . {i:Size | i>=0}
                    -> fx:({j:Size|j<i} -> a<p>)
                    -> fxs:({j:Size|j<i}-> {xs:Stream<q> a<p>
                                              |size xs >= j })
                    -> {v:Stream<q> a<p>|size v = i
                        && v = mkStream i fx fxs
                        && v = Cons (fx 0) (fxs 0)}
@-}
mkStream :: Size -> (Size -> a) -> (Size -> Stream a) -> Stream a
mkStream _ fx fxs = Cons (fx 0) (fxs 0)

{-@ reflect repeatR @-}
repeatR x = Cons x (repeatR x)

{-@ assume bisim :: i:Size
                 -> xs:_
                 -> ys:_
                 -> ({j:Size| j<i} -> {_hd xs = _hd ys})
                 -> ({j:Size| j<i} -> {_tl xs = _tl ys})
                 -> {xs = ys}
@-}
bisim :: Size -> Stream a -> Stream a
      -> (Size -> Proof) -> (Size -> Proof)
      -> Proof
bisim i xs ys p1 p2 = ()

{-@ thRepeatEq :: i:Size -> x:_ -> {repeatR x = repeat 0 x} @-}
thRepeatEq i x = bisim i (repeatR x) (repeat 0 x) thH thT
  where
    thH j
      =   _hd (thRep j)
      === x
      === _hd (Cons x (repeatR x))
      === _hd (repeatR x)
      *** QED
    thT j
      =   _tl (thRep j)
      === repeat 0 x
        ? thRepeatEq j x
      === repeatR x
      *** QED
    thRep j
      =   repeat 0 x
      === mkStream 0 (_repeat_1 x) (_repeat_2 0 x)
      === Cons (_repeat_1 x 0) (_repeat_2 0 x 0)
      === Cons x (repeat 0 x)

{-@ reflect _repeat_1 @-}
_repeat_1 :: a -> Size -> a
_repeat_1 x j = x

{-@ reflect _repeat_2 @-}
{-@ _repeat_2 :: i:Size -> a -> {j:Size|j<i} -> StreamG a j /[i,0]@-}
_repeat_2 :: Size -> a -> Size -> Stream a
_repeat_2 i x j = repeat j x

{-@ reflect repeat @-}
{-@ repeat :: i:Size -> _ -> StreamG _ i /[i,1]@-}
repeat i x = mkStream i (_repeat_1 x) (_repeat_2 i x)
-- repeat i x = mkStream i (const x) (\j -> repeat j x)


{-@
reflect zipWith
zipWith :: i:Size -> _
        -> StreamG _ i
        -> StreamG _ i
        -> StreamG _ i
        / [i,1]
@-}
zipWith :: Size -> (a -> a -> a) -> Stream a -> Stream a -> Stream a
zipWith i f xs ys = mkStream i (_zipWith_1 i f xs ys)
                               (_zipWith_2 i f xs ys)
-- zipWith i f xs ys = mkStream i
--                       (\j -> hd j xs `f` hd j ys)
--                       $ \j -> zipWith j f (tl j xs) (tl j ys)
{-@
reflect _zipWith_1
_zipWith_1 :: i:Size
           -> _
           -> StreamG _ i
           -> StreamG _ i
           -> {j:Size|j<i}
           -> _
@-}
_zipWith_1 :: Size -> (a -> a -> a) -> Stream a -> Stream a -> Size -> a
_zipWith_1 _ f xs ys j = hd j xs `f` hd j ys

{-@
reflect _zipWith_2
_zipWith_2 :: i:Size
           -> _
           -> StreamG _ i
           -> StreamG _ i
           -> {j:Size|j<i}
           -> StreamG _ j
           / [i,0]
@-}
_zipWith_2
  :: Size
  -> (a -> a -> a)
  -> Stream a
  -> Stream a
  -> Size
  -> Stream a
_zipWith_2 _ f xs ys j = zipWith j f (tl j xs) (tl j ys)

{-@ reflect odds @-}
{-@ odds :: i:Size -> StreamI _ -> StreamG _ i /[i,1]@-}
odds :: Size -> Stream a -> Stream a
odds i xs = mkStream i (_odds_1 i xs) (_odds_2 i xs)
-- odds i xs = mkStream i (const $ hdi xs) (\j -> odds j $ tli . tli $ xs)

{-@ reflect _odds_1 @-}
{-@ _odds_1 :: i:Size -> StreamI _ -> {j:Size|j<i} -> _ @-}
_odds_1 :: Size -> Stream a -> Size -> a
_odds_1 _ xs _ = hdi xs

{-@ reflect _odds_2 @-}
{-@ _odds_2 :: i:Size -> StreamI _ -> {j:Size|j<i}-> StreamG _ j /[i,0]@-}
_odds_2 :: Size -> Stream a -> Size -> Stream a
_odds_2 i xs j = odds j $ tli . tli $ xs

{-@ thOddsEq :: i:Size -> xs:StreamI _ -> {oddsR xs = odds 0 xs} @-}
thOddsEq i xs = bisim i (oddsR xs) (odds 0 xs) thH thT
  where
    thH j
      =   _hd (thOdds j)
      === _hd xs
      === _hd (oddsR xs)
      *** QED
    thT j
      =   _tl (thOdds j)
      === (odds 0 $ _tl . _tl $ xs)
        ? thOddsEq j (_tl . _tl $ xs)
      === (oddsR $ _tl . _tl $ xs)
      === _tl (oddsR xs)
      *** QED
    thOdds j
      =   odds 0 xs
      === mkStream 0 (_odds_1 0 xs) (_odds_2 0 xs)
      === Cons (_odds_1 0 xs 0) (_odds_2 0 xs 0)
      === Cons (hdi xs) (odds 0 $ tli . tli $ xs)
      === Cons (_hd xs) (odds 0 $ _tl . _tl $ xs)

{-@ reflect oddsR @-}
oddsR xs = Cons (_hd xs) (oddsR $ _tl . _tl $ xs)

{-@ reflect evens @-}
{-@ evens :: i:Size -> StreamI _ -> StreamG _ i @-}
evens :: Size -> Stream a -> Stream a
evens i = odds i . tli

{-@ reflect evensR @-}
evensR = oddsR . _tl

{-@ thEvensEq :: i:Size -> xs:StreamI _ -> {evensR xs = evens 0 xs} @-}
thEvensEq :: Size -> Stream a -> Proof
thEvensEq i xs
  =   evens 0 xs
  === (odds 0 . tli $ xs)
  === odds 0 (tli xs)
    ? thOddsEq i (tli xs)
  === oddsR (tl 0 xs)
  === (oddsR . _tl $ xs)
  === evensR xs
  *** QED

{-@ reflect merge @-}
{-@ merge :: i:Size -> StreamG _ i -> StreamG _ i -> StreamG _ i /[i,1]@-}
merge :: Size -> Stream a -> Stream a -> Stream a
merge i xs ys = mkStream i (_merge_1 i xs) (_merge_2 i xs ys)
-- merge i xs ys = mkStream i (\j -> hd j xs) (\j -> merge j ys (tl j xs))

{-@ reflect _merge_1 @-}
{-@ _merge_1 :: i:Size -> StreamG _ i -> {j:Size|j<i} -> _ @-}
_merge_1 :: Size -> Stream a -> Size -> a
_merge_1 _ xs j = hd j xs

{-@
reflect _merge_2
_merge_2 :: i:Size
         -> StreamG _ i
         -> StreamG _ i
         -> {j:Size|j<i}
         -> StreamG _ j
         / [i,0]
@-}
_merge_2 :: Size -> Stream a -> Stream a -> Size -> Stream a
_merge_2 i xs ys j = merge j ys (tl j xs)

{-@ reflect mergeR @-}
mergeR xs ys = _hd xs `Cons` mergeR ys (_tl xs)


{-@ thMergeEq :: i:Size
              -> xs:StreamP _
              -> ys:StreamP _
              -> {mergeR xs ys = merge 0 xs ys}
@-}
thMergeEq i xs ys = bisim i (mergeR xs ys) (merge 0 xs ys) thH thT
  where
    thH j
      =   _hd (thMerge j)
      === _hd xs
      === _hd (mergeR xs ys)
      *** QED
    thT j
      =   _tl (thMerge j)
      === merge 0 ys (_tl xs)
        ? thMergeEq j ys (_tl xs)
      === mergeR ys (_tl xs)
      === _tl (mergeR xs ys)
      *** QED
    thMerge j
      =   merge 0 xs ys
      === mkStream 0 (_merge_1 0 xs) (_merge_2 0 xs ys)
      === Cons (_merge_1 0 xs 0) (_merge_2 0 xs ys 0)
      === Cons (hd 0 xs) (merge 0 ys (tl 0 xs))
      === Cons (_hd xs) (merge 0 ys (_tl xs))

{-@ reflect toggle @-}
{-@ toggle :: i:Size -> StreamG _ i /[i,1] @-}
toggle :: Num a => Size -> Stream a
toggle i = mkStream i (const 0) (_toggle i)
-- toggle i = mkStream i (const 0) $ \j ->
--            mkStream j (const 1) toggle

{-@ reflect _toggle @-}
{-@ _toggle :: i:Size -> {j:Size|j<i} -> StreamG _ j / [i,0] @-}
_toggle :: Num a => Size -> Size -> Stream a
_toggle i j = mkStream j (const 1) toggle


-- In paperfolds one unfolding of merge is necessary
--    to prove termination of paperfolds.
-- The original definition is
-- paperfolds = merge toggle paperfolds
{-@ reflect paperfolds @-}
{-@ paperfolds :: i:Size -> StreamG _ i / [i,1] @-}
paperfolds :: Num a =>  Size -> Stream a
paperfolds i = mkStream i _pfolds_1 (_pfolds_2 i)
-- paperfolds i = mkStream i (\j -> hd j (toggle i)) $
--                            \j -> merge j (paperfolds j) (tl j (toggle i))

{-@ reflect _pfolds_1 @-}
{-@ _pfolds_1 :: Size -> _ @-}
_pfolds_1 :: Num a => Size -> a
_pfolds_1 j = hd j (toggle (j+1))

{-@ reflect _pfolds_2 @-}
{-@ _pfolds_2 :: i:Size -> {j:Size|j<i} -> StreamG _ j / [i,0] @-}
_pfolds_2 :: Num a => Size -> Size -> Stream a
_pfolds_2 i j = merge j (paperfolds j) (tl j (toggle i))

{-@
reflect fivesUp
fivesUp :: i:Size -> n:_
        -> StreamG {v:_ | v >= n} i / [i, fivesUpTerm n,1]
@-}
fivesUp :: Size -> Int -> Stream Int
-- the first clause has i<j (guarded by coinductive constructor)
fivesUp i n | n `mod` 5 == 0
            = mkStream i (const n) (_fivesUp i n)
--          = mkStream i (const n) $ \j -> fivesUp j (n+1)
-- the second clause has decreasing fivesUpTerm n.
            | otherwise = fivesUp i (n+1)

{-@
reflect _fivesUp
_fivesUp :: i:Size
         -> {n:_|n mod 5 = 0}
         -> {j:Size|j<i}
         -> StreamG {v:_ | v >= n} j
         / [i, fivesUpTerm n,0]
@-}
_fivesUp :: Size -> Int -> Size -> Stream Int
_fivesUp _ n j = fivesUp j (n+1)


{-@ inline fivesUpTerm @-}
fivesUpTerm :: Int -> Int
fivesUpTerm n = 4 - ((n-1) `mod` 5)

