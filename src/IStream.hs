{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
module IStream where

import Language.Haskell.Liquid.ProofCombinators

data IStream a = ICons a (IStream a)

{-@ measure ihead @-}
ihead (ICons x _)  = x 

{-@ measure itail @-}
itail (ICons _ xs) = xs


{-@ reflect nneg @-}
nneg :: IStream Int -> Bool
nneg (ICons x xs) = x >= 0 && nneg xs

-- pointwise product of streams
{-@ reflect mult @-}
mult :: IStream Int -> IStream Int -> IStream Int
mult (ICons a as) (ICons b bs) = ICons (a * b) (mult as bs)

{-@ theoremNNegSquare :: a:IStream Int -> {nneg (mult a a)}@-}
theoremNNegSquare :: IStream Int -> ()
theoremNNegSquare (ICons a as)
  =   nneg (mult (ICons a as) (ICons a as))
  === nneg (ICons (a * a) (mult as as))
  === (a * a >= 0 && nneg (mult as as))
    ? theoremNNegSquare as
  *** QED


{-@ reflect below @-}
below :: Ord a => IStream a -> IStream a -> Bool 
below (ICons x xs) (ICons y ys)
  = x <= y && ((x == y) `implies` below xs ys ) 

{-@ theoremBelowMult :: a:IStream Int -> {below a (mult a a)}@-}
theoremBelowMult :: IStream Int -> ()
theoremBelowMult (ICons a as)
  =   below (ICons a as) (mult (ICons a as) (ICons a as))
  === below (ICons a as) (ICons (a * a) (mult as as))
  === (a <= a*a && ( (a == a*a) `implies` below as (mult as as))) 
      ? theoremBelowMult as
  *** QED


{-@ reflect merge @-}
merge :: IStream a -> IStream a -> IStream a
merge (ICons x xs) ys = ICons x (merge ys xs)

{-@ reflect odds @-}
odds  :: IStream a -> IStream a
odds (ICons x xs) = ICons x (odds (itail xs))

{-@ reflect evens @-}
evens :: IStream a -> IStream a
evens = odds . itail

{-@ lemmaEvenOdd :: xs:_ -> {merge (odds xs) (evens xs) = xs} @-}
lemmaEvenOdd :: IStream a -> Proof
lemmaEvenOdd (ICons x xs) 
  =   merge (odds (ICons x xs)) (evens (ICons x xs))
  === merge (ICons x (odds (itail xs))) ((odds . itail) (ICons x xs))
  === merge (ICons x ((odds . itail) xs)) (odds xs)
  === ICons x (merge (odds xs) (evens xs))
      ? lemmaEvenOdd xs
  === ICons x xs
  *** QED

------------------------------------------------------------
-- Examples below are not complete: We still need lazy to make
--   them pass. In Dafny the parts marked lazy would be exempt
--   from termination checks as "co-recursive calls".

{-@ lazy up @-}
{-@ up :: n:_ -> IStream {v:_| v >= n} @-}
up :: Int -> IStream Int
up n = n `ICons` up (n+1)

-- this is not checked for termination in dafny.
{-@ lazy fivesUpC @-}
{-@ fivesUpC :: n:{v:_| v mod 5 = 0} -> IStream {v:_ | v >= n}  @-}
fivesUpC :: Int -> IStream Int
fivesUpC n = n `ICons` fivesUpI (n+1)

-- this should be checked, but lazy prevents it.
-- how this *probably* works in dafny:
--   - n mod 5 /=0 ==> fivesUpTerm (n+1) < fivesUpTerm n
--     (see theoremFivesUpTerm below).
--   - The important part is that only fivesUpI is checked and
--     this established the precondition n mod 5 /= 0 for the
--     termination check.
{-@ fivesUpI :: n:{v:_| v mod 5 /= 0} 
             -> IStream {v:_ | v >= n} / [fivesUpTerm n]  @-}
fivesUpI :: Int -> IStream Int
fivesUpI n | np1 `mod` 5 /= 0 = fivesUpI np1 
           | otherwise        = fivesUpC np1
             where np1 = n + 1

{-@ fivesUp :: n:_ -> IStream {v:_ | v >= n} @-}
fivesUp :: Int -> IStream Int
fivesUp n | n `mod` 5 == 0 = fivesUpC n
          | otherwise      = fivesUpI n

{-@ inline fivesUpTerm @-}
fivesUpTerm :: Int -> Int
fivesUpTerm n = 4 - ((n-1) `mod` 5)


{-@ reflect trueStream @-}
trueStream :: IStream a -> Bool
trueStream = trueStream . itail 

{-@ trueLemma :: s:_ -> {trueStream s} @-}
trueLemma :: IStream a -> Proof
trueLemma (ICons s ss) 
  =   trueStream (ICons s ss) 
  === (trueStream . itail) (ICons s ss)
  === trueStream ss
      ? trueLemma ss
  *** QED

-- falseLemma erroneously typechecks but when we translate 
--    the proof to induction it successfully fails.
{-@ falseLemma :: s:_ -> {false} @-}
falseLemma :: IStream a -> Proof
falseLemma (ICons s ss) 
  =  False ? falseLemma ss
  *** QED

------------------------------------------------------------

{-@ reflect implies @-}
{-@ implies :: p:Bool -> q:Bool -> {v:_| v <=> (p => q)} @-}
implies False _ = True
implies _ True = True
implies _ _ = False

{-@ theoremFivesUpTerm :: n:{n:_| n mod 5 /=0} 
                       -> {fivesUpTerm (n+1) < fivesUpTerm n} @-}
theoremFivesUpTerm :: Int -> Proof
theoremFivesUpTerm _ = ()
