{-@ LIQUID "--reflection" @-}

-- NV: The flag below says that Haskell ADTs are not encoded as SMT ADTs
{-@ LIQUID "--no-adt" @-}

module Streams where 

import Language.Haskell.Liquid.ProofCombinators 

-- infinite streams
-- !!! The line below yields an SMTLib2 error:
--   "datatype not well founded".
--   This is due to cyclical definition of IStream (see SMTLib2 reference).
-- {-@ data IStream a = ICons {ihead :: a, itail :: IStream a} @-}
data     IStream a = ICons {ihead :: a, itail :: IStream a}

{-@ reflect pos @-} --this reflect will not work because IStream is not reflected.
pos (ICons x xs) = x > 0 && pos xs 


-- pointwise product of streams
mult :: IStream Int -> IStream Int -> IStream Int
mult (ICons a as) (ICons b bs) = ICons (a*b) (mult as bs)
{-@ reflect mult @-} --this reflect will not work because IStream is not reflected.

{-@ reflect nat @-} 
nat (ICons x xs) = x >= 0 && nat xs 

-- NV: This does not hold because the elements might be equalt to zero
{- theoremPosSquare :: a:IStream Int -> {pos (mult a a) }@-}
{- 
theoremPosSquare :: IStream Int -> ()
theoremPosSquare a@(ICons ha ta)
  =   pos (mult a a)
  === pos (mult (ICons ha ta) (ICons ha ta))
  === pos (ICons (ha * ha) (mult ta ta))
  === (ha * ha >= 0 && pos (mult ta ta))
    ? theoremPosSquare ta 
  === True 
  *** QED
-}

{-@ theoremNatSquare :: a:IStream Int -> {nat (mult a a) }@-}
theoremNatSquare :: IStream Int -> ()
theoremNatSquare a@(ICons ha ta)
  =   nat (mult a a)
  === nat (mult (ICons ha ta) (ICons ha ta))
  === nat (ICons (ha * ha) (mult ta ta))
  === (ha * ha >= 0 && nat (mult ta ta))
    ? theoremNatSquare ta 
  === (ha * ha >= 0) 
  === True 
  *** QED

-- NV: In Liquid Haskell it is more natural to express the 
-- theoremNatSquare intrinsically, ie as part of the mu definition: 
{-@ multIntr :: IStream {v:Int | 0 <= v } -> IStream {v:Int | 0 <= v } -> IStream {v:Int | 0 <= v } @-}
multIntr :: IStream Int -> IStream Int -> IStream Int
multIntr (ICons a as) (ICons b bs) = ICons (a*b) (multIntr as bs)



-- lists
{-@ data List [size] a = Cons {hd :: a, tl :: List a} | Nil @-}
data List a = Cons {hd :: a, tl :: List a} | Nil

{-@ measure size @-}
{-@ size :: List a -> Nat @-}
size :: List a -> Int 
size Nil = 0 
size (Cons _ xs) = 1 + size xs 

-- this predicate is ill-defined.
{-
predicate Below XS YS =
  (hd XS <= hd YS) &&
  ((hd XS = hd YS) ==> (Below (tl XS) (tl YS)))
@-}

-- NV: You can define Below as a Reflected Haskell Function 

{-@ reflect below @-}
below :: Ord a => List a -> List a -> Bool 
below (Cons x xs) (Cons y ys)
  = x <= y && if x == y then below xs ys else False 
below Nil Nil  = True 
below _ _ = False -- I assume 


{-@ type Pos = {v:Int| v > 0} @-}

 --this function will not typecheck unless marked lazy, because of termination.
 -- NV: Your termination metric does not seem correct: 
 -- I encoded it as a theorem to show termination, but the theorem has a counter example
{-@ fivesUp :: n:Pos -> List Pos / [fibUpTerm n] @-}
fivesUp :: Int -> List Int
fivesUp n   | n `mod` 5 == 0 = n `Cons` fivesUp (n+1 ? fibUpTermProof n) -- this should be exempt from termination check
            | otherwise      = fivesUp (n+1 ? fibUpTermProof n) 


{-@ inline fibUpTerm @-}
fibUpTerm :: Int -> Int 
fibUpTerm n = 4 - (n-1) `mod` 5

{-@ fibUpTermProof :: n:Pos -> { fibUpTerm (n+1) >= 0 && fibUpTerm (n+1) < fibUpTerm n } @-}
fibUpTermProof :: Int -> () 
fibUpTermProof n = fibUpTermProofR n  


-- NV: This is not true: does not hold for n == 4
-- fibUpTerm (4+1) = 4 - 4 `mod` 5 = 0 >  
-- fibUpTerm 4     = 4 - 3 `mod` 5 = 1
{-@ assume fibUpTermProofR :: n:Pos -> { fibUpTerm (n+1) < fibUpTerm n } @-}
fibUpTermProofR :: Int -> () 
fibUpTermProofR n = () 
