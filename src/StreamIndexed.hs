{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--reflection" @-}

module StreamIndexed where

import Language.Haskell.Liquid.ProofCombinators
       hiding ((***), QED, trivial)

import Prelude hiding (not, take)
import Stream

{-@ infixr :> @-}
{-@ infixr . @-}

-- | Predicates
{-@ reflect eqK @-}
{-@ eqK :: k: Nat -> _ -> _ -> _ @-}
eqK :: (Eq a) => Int -> Stream a -> Stream a -> Bool
eqK 0 _ _ = True
eqK k (a :> as) (b :> bs) = a == b && eqK (k-1) as bs

{-@ eqLemma :: xs:_ -> ys:_
              -> (k:Nat -> {eqK k xs ys}) -> {xs = ys} @-}
eqLemma :: Eq a => Stream a -> Stream a -> (Int -> Proof) -> Proof
eqLemma = approx

-- lexicographic comparison
{-@ reflect belowK @-}
{-@ belowK :: Nat -> _ -> _ -> _ @-}
belowK :: Ord a => Int -> Stream a -> Stream a -> Bool
belowK 0 _ _ = True
belowK k (x :> xs) (y :> ys)
  = x <= y && ((x == y) `implies` belowK (k-1) xs ys )

{-@ assume belowLemma :: xs:_ -> ys:_ -> (k:Nat -> {belowK k xs ys})
                        -> {below xs ys} @-}
belowLemma :: Ord a => Stream a -> Stream a -> (Int -> Proof) -> Proof
belowLemma _ _ _ = ()

{-@ reflect trueStreamK @-}
{-@ trueStreamK :: k:Nat -> _ -> Bool /[k] @-}
trueStreamK :: Int -> Stream a -> Bool
trueStreamK 0 _ = True
trueStreamK k (s:>ss) = trueStreamK (k-1) ss

{-@ assume trueSLemma :: x:_ -> (k:Nat -> {trueStreamK k x})
                             -> {trivial x} @-}
trueSLemma :: Stream a -> (Int -> Proof) -> Proof
trueSLemma _ _ = ()



{-@ reflect dupK @-}
{-@ dupK :: Nat -> _ -> _ @-}
dupK :: Eq a => Int -> Stream a -> Bool
dupK 0 _ = True
dupK k (x :> x' :> xs) = x == x' && dupK (k-1) xs

{-@ assume dupLemma :: xs:_ -> (k:Nat -> {dupK k xs}) -> {dup xs} @-}
dupLemma :: Stream a -> (Int -> Proof) -> Proof
dupLemma _ _ = ()

{-@ reflect nnegK @-}
{-@ nnegK :: Nat -> _ -> _ @-}
nnegK :: Int -> Stream Int -> Bool
nnegK 0 _ = True
nnegK k (x :> xs) = x >= 0 && nnegK (k-1) xs

{-@ assume nnegLemma :: xs:_ -> (k:Nat -> {nnegK k xs}) -> {nneg xs} @-}
nnegLemma :: Stream Int ->(Int -> Proof) -> Proof
nnegLemma _ _ = ()

------------------------------------------------------------
-- | Proofs

{-@ mapFusionK :: f:_ -> g:_ -> xs:_ -> k:Nat
                  -> {eqK k (smap f (smap g xs)) (smap (f . g) xs)} @-}
mapFusionK f g xs 0 =
  eqK 0 (smap f (smap g xs)) (smap (f . g) xs) *** QED
mapFusionK f g xxs@(x:>xs) k
  =  smap f (smap g xxs)
 === smap f (g x :> smap g xs)
 === f (g x) :> smap f (smap g xs)
   ? mapFusionK f g xs (k-1)
 =#=  k #
     (f . g) x :> smap (f . g) xs
 === smap (f . g) xxs
 *** QED

{-@ mergeEvenOddK :: xs:_ -> k: Nat
                  -> {eqK k (merge (odds xs) (evens xs)) xs}
@-}
mergeEvenOddK s 0
  =   eqK 0 (merge (odds s) (evens s)) s
  *** QED
mergeEvenOddK xxs@(x :> xs) k
  =
  merge (odds xxs) (evens xxs)
  === merge (x :> odds (stail xs))
            ((odds . stail) xxs)
  === merge (x :> (odds . stail) xs) (odds xs)
  === x :> merge (odds xs) (evens xs)
    ? mergeEvenOddK xs (k-1)
  =#= k # x :> xs
  *** QED

{-@ belowSquareK :: a: Stream Int
                        -> k: Nat
                        -> {belowK k a (mult a a)} @-}
belowSquareK as 0
  =   belowK 0 as (mult as as)
  *** QED
belowSquareK (a :> as) k
   =  a :> as
   ?  belowSquareK as (k-1)
  <=# k #
      a * a :> mult as as
  === mult (a :> as) (a :> as)
  *** QED

{-@ trivialAllK :: s:_ -> k: Nat -> {trueStreamK k s} @-}
trivialAllK s 0 = trueStreamK 0 s *** QED
trivialAllK (s :> ss) k
  =   trueStreamK k (s:>ss)
  === trueStreamK (k-1) ss
  ? trivialAllK ss (k-1)
  *** QED

{-@ mergeSelfDupK :: xs:_ -> k:Nat -> {dupK k (merge xs xs)} @-}
mergeSelfDupK xs 0 = dupK 0 (merge xs xs) *** QED
mergeSelfDupK xxs@(x :> xs) k =
  dupK k (   merge xxs xxs
         === x :> merge xxs xs
         === x :> x :> merge xs xs
         )
  === dupK (k-1) (merge xs xs)
    ? mergeSelfDupK xs (k-1)
  *** QED

{-@ morseMergeK :: xs:_ -> k:Nat
                   -> {eqK k (ff xs) (merge xs (smap not xs))}
@-}
morseMergeK xs 0 = eqK 0 (ff xs) (merge xs (smap not xs)) *** QED
morseMergeK xxs@(x :> xs) 1
  =   ff xxs
  === x :> not x :> ff xs
    ? (eqK 0 (not x :> ff xs) (not x :> merge xs (smap not xs)) *** QED)
  =#= 1 #
      x :> not x :> merge xs (smap not xs)
  === x :> merge (not x :> smap not xs) xs
  === merge xxs (smap not xxs)
  *** QED
morseMergeK xxs@(x :> xs) k
  =   ff xxs
  === x :> (
               not x :> ff xs
             ? morseMergeK xs (k-2)
           =#= k-1 #
               not x :> merge xs (smap not xs)
           )
  =#= k #
      x :> not x :> merge xs (smap not xs)
  === x :> merge (not x :> smap not xs) xs
  === merge xxs (smap not xxs)
  *** QED

{-@ theoremNotFK :: xs:_ -> k:Nat -> {eqK k (smap not (ff xs))
                                            (ff (smap not xs))}
@-}
theoremNotFK xs 0 = eqK 0 (smap not (ff xs)) (ff (smap not xs)) *** QED
theoremNotFK xxs@(x :> xs) 1
  =   smap not (ff xxs)
  === smap not (x :> not x :> ff xs)
  === not x :> smap not (not x :> ff xs)
    ? (eqK 0 (smap not (not x :> ff xs))
             (not (not x) :> ff (smap not xs))
       *** QED
      )
  =#= 1 #
      not x :> not (not x) :> ff (smap not xs)
  === ff (not x :> smap not xs)
  === ff (smap not xxs)
  *** QED
theoremNotFK xxs@(x :> xs) k | k > 1
  =   smap not (ff xxs)
  === smap not (x :> not x :> ff xs)
  === not x :> smap not (not x :> ff xs)
  === not x :> (   not (not x) :> smap not (ff xs)
               ?   theoremNotFK xs (k-2)
               =#= k-1 #
                    not (not x) :> ff (smap not xs)
               )
  =#= k #
      not x :> not (not x) :> ff (smap not xs)
  === ff (not x :> smap not xs)
  === ff (smap not xxs)
  *** QED

{-@ squareNNegK :: xs:_ -> k:Nat -> {nnegK k (mult xs xs)} @-}
squareNNegK xs 0 = nnegK 0 (mult xs xs) *** QED
squareNNegK xxs@(x:>xs) k
  =   nnegK k (mult xxs xxs)
  === nnegK k (x * x :> mult xs xs)
  === (x * x >= 0 && nnegK (k-1) (mult xs xs))
    ? squareNNegK xs (k-1)
  *** QED


-- | Original theorems.

{-@ mapFusion :: f:_ -> g:_ -> xs:_
                 -> {smap f (smap g xs) = smap (f . g) xs} @-}
mapFusion f g xs
  = eqLemma (smap f (smap g xs)) (smap (f . g) xs) (mapFusionK f g xs)

{-@ mergeEvenOdd :: xs:_ -> {merge (odds xs) (evens xs) = xs} @-}
mergeEvenOdd xs =
  eqLemma (merge (odds xs) (evens xs)) xs (mergeEvenOddK xs)

{-@ trivialAll :: xs:_ -> {trivial xs} @-}
trivialAll xs = trueSLemma xs (trivialAllK xs)

{-@ belowSquare :: xs:_ -> {below xs (mult xs xs)} @-}
belowSquare xs =
  belowLemma xs (mult xs xs) (belowSquareK xs)

{-@ mergeSelfDup :: xs:_ -> {dup (merge xs xs)} @-}
mergeSelfDup xs = dupLemma (merge xs xs) (mergeSelfDupK xs)


{-@ morseFix :: {ff morse = morse} @-}
morseFix
  =   ff morse
  === shead morse :> not (shead morse) :> ff (stail morse)
    ? morseMerge (stail morse)
  === False :> True :> merge (stail morse) (smap not (stail morse))
  === morse
  *** QED

{-@ morseMerge :: xs:_ -> {ff xs = merge xs (smap not xs)} @-}
morseMerge :: Stream Bool -> Proof
morseMerge xs =
  eqLemma (ff xs) (merge xs (smap not xs)) (morseMergeK xs)

{-@ theoremNotF :: xs:_ -> {smap not (ff xs) = ff (smap not xs)} @-}
theoremNotF :: Stream Bool -> Proof
theoremNotF xs =
  eqLemma (smap not (ff xs)) (ff (smap not xs)) (theoremNotFK xs)

{-@ squareNNeg :: xs:_ -> {nneg (mult xs xs)} @-}
squareNNeg xs = nnegLemma (mult xs xs) (squareNNegK xs)

------------------------------------------------------------
-- | Proof that \forall i. (Bisimilar i xs ys) => xs = ys
-- using the take lemma.

{-@ reflect take @-}
{-@ take :: Nat -> Stream a -> [a] @-}
take :: Int -> Stream a -> [a]
take 0 _ = []
take i (x :> xs) = x:take (i-1) xs

{-@ assume takeLemma :: x:Stream a -> y:Stream a
                     -> (n:Nat -> {take n x = take n y})
                     -> {x = y} @-}
takeLemma :: Stream a -> Stream a -> (Int -> ()) -> ()
takeLemma _ _ _ = ()

{-@ eqKLemma :: x:_ -> y:_ -> k:Nat
             -> {eqK k x y <=> take k x = take k y} @-}
eqKLemma :: Eq a => Stream a -> Stream a -> Int -> Proof
eqKLemma x y 0 = eqK 0 x y === take 0 x == take 0 y *** QED
eqKLemma (x:>xs) (y:>ys) k
  =   take k (x:>xs) == take k (y:>ys)
  === x:take (k-1) xs == y:take (k-1) ys
  === (x == y && take (k-1) xs == take (k-1) ys)
   ?  eqKLemma xs ys (k-1)
  === eqK k (x:>xs) (y:>ys)
  *** QED

{-@ approx :: x:_ -> y:_ -> (k:Nat -> {eqK k x y}) -> {x = y} @-}
approx x y p = takeLemma x y (\k -> eqKLemma x y k ? p k)

------------------------------------------------------------

infix 0 ***

data QED = QED
_ *** QED = ()

infixr 1 #
(#) = ($)

infix 2 =#=
{-@ (=#=) :: Eq a => x:Stream a -> k:{Nat | 0 < k }
          -> y:{Stream a | eqK (k-1) (stail x) (stail y)
                           && shead x == shead y }
          -> {v:Stream a | eqK k x y && v == x } @-}
(=#=) :: Eq a => Stream a -> Int -> Stream a -> Stream a
(=#=)  xxs@(x :> xs) k yys@(y :> ys) =
  xxs ? (eqK k xxs yys === (x == y && eqK (k-1) xs ys) *** QED)

infix 2 <=#
{-@ (<=#) :: x:Stream Int -> k:{Nat | 0 < k}
          -> y:{Stream Int | (belowK (k-1) (stail x) (stail y)
                               && shead x == shead y)
                             || shead x < shead y}
          -> {v:Stream Int | belowK k x y && v = y } @-}
(<=#) :: Stream Int -> Int -> Stream Int -> Stream Int
(<=#)  xxs@(x :> xs) k yys@(y :> ys) =
  yys ? (belowK k xxs yys
    === (x <= y && ((x == y) `implies` belowK (k-1) xs ys))
    === (x < y || (x == y && belowK (k-1) xs ys))
    *** QED)
