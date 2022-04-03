{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
module IStream where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.Prelude
data IStream a = ICons a (IStream a)

{-@ measure ihead @-}
ihead (ICons x _)  = x

{-@ measure itail @-}
itail (ICons _ xs) = xs

-- pointwise product of streams
{-@ reflect mult @-}
mult :: IStream Int -> IStream Int -> IStream Int
mult (ICons a as) (ICons b bs) = ICons (a * b) (mult as bs)


{-@ reflect nneg @-}
nneg :: IStream Int -> Bool
nneg (ICons x xs) = x >= 0 && nneg xs

{-@ assume dAxiom_nneg :: xs:IStream Int
                       -> (k:Nat -> {nnegK k xs}) -> {nneg xs} @-}
dAxiom_nneg :: IStream Int -> (Int -> Proof) -> Proof
dAxiom_nneg _ _ = ()

{-@ reflect nnegK @-}
{-@ nnegK :: Nat -> _ -> _ @-}
nnegK :: Int -> IStream Int -> Bool
nnegK 0 _ = True
nnegK k (ICons x xs) = x >= 0 && nnegK (k-1) xs

{-@ theoremNNegSquare :: a:IStream Int -> {nneg (mult a a)}@-}
theoremNNegSquare :: IStream Int -> ()
-- theoremNNegSquare (ICons a as)
--   =   nneg (mult (ICons a as) (ICons a as))
--   === nneg (ICons (a * a) (mult as as))
--   === (a * a >= 0 && nneg (mult as as))
--     ? theoremNNegSquare as
--   *** QED
--
-- | The above theorem must be proven without co-recursion through
--    the prefix versions

theoremNNegSquare a =
  dAxiom_nneg (mult a a) (\k -> _theoremNNegSquareK k a)

{-@ _theoremNNegSquareK :: k:Nat -> a:IStream Int
                        -> {nnegK k (mult a a)} @-}
_theoremNNegSquareK :: Int -> IStream Int -> ()
_theoremNNegSquareK 0 a = nnegK 0 (mult a a) *** QED
_theoremNNegSquareK k (ICons a as)
  =   nnegK k (mult (ICons a as) (ICons a as))
  === nnegK k (ICons (a * a) (mult as as))
  === (a * a >= 0 && nnegK (k-1) (mult as as))
    ? _theoremNNegSquareK (k-1) as
  *** QED



{-@ reflect below @-}
below :: Ord a => IStream a -> IStream a -> Bool
below (ICons x xs) (ICons y ys)
  = x <= y && ((x == y) `implies` below xs ys )

{-@ assume dAxiom_below :: xs:_ -> ys:_ -> (k:Nat -> {_belowK k xs ys})
                        -> {below xs ys} @-}
dAxiom_below :: Ord a => IStream a -> IStream a -> (Int -> Proof) -> Proof
dAxiom_below _ _ _ = ()

{-@ reflect _belowK @-}
{-@ _belowK :: Nat -> _ -> _ -> _ @-}
_belowK :: Ord a => Int -> IStream a -> IStream a -> Bool
_belowK 0 _ _ = True
_belowK k (ICons x xs) (ICons y ys)
  = x <= y && ((x == y) `implies` _belowK (k-1) xs ys )


{-@ theoremBelowSquare :: a:IStream Int -> {below a (mult a a)}@-}
-- theoremBelowSquare (ICons a as)
--   =   below (ICons a as) (mult (ICons a as) (ICons a as))
--   === below (ICons a as) (ICons (a * a) (mult as as))
--   === (a <= a*a && ( (a == a*a) `implies` below as (mult as as)))
--     ? theoremBelowSquare as
--   *** QED

{-@ _theoremBelowSquareK :: k: Nat
                         -> a: IStream Int
                         -> {_belowK k a (mult a a)} @-}
_theoremBelowSquareK :: Int -> IStream Int -> ()
_theoremBelowSquareK 0 as
  =   _belowK 0 as (mult as as)
  *** QED
_theoremBelowSquareK k (ICons a as)
  =   _belowK k (ICons a as) (mult (ICons a as) (ICons a as))
  === _belowK k (ICons a as) (ICons (a * a) (mult as as))
  === (a <= a*a &&
        ((a == a*a) `implies` _belowK (k-1) as (mult as as)))
    ? _theoremBelowSquareK (k-1) as
  *** QED

theoremBelowSquare :: IStream Int -> ()
theoremBelowSquare a = dAxiom_below a (mult a a)
                        (\k -> _theoremBelowSquareK k a)


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
lemmaEvenOdd :: Eq a => IStream a -> Proof
-- lemmaEvenOdd (ICons x xs)
--   =   merge (odds (ICons x xs)) (evens (ICons x xs))
--   === merge (ICons x (odds (itail xs))) ((odds . itail) (ICons x xs))
--   === merge (ICons x ((odds . itail) xs)) (odds xs)
--   === ICons x (merge (odds xs) (evens xs))
--     ? lemmaEvenOdd xs
--   === ICons x xs
--   *** QED

lemmaEvenOdd xs = dAxiom_eq (merge (odds xs) (evens xs)) xs
                            (\k -> _lemmaEvenOddK k xs)

{-@ _lemmaEvenOddK :: k: Nat -> xs:_ -> {eqK k (merge (odds xs) (evens xs)) xs} @-}
_lemmaEvenOddK :: (Eq a) => Int -> IStream a -> Proof
_lemmaEvenOddK 0 s
  =   eqK 0 (merge (odds s) (evens s)) s
  *** QED
_lemmaEvenOddK k (ICons x xs)
  =   eqK k (merge (odds (ICons x xs)) (evens (ICons x xs))) (ICons x xs)
  === eqK k (merge (ICons x (odds (itail xs))) ((odds . itail) (ICons x xs))) (ICons x xs)
  === eqK k (merge (ICons x ((odds . itail) xs)) (odds xs)) (ICons x xs)
  === eqK k (ICons x (merge (odds xs) (evens xs))) (ICons x xs)
  === eqK (k-1) (merge (odds xs) (evens xs)) xs
    ? _lemmaEvenOddK (k-1) xs
  *** QED

------------------------------------------------------------
-- Dafny classifies automatically calls as recursive and
--  co-recursive and excludes the second from termination checks.
--  Below we do the same thing manually by:
--  1. Marking functions that contain co-recursive calls lazy
--  2. Adding manual termination checks to recursive calls that
--    are inside lazy functions. (e.g. fivesUp).


{-@ lazy up @-}
{-@ up :: n:_ -> IStream {v:_| v >= n} @-}
up :: Int -> IStream Int
up n = n `ICons` up (n+1)


{-@ lazy fivesUp @-}
{-@ fivesUp :: n:_ -> IStream {v:_ | v >= n} @-}
fivesUp :: Int -> IStream Int
-- the first clause is not checked for termination in dafny.
fivesUp n | n `mod` 5 == 0 = n `ICons` fivesUp (n+1)
          | otherwise      =
-- only the second clause is checked (here we have to do it manually
--   with liquidAssert).
            liquidAssert (fivesUpTerm (n+1) < fivesUpTerm n)
                         $ fivesUp (n+1)

{-@ inline fivesUpTerm @-}
fivesUpTerm :: Int -> Int
fivesUpTerm n = 4 - ((n-1) `mod` 5)


{-@ reflect trueStream @-}
trueStream :: IStream a -> Bool
trueStream = trueStream . itail

{-@ assume dAxiom_trueStream :: x:_ -> (k:Nat -> {_trueStreamK k x})
                      -> {trueStream x} @-}
dAxiom_trueStream :: IStream a -> (Int -> Proof) -> Proof
dAxiom_trueStream _ _ = ()

{-@ reflect _trueStreamK @-}
{-@ _trueStreamK :: k:Nat -> _ -> Bool /[k] @-}
_trueStreamK :: Int -> IStream a -> Bool
_trueStreamK 0 _ = True
_trueStreamK k s = _trueStreamK (k-1) (itail s)

{-@ trueLemma :: s:_ -> {trueStream s} @-}
trueLemma :: IStream a -> Proof
-- trueLemma (ICons s ss)
--   =   trueStream (ICons s ss)
--   === (trueStream . itail) (ICons s ss)
--   === trueStream ss
--     ? trueLemma ss
--   *** QED
trueLemma s = dAxiom_trueStream s (\k -> _trueLemmaK k s)

{-@ _trueLemmaK :: k: Nat -> s:_ -> {_trueStreamK k s} @-}
_trueLemmaK :: Int -> IStream a -> Proof
_trueLemmaK 0 s = _trueStreamK 0 s *** QED
_trueLemmaK k (ICons s ss)
  =   _trueStreamK k (ICons s ss)
  === _trueStreamK (k-1) (itail (ICons s ss))
  === _trueStreamK  (k-1) ss
    ? _trueLemmaK (k-1) ss
  *** QED

-- falseLemma erroneously typechecks but when we translate
--    the proof to induction it successfully fails.
{-@ falseLemma :: s:_ -> {false} @-}
falseLemma :: IStream a -> Proof
falseLemma (ICons s ss)
  =  False ? falseLemma ss
  *** QED

-- code below will (fortunately) not typecheck without ignore.
-- That is because _falseLemmaK can not be proven for k == 0.
-- Note that we have to call the prefix method _falseLemmaK in the
--   inductive step. That is not true for every coinductive method.
--   If there was a call to a coinductive method that belongs to another
--   cluster (~not mutually recursive with the current one) then we would
--   leave the call as is.
{-@ ignore _falseLemmaK @-}
{-@ _falseLemmaK :: k:Nat -> s:_ -> {false} @-}
_falseLemmaK :: Int -> IStream a -> Proof
_falseLemmaK k (ICons s ss)
  | k <= 0 = ()
  | k >  0
  =   False ? _falseLemmaK (k-1) ss
  *** QED



{-@ reflect irepeat @-}
{-@ lazy irepeat @-}
irepeat x = x `ICons` irepeat x

{-@ lemmaRepeat :: x:_ -> {itail (irepeat x) = irepeat x} @-}
-- lemmaRepeat x
--   =   itail (irepeat x)
--   === itail (x `ICons` irepeat x)
--   === irepeat x
--   *** QED

lemmaRepeat x =
  dAxiom_eq (itail (irepeat x)) (irepeat x) (\k -> _lemmaRepeatK k x)

{-@ _lemmaRepeatK :: k:Nat -> x:_ -> {eqK k (itail (irepeat x)) (irepeat x)} @-}
_lemmaRepeatK k x | k == 0
  =   eqK 0 (itail xs) xs
  *** QED
  | otherwise
  =   eqK k (itail xs) xs
  === eqK k (itail (x `ICons` xs)) xs
  === eqK k xs xs
    ? lemmaEqKReflexive k xs
  *** QED
  where xs = irepeat x

---------------------------------------------------------
-- eqK properties for IStreams.

{-@ assume dAxiom_eq :: xs:_ -> ys:_
                     -> (k:Nat -> {eqK k xs ys}) -> {xs = ys} @-}
dAxiom_eq :: Eq a => IStream a -> IStream a -> (Int -> Proof) -> Proof
dAxiom_eq _ _ _ = ()

{-@ assume dAxiom_eq_r :: xs:_ -> ys:_ -> {v:Proof| xs = ys}
                       -> k:Nat -> {eqK k xs ys} @-}
dAxiom_eq_r :: Eq a => IStream a -> IStream a -> Proof -> Int -> Proof
dAxiom_eq_r _ _ _ _ = ()

{-@ reflect eqK @-}
{-@ eqK :: k: Nat -> _ -> _ -> _ @-}
eqK :: (Eq a) => Int -> IStream a -> IStream a -> Bool
eqK 0 _ _ = True
eqK k (ICons a as) (ICons b bs) = a == b && eqK (k-1) as bs

{-@ lemmaEqKReflexive :: k:Nat -> xs:_ -> {eqK k xs xs } @-}
lemmaEqKReflexive :: (Eq a) => Int -> IStream a -> Proof
lemmaEqKReflexive 0 xs     = eqK 0 xs xs *** QED
lemmaEqKReflexive k xxs@(ICons x xs)
  =   eqK k xxs xxs
  === ((x == x) && eqK (k-1) xs xs) ? lemmaEqKReflexive (k-1) xs
  *** QED

{-@ lemmaEqKCommutative :: k:Nat -> xs:_ -> ys:_
                        -> {eqK k xs ys = eqK k ys xs }
@-}
lemmaEqKCommutative :: (Eq a) => Int -> IStream a -> IStream a -> Proof
lemmaEqKCommutative 0 xs ys
  =   eqK 0 xs ys
  === True
  === eqK 0 ys xs
  *** QED
lemmaEqKCommutative k xxs@(ICons x xs) yys@(ICons y ys)
  =   eqK k xxs yys
  === ((x == y) && eqK (k-1) xs ys)
    ? lemmaEqKCommutative (k-1) xs ys
  === ((y == x) && eqK (k-1) ys xs)
  === eqK k yys xxs
  *** QED

{-@ lemmaEqKTransitive :: k:Nat -> xs:_
                       -> ys:{ys:_| eqK k xs ys}
                       -> zs:{zs:_| eqK k ys zs}
                       -> {eqK k xs zs}
@-}
lemmaEqKTransitive
    :: (Eq a)
    => Int
    -> IStream a
    -> IStream a
    -> IStream a
    -> Proof
lemmaEqKTransitive 0 xs ys zs
  =   eqK 0 xs zs
  === True
  *** QED
lemmaEqKTransitive k xxs@(ICons x xs) yys@(ICons y ys) zzs@(ICons z zs)
  =   (eqK k xxs yys && eqK k yys zzs)
  === ((x == y) && eqK (k-1) xs ys && (y==z) && eqK (k-1) ys zs)
    ? lemmaEqKTransitive (k-1) xs ys zs
  === ((x == z) && eqK (k-1) xs zs)
  === eqK k xxs zzs
  *** QED

------------------------------------------------------------
{-@ type Nat = {v:Int | v >= 0}@-}

{-@ reflect implies @-}
{-@ implies :: p:Bool -> q:Bool -> {v:_| v <=> (p => q)} @-}
implies False _ = True
implies _ True = True
implies _ _ = False

{-@ theoremFivesUpTerm :: n:{n:_| n mod 5 /=0}
                       -> {fivesUpTerm (n+1) < fivesUpTerm n} @-}
theoremFivesUpTerm :: Int -> Proof
theoremFivesUpTerm _ = ()
