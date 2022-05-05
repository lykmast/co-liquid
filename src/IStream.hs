{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
module IStream where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.Prelude
data IStream a = a :> IStream a
infixr 5 :>

{-@ measure ihead @-}
ihead (x :> _)  = x

{-@ measure itail @-}
itail (_ :> xs) = xs


{-@ reflect nneg @-}
nneg :: IStream Int -> Bool
nneg (x :> xs) = x >= 0 && nneg xs

-- pointwise product of streams
{-@ reflect mult @-}
mult :: IStream Int -> IStream Int -> IStream Int
mult (a :> as) (b :> bs) = a * b :> mult as bs

{-@ theoremNNegSquare :: a:IStream Int -> {nneg (mult a a)}@-}
theoremNNegSquare :: IStream Int -> ()
-- theoremNNegSquare (a :> as)
--   =   nneg (mult (a :> as) (a :> as))
--   === nneg (a * a :> mult as as)
--   === (a * a >= 0 && nneg (mult as as))
--     ? theoremNNegSquare as
--   *** QED
--
-- | The above theorem must be proven without co-recursion through
--    the prefix versions

theoremNNegSquare a =
  dAxiom_nneg (mult a a) (\k -> _theoremNNegSquareK k a)



{-@ reflect below @-}
below :: Ord a => IStream a -> IStream a -> Bool
below (x :> xs) (y :> ys)
  = x <= y && ((x == y) `implies` below xs ys )

{-@ theoremBelowSquare :: a:IStream Int -> {below a (mult a a)}@-}
-- theoremBelowSquare (a :> as)
--   =   below (a :> as) (mult (a :> as) (a :> as))
--   === below (a :> as) (a * a :> mult as as)
--   === (a <= a*a && ( (a == a*a) `implies` below as (mult as as)))
--     ? theoremBelowSquare as
--   *** QED

theoremBelowSquare :: IStream Int -> ()
theoremBelowSquare a = dAxiom_below a (mult a a)
                        (\k -> _theoremBelowSquareK k a)


{-@ reflect merge @-}
merge :: IStream a -> IStream a -> IStream a
merge (x :> xs) ys = x :> (merge ys xs)

{-@ reflect odds @-}
odds  :: IStream a -> IStream a
odds (x :> xs) = x :> (odds (itail xs))

{-@ reflect evens @-}
evens :: IStream a -> IStream a
evens = odds . itail

{-@ lemmaEvenOdd :: xs:_ -> {merge (odds xs) (evens xs) = xs} @-}
lemmaEvenOdd :: Eq a => IStream a -> Proof
-- lemmaEvenOdd (x :> xs)
--   =   merge (odds (x :> xs)) (evens (x :> xs))
--   === merge (x :> odds (itail xs)) ((odds . itail) (x :> xs))
--   === merge (x :> (odds . itail) xs) (odds xs)
--   === x :> merge (odds xs) (evens xs)
--     ? lemmaEvenOdd xs
--   === x :> xs
--   *** QED

lemmaEvenOdd xs = dAxiom_eq (merge (odds xs) (evens xs)) xs
                            (\k -> _lemmaEvenOddK k xs)
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
up n = n :> up (n+1)


{-@ lazy fivesUp @-}
{-@ fivesUp :: n:_ -> IStream {v:_ | v >= n} @-}
fivesUp :: Int -> IStream Int
-- the first clause is not checked for termination in dafny.
fivesUp n | n `mod` 5 == 0 = n :> fivesUp (n+1)
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

{-@ trueLemma :: s:_ -> {trueStream s} @-}
trueLemma :: IStream a -> Proof
-- trueLemma (s :> ss)
--   =   trueStream (s :> ss)
--   === (trueStream . itail) (s :> ss)
--   === trueStream ss
--     ? trueLemma ss
--   *** QED
trueLemma s = dAxiom_trueStream s (\k -> _trueLemmaK k s)

-- falseLemma erroneously typechecks but when we translate
--    the proof to induction it successfully fails.
{-@ falseLemma :: s:_ -> {false} @-}
falseLemma :: IStream a -> Proof
falseLemma (s :> ss)
  =  False ? falseLemma ss
  *** QED


{-@ reflect irepeat @-}
{-@ lazy irepeat @-}
irepeat x = x :> irepeat x

{-@ lemmaRepeat :: x:_ -> {itail (irepeat x) = irepeat x} @-}
-- lemmaRepeat x
--   =   itail (irepeat x)
--   === itail (x :> irepeat x)
--   === irepeat x
--   *** QED

lemmaRepeat x =
  dAxiom_eq (itail (irepeat x)) (irepeat x) (\k -> _lemmaRepeatK k x)

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
eqK k (a :> as) (b :> bs) = a == b && eqK (k-1) as bs

{-@ lemmaEqKReflexive :: k:Nat -> xs:_ -> {eqK k xs xs } @-}
lemmaEqKReflexive :: (Eq a) => Int -> IStream a -> Proof
lemmaEqKReflexive 0 xs     = eqK 0 xs xs *** QED
lemmaEqKReflexive k xxs@(x :> xs)
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
lemmaEqKCommutative k xxs@(x :> xs) yys@(y :> ys)
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
lemmaEqKTransitive k xxs@(x :> xs) yys@(y :> ys) zzs@(z :> zs)
  =   (eqK k xxs yys && eqK k yys zzs)
  === ((x == y) && eqK (k-1) xs ys && (y==z) && eqK (k-1) ys zs)
    ? lemmaEqKTransitive (k-1) xs ys zs
  === ((x == z) && eqK (k-1) xs zs)
  === eqK k xxs zzs
  *** QED

------------------------------------------------------------
-- coinductive to inductive proofs.

{-@ type Nat = {v:Int | v >= 0}@-}

{-@ assume dAxiom_trueStream :: x:_ -> (k:Nat -> {_trueStreamK k x})
                      -> {trueStream x} @-}
dAxiom_trueStream :: IStream a -> (Int -> Proof) -> Proof
dAxiom_trueStream _ _ = ()

{-@ reflect _trueStreamK @-}
{-@ _trueStreamK :: k:Nat -> _ -> Bool /[k] @-}
_trueStreamK :: Int -> IStream a -> Bool
_trueStreamK 0 _ = True
_trueStreamK k s = _trueStreamK (k-1) (itail s)

{-@ _trueLemmaK :: k: Nat -> s:_ -> {_trueStreamK k s} @-}
_trueLemmaK :: Int -> IStream a -> Proof
_trueLemmaK 0 s = _trueStreamK 0 s *** QED
_trueLemmaK k (s :> ss)
  =   _trueStreamK k (s :> ss)
  === _trueStreamK (k-1) (itail (s :> ss))
  === _trueStreamK  (k-1) ss
    ? _trueLemmaK (k-1) ss
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
_falseLemmaK k (s :> ss)
  | k <= 0 = ()
  | k >  0
  =   False ? _falseLemmaK (k-1) ss
  *** QED


{-@ assume dAxiom_below :: xs:_ -> ys:_ -> (k:Nat -> {_belowK k xs ys})
                        -> {below xs ys} @-}
dAxiom_below :: Ord a => IStream a -> IStream a -> (Int -> Proof) -> Proof
dAxiom_below _ _ _ = ()

{-@ reflect _belowK @-}
{-@ _belowK :: Nat -> _ -> _ -> _ @-}
_belowK :: Ord a => Int -> IStream a -> IStream a -> Bool
_belowK 0 _ _ = True
_belowK k (x :> xs) (y :> ys)
  = x <= y && ((x == y) `implies` _belowK (k-1) xs ys )

{-@ _theoremBelowSquareK :: k: Nat
                         -> a: IStream Int
                         -> {_belowK k a (mult a a)} @-}
_theoremBelowSquareK :: Int -> IStream Int -> ()
_theoremBelowSquareK 0 as
  =   _belowK 0 as (mult as as)
  *** QED
_theoremBelowSquareK k (a :> as)
  =   _belowK k (a :> as) (mult (a :> as) (a :> as))
  === _belowK k (a :> as) (a * a :> mult as as)
  === (a <= a*a &&
        ((a == a*a) `implies` _belowK (k-1) as (mult as as)))
    ? _theoremBelowSquareK (k-1) as
  *** QED

{-@ _lemmaEvenOddK :: k: Nat -> xs:_ -> {eqK k (merge (odds xs) (evens xs)) xs} @-}
_lemmaEvenOddK :: (Eq a) => Int -> IStream a -> Proof
_lemmaEvenOddK 0 s
  =   eqK 0 (merge (odds s) (evens s)) s
  *** QED
_lemmaEvenOddK k (x :> xs)
  =   eqK k (merge (odds (x :> xs)) (evens (x :> xs))) (x :> xs)
  === eqK k (merge (x :> (odds (itail xs))) ((odds . itail) (x :> xs)))
            (x :> xs)
  === eqK k (merge (x :> (odds . itail) xs) (odds xs)) (x :> xs)
  === eqK k (x :> merge (odds xs) (evens xs)) (x :> xs)
  === eqK (k-1) (merge (odds xs) (evens xs)) xs
    ? _lemmaEvenOddK (k-1) xs
  *** QED

{-@ _lemmaRepeatK :: k:Nat -> x:_ -> {eqK k (itail (irepeat x)) (irepeat x)} @-}
_lemmaRepeatK k x | k == 0
  =   eqK 0 (itail xs) xs
  *** QED
  | otherwise
  =   eqK k (itail xs) xs
  === eqK k (itail (x :> xs)) xs
  === eqK k xs xs
    ? lemmaEqKReflexive k xs
  *** QED
  where xs = irepeat x

{-@ assume dAxiom_nneg :: xs:IStream Int
                       -> (k:Nat -> {nnegK k xs}) -> {nneg xs} @-}
dAxiom_nneg :: IStream Int -> (Int -> Proof) -> Proof
dAxiom_nneg _ _ = ()

{-@ reflect nnegK @-}
{-@ nnegK :: Nat -> _ -> _ @-}
nnegK :: Int -> IStream Int -> Bool
nnegK 0 _ = True
nnegK k (x :> xs) = x >= 0 && nnegK (k-1) xs

{-@ _theoremNNegSquareK :: k:Nat -> a:IStream Int
                        -> {nnegK k (mult a a)} @-}
_theoremNNegSquareK :: Int -> IStream Int -> ()
_theoremNNegSquareK 0 a = nnegK 0 (mult a a) *** QED
_theoremNNegSquareK k (a :> as)
  =   nnegK k (mult (a :> as) (a :> as))
  === nnegK k (a * a :> mult as as)
  === (a * a >= 0 && nnegK (k-1) (mult as as))
    ? _theoremNNegSquareK (k-1) as
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
