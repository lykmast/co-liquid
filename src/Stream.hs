{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
module Stream where

import Language.Haskell.Liquid.ProofCombinators hiding((***), QED)
import Language.Haskell.Liquid.Prelude
data Stream a = a :> Stream a
infixr 5 :>

{-@ measure hd @-}
hd (x :> _ ) = x

{-@ measure tl @-}
tl (_ :> xs) = xs


{-@ reflect nneg @-}
nneg :: Stream Int -> Bool
nneg (x :> xs) = x >= 0 && nneg xs

-- pointwise product of streams
{-@ reflect mult @-}
mult :: Stream Int -> Stream Int -> Stream Int
mult (a :> as) (b :> bs) = a * b :> mult as bs

{-@ theoremNNegSquare :: a:Stream Int -> {nneg (mult a a)}@-}
theoremNNegSquare :: Stream Int -> ()
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
below :: Ord a => Stream a -> Stream a -> Bool
below (x :> xs) (y :> ys)
  = x <= y && ((x == y) `implies` below xs ys )

{-@ theoremBelowSquare :: a:Stream Int -> {below a (mult a a)}@-}
-- theoremBelowSquare (a :> as)
--   =   below (a :> as) (mult (a :> as) (a :> as))
--   === below (a :> as) (a * a :> mult as as)
--   === (a <= a*a && ( (a == a*a) `implies` below as (mult as as)))
--     ? theoremBelowSquare as
--   *** QED

theoremBelowSquare :: Stream Int -> ()
theoremBelowSquare a = dAxiom_below a (mult a a)
                        (\k -> _theoremBelowSquareK k a)


{-@ reflect merge @-}
merge :: Stream a -> Stream a -> Stream a
merge (x :> xs) ys = x :> (merge ys xs)

{-@ reflect odds @-}
odds  :: Stream a -> Stream a
odds (x :> xs) = x :> (odds (tl xs))

{-@ reflect evens @-}
evens :: Stream a -> Stream a
evens = odds . tl

{-@ lemmaEvenOdd :: xs:_ -> {merge (odds xs) (evens xs) = xs} @-}
lemmaEvenOdd :: Eq a => Stream a -> Proof
-- lemmaEvenOdd (x :> xs)
--   =   merge (odds (x :> xs)) (evens (x :> xs))
--   === merge (x :> odds (tl xs)) ((odds . tl) (x :> xs))
--   === merge (x :> (odds . tl) xs) (odds xs)
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
{-@ up :: n:_ -> Stream {v:_| v >= n} @-}
up :: Int -> Stream Int
up n = n :> up (n+1)


{-@ lazy fivesUp @-}
{-@ fivesUp :: n:_ -> Stream {v:_ | v >= n} @-}
fivesUp :: Int -> Stream Int
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
trueStream :: Stream a -> Bool
trueStream = trueStream . tl

{-@ trueLemma :: s:_ -> {trueStream s} @-}
trueLemma :: Stream a -> Proof
-- trueLemma (s :> ss)
--   =   trueStream (s :> ss)
--   === (trueStream . tl) (s :> ss)
--   === trueStream ss
--     ? trueLemma ss
--   *** QED
trueLemma s = dAxiom_trueStream s (\k -> _trueLemmaK k s)

-- falseLemma erroneously typechecks but when we translate
--    the proof to induction it successfully fails.
{-@ falseLemma :: s:_ -> {false} @-}
falseLemma :: Stream a -> Proof
falseLemma (s :> ss)
  =  False ? falseLemma ss
  *** QED


{-@ reflect irepeat @-}
{-@ lazy irepeat @-}
irepeat x = x :> irepeat x

{-@ lemmaRepeat :: x:_ -> {tl (irepeat x) = irepeat x} @-}
-- lemmaRepeat x
--   =   tl (irepeat x)
--   === tl (x :> irepeat x)
--   === irepeat x
--   *** QED

lemmaRepeat x =
  dAxiom_eq (tl (irepeat x)) (irepeat x) (\k -> _lemmaRepeatK k x)

---------------------------------------------------------
-- eqK properties for Streams.

{-@ assume dAxiom_eq :: xs:_ -> ys:_
                     -> (k:Nat -> {eqK k xs ys}) -> {xs = ys} @-}
dAxiom_eq :: Eq a => Stream a -> Stream a -> (Int -> Proof) -> Proof
dAxiom_eq _ _ _ = ()

{-@ assume dAxiom_eq_r :: xs:_ -> ys:_ -> {v:Proof| xs = ys}
                       -> k:Nat -> {eqK k xs ys} @-}
dAxiom_eq_r :: Eq a => Stream a -> Stream a -> Proof -> Int -> Proof
dAxiom_eq_r _ _ _ _ = ()

{-@ reflect eqK @-}
{-@ eqK :: k: Nat -> _ -> _ -> _ @-}
eqK :: (Eq a) => Int -> Stream a -> Stream a -> Bool
eqK 0 _ _ = True
eqK k (a :> as) (b :> bs) = a == b && eqK (k-1) as bs

{-@ lemmaEqKReflexive :: k:Nat -> xs:_ -> {eqK k xs xs } @-}
lemmaEqKReflexive :: (Eq a) => Int -> Stream a -> Proof
lemmaEqKReflexive 0 xs     = eqK 0 xs xs *** QED
lemmaEqKReflexive k xxs@(x :> xs)
  =   eqK k xxs xxs
  === ((x == x) && eqK (k-1) xs xs) ? lemmaEqKReflexive (k-1) xs
  *** QED

{-@ lemmaEqKCommutative :: k:Nat -> xs:_ -> ys:_
                        -> {eqK k xs ys = eqK k ys xs }
@-}
lemmaEqKCommutative :: (Eq a) => Int -> Stream a -> Stream a -> Proof
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
    -> Stream a
    -> Stream a
    -> Stream a
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
dAxiom_trueStream :: Stream a -> (Int -> Proof) -> Proof
dAxiom_trueStream _ _ = ()

{-@ reflect _trueStreamK @-}
{-@ _trueStreamK :: k:Nat -> _ -> Bool /[k] @-}
_trueStreamK :: Int -> Stream a -> Bool
_trueStreamK 0 _ = True
_trueStreamK k s = _trueStreamK (k-1) (tl s)

{-@ _trueLemmaK :: k: Nat -> s:_ -> {_trueStreamK k s} @-}
_trueLemmaK :: Int -> Stream a -> Proof
_trueLemmaK 0 s = _trueStreamK 0 s *** QED
_trueLemmaK k (s :> ss)
  =   _trueStreamK k (s :> ss)
  === _trueStreamK (k-1) (tl (s :> ss))
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
_falseLemmaK :: Int -> Stream a -> Proof
_falseLemmaK k (s :> ss)
  | k <= 0 = ()
  | k >  0
  =   False ? _falseLemmaK (k-1) ss
  *** QED


{-@ assume dAxiom_below :: xs:_ -> ys:_ -> (k:Nat -> {_belowK k xs ys})
                        -> {below xs ys} @-}
dAxiom_below :: Ord a => Stream a -> Stream a -> (Int -> Proof) -> Proof
dAxiom_below _ _ _ = ()

{-@ reflect _belowK @-}
{-@ _belowK :: Nat -> _ -> _ -> _ @-}
_belowK :: Ord a => Int -> Stream a -> Stream a -> Bool
_belowK 0 _ _ = True
_belowK k (x :> xs) (y :> ys)
  = x <= y && ((x == y) `implies` _belowK (k-1) xs ys )

{-@ _theoremBelowSquareK :: k: Nat
                         -> a: Stream Int
                         -> {_belowK k a (mult a a)} @-}
_theoremBelowSquareK :: Int -> Stream Int -> ()
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
_lemmaEvenOddK :: (Eq a) => Int -> Stream a -> Proof
_lemmaEvenOddK 0 s
  =   eqK 0 (merge (odds s) (evens s)) s
  *** QED
_lemmaEvenOddK k xxs@(x :> xs)
  =
  merge (odds xxs) (evens xxs)
  === merge (x :> odds (tl xs))
            ((odds . tl) xxs)
  === merge (x :> (odds . tl) xs) (odds xs)
  === x :> merge (odds xs) (evens xs)
    ? _lemmaEvenOddK (k-1) xs
  =#= k # x :> xs
  *** QED


{-@ _lemmaRepeatK :: k:Nat -> x:_ -> {eqK k (tl (irepeat x)) (irepeat x)} @-}
_lemmaRepeatK k x | k == 0
  =   eqK 0 (tl xs) xs
  *** QED
  | otherwise
  =   eqK k (tl xs) xs
  === eqK k (tl (x :> xs)) xs
  === eqK k xs xs
    ? lemmaEqKReflexive k xs
  *** QED
  where xs = irepeat x

{-@ assume dAxiom_nneg :: xs:Stream Int
                       -> (k:Nat -> {nnegK k xs}) -> {nneg xs} @-}
dAxiom_nneg :: Stream Int -> (Int -> Proof) -> Proof
dAxiom_nneg _ _ = ()

{-@ reflect nnegK @-}
{-@ nnegK :: Nat -> _ -> _ @-}
nnegK :: Int -> Stream Int -> Bool
nnegK 0 _ = True
nnegK k (x :> xs) = x >= 0 && nnegK (k-1) xs

{-@ _theoremNNegSquareK :: k:Nat -> a:Stream Int
                        -> {nnegK k (mult a a)} @-}
_theoremNNegSquareK :: Int -> Stream Int -> ()
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
------------------------------------------------------------

infix 0 ***

data QED = QED
_ *** QED = ()

infixr 1 #
(#) = ($)

infix 2 =#=
{-@ (=#=) :: Eq a => x:Stream a -> k:{Nat | 0 < k } -> y:{Stream a | eqK (k-1) (tl x) (tl y) && hd x == hd y } -> {v:Stream a | eqK k x y && v == x } @-}
(=#=) :: Eq a => Stream a -> Int -> Stream a -> Stream a
(=#=)  xxs@(x :> xs) k yys@(y :> ys) =
  xxs ? (eqK k xxs yys === (x == y && eqK (k-1) xs ys) *** QED)
