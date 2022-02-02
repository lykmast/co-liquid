{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--higherorder" @-}

module Filter where

-- The following come from dafny-lang/dafny/Test/dafny3/Filter.dfy
-- in github.
-- They are also referenced in "Co-induction Simply".

import IStream
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.Prelude(liquidAssert)
import Prelude hiding(filter)

{-@ reflect tailN @-}
{-@ tailN :: Nat -> _ -> _ @-}
tailN :: Int -> IStream a -> IStream a
tailN n s
  | n == 0    = s
  | otherwise = tailN (n-1) (itail s)

{-@ reflect headN @-}
{-@ headN :: Nat -> _ -> _ @-}
headN :: Int -> IStream a -> a
headN n = ihead . tailN n
{-@ reflect mem @-}
mem :: Eq a => a -> IStream a -> Bool
mem v (ICons x xs) = x == v || mem v xs

{-@ reflect isSubStream @-}
isSubStream :: Eq a => IStream a -> IStream a -> Bool
isSubStream (ICons x xs) ys = mem x ys && isSubStream xs ys

{-@ lemmaInTail :: e:_ -> {xs:_ | mem e (itail xs)}  -> {mem e xs}  @-}
lemmaInTail :: Eq a => a -> IStream a -> Proof
lemmaInTail v xxs@(ICons x xs)
  =   v `mem` xs
  === v `mem` xxs
  *** QED

{-@ lemmaTailSubStream :: s:_
                       -> {u:_| isSubStream s (itail u)}
                       -> {isSubStream s u}
@-}
lemmaTailSubStream :: Eq a => IStream a -> IStream a -> Proof
lemmaTailSubStream sss@(ICons s ss) uus@(ICons u us)
  =   sss `isSubStream` us
    ? lemmaInTail s uus
    ? lemmaTailSubStream ss uus
  === sss `isSubStream` uus
  *** QED

type Pred a = a -> Bool

{-@ reflect allP @-}
allP :: Pred a -> IStream a -> Bool
allP p (ICons x xs) = p x && allP p xs

{-@ lemmaInAllP :: p:_
                -> {xs:_| allP p xs}
                -> {x:_ | mem  x xs}
                -> {p x}
@-}
lemmaInAllP :: Eq a => Pred a -> IStream a -> a -> Proof
lemmaInAllP p xxs@(ICons x xs) e
  | e == x = allP p xxs === p e *** QED
  | e /= x = (allP p xxs && e `mem` xxs) ? lemmaInAllP p xs e *** QED

{-@ reflect isAnother @-}
isAnother :: Pred a -> IStream a -> Bool
isAnother p (ICons x xs) = p x || isAnother p xs

{-@ reflect alwaysAnother @-}
alwaysAnother :: Pred a -> IStream a -> Bool
alwaysAnother p xxs@(ICons x xs) = isAnother p xxs && alwaysAnother p xs

{-@ lemmaTailAlwaysAnother :: p:_
                           -> {xs:_| alwaysAnother p xs}
                           -> {alwaysAnother p (itail xs)}
@-}
lemmaTailAlwaysAnother :: Pred a -> IStream a -> Proof
lemmaTailAlwaysAnother p xxs@(ICons x xs)
  =   alwaysAnother p xxs
  === alwaysAnother p xs
  *** QED

{-@ lemmaAllImpliesAlwaysAnother :: p:_
                                 -> {xs:_| allP p xs}
                                 -> {alwaysAnother p xs}
@-}
lemmaAllImpliesAlwaysAnother :: Pred a -> IStream a -> Proof
lemmaAllImpliesAlwaysAnother p xxs@(ICons x xs)
  =   allP p xxs
  -- === (p x && allP p xs)
  === (isAnother p xxs && allP p xs)
    ? lemmaAllImpliesAlwaysAnother p xs
  -- === (isAnother p xxs && alwaysAnother p xs)
  === alwaysAnother p xxs
  *** QED

{-@ reflect next @-}
{-@ next :: p:_
         -> xs:_
         -> Nat @-}-- {n:Nat| p (headN n xs) }@-}
next :: Pred a -> IStream a -> Int
next p xxs@(ICons x xs) | p x       = 0
                        | otherwise = 1 + next p xs


{-@ lemmaNextIsP :: p:_
                 -> {xs:_| alwaysAnother p xs}
                 -> {p (headN (next p xs) xs)}
@-}
lemmaNextIsP :: Pred a -> IStream a -> Proof
lemmaNextIsP p xxs@(ICons x xs)
  | p x
  =   p (headN (next p xxs) xxs)
  === p (headN 0 xxs)
  === p ((ihead . tailN 0) xxs)
  *** QED
  | otherwise
  =   p (headN (next p xxs) xxs)
  === p (headN (1 + next p xs) xxs)
  === p ((ihead . tailN (1 + next p xs)) xxs)
  === p ((ihead . tailN (next p xs)) xs)
  === p (headN (next p xs) xs)
    ? lemmaTailAlwaysAnother p xxs
    ? lemmaNextIsP p xs
  *** QED

{-@ lemmaNoSmallerP :: p:_
                    -> s:_
                    -> {n:Nat| n < next p s}
                    -> {not (p (headN n s))}
@-}
lemmaNoSmallerP :: Pred a -> IStream a -> Int -> Proof
lemmaNoSmallerP p xxs@(ICons x xs) n
  | next p xxs == 0 = () --false precondition
  | n == 0
  =   not (p (headN n xxs))
  === not (p ((ihead . tailN n) xxs))
  -- === not (p x)
  -- === next p xxs /= 0
  *** QED
  | otherwise
  =   not (p (headN n xxs))
  === not (p ((ihead . tailN n) xxs))
  === not (p ((ihead . tailN (n-1)) xs))
  === not (p (headN (n-1) xs))
    ? lemmaNoSmallerP p xs (n-1)
  *** QED

{-@ nextLemma :: p:_
              -> {xs:_| not (p (ihead xs)) }
              -> {next p (itail xs) >= 0 && next p xs > next p (itail xs)}
@-}
nextLemma :: Pred a -> IStream a -> Proof
nextLemma p xxs@(ICons _ xs)
  =   next p xxs    > next p xs
  === 1 + next p xs > next p xs
  *** QED


-- The function filter' uses some helper lemmas (to prove
--   termination and refinement properties) which cannot (?) be
--   reflected. In order to have filter reflected, we removed helper
--   lemmas from its body.

{-@ lazy filter @-}
{-@ reflect filter @-}
{-@ assume filter :: p:_
                  -> {xs:_| alwaysAnother p xs}
                  -> {v:_| allP p v} @-}
filter :: Pred a -> IStream a -> IStream a
filter p xxs | p x       = x `ICons` filter p xs
             | otherwise = filter p xs
             where x  = ihead xxs
                   xs = itail xxs

{-@ lazy filter' @-}
{-@ filter' :: p:_
           -> {xs:_|alwaysAnother p xs}
           -> {v:_| allP p v }
@-}
filter' :: Pred a -> IStream a -> IStream a
filter' p xxs
  | p x
  = x `ICons` filter' p (xs ? lemmaTailAlwaysAnother p xxs)
      ? lemmaAllHelp p x (filter' p xs)
  | otherwise
  = liquidAssert (next p xs < next p xxs ? nextLemma p xxs)
     $ filter' p (xs ? lemmaTailAlwaysAnother p xxs)

  where x  = ihead xxs
        xs = itail xxs

{-@ lemmaAllHelp :: p:_
                 -> {x:_| p x}
                 -> {xs:_| allP p xs}
                 -> {allP p (ICons x xs)}
@-}
lemmaAllHelp :: Pred a -> a -> IStream a -> Proof
lemmaAllHelp p x xs
  =   allP p (ICons x xs)
  === (p x && allP p xs)
  *** QED

{-@ lemmaFilterIsSubStream :: p:_
                           -> {xs:_|alwaysAnother p xs}
                           -> {isSubStream (filter p xs) xs}
@-}
lemmaFilterIsSubStream :: Eq a => Pred a -> IStream a -> Proof
lemmaFilterIsSubStream p xxs@(ICons x xs)
  | p x
  =   isSubStream (filter p xxs) xxs
  === isSubStream (x `ICons` filter p xs) xxs
  === (mem x xxs && isSubStream (filter p xs) xxs)
    ? lemmaTailAlwaysAnother p xxs
    ? lemmaFilterIsSubStream p xs
    ? lemmaTailSubStream (filter p xs) xxs
  *** QED
  | otherwise
  =   isSubStream (filter p xxs) xxs
  === isSubStream (filter p xs) xxs
    ? lemmaTailAlwaysAnother p xxs
    ? lemmaFilterIsSubStream p xs
    ? lemmaTailSubStream (filter p xs) xxs
  *** QED

--------------- orderings --------------

type OrdF a = a -> Int

{-@ reflect increasing @-}
increasing :: OrdF a -> IStream a -> Bool
increasing ord (ICons x xs) =
  ord x < ord (ihead xs) && increasing ord xs

{-@ reflect incrFrom @-}
incrFrom :: OrdF a -> Int -> IStream a -> Bool
incrFrom ord low (ICons x xs) =
  low <= ord x  && incrFrom ord (ord x + 1) xs


{-@ lemmaIncr0 :: ord:_
               -> low:_
               -> {xs:_| incrFrom ord low xs}
               -> {increasing ord xs}
@-}
lemmaIncr0 :: OrdF a -> Int -> IStream a -> Proof
lemmaIncr0 ord low xxs@(ICons x xs)
  =   incrFrom ord low xxs
  === incrFrom ord (ord x + 1) xs
  === (ord x + 1 <= ord x'
        && incrFrom ord (ord x + 1) xs)
  === (ord x < ord (ihead xs)
        && incrFrom ord (ord x + 1) xs)
    ? lemmaIncr0 ord (ord x + 1) xs
  === (ord x < ord (ihead xs) && increasing ord xs)
  === increasing ord xxs
  *** QED
  where ICons x' xs' = xs
{-@ lemmaIncrLoose :: ord:_
                   -> low:_
                   -> {lower:_| lower <= low}
                   -> {xs:_| incrFrom ord low xs}
                   -> {incrFrom ord lower xs}
@-}
lemmaIncrLoose :: OrdF a -> Int -> Int -> IStream a -> Proof
lemmaIncrLoose ord low lower xxs@(ICons x xs)
  =   incrFrom ord low xxs
  === (low   <= ord x && incrFrom ord (ord x + 1) xs)
  === (lower <= ord x && incrFrom ord (ord x + 1) xs)
  === incrFrom ord lower xxs
  *** QED

{-@ lemmaIncr1 :: ord:_
               -> {xs:_| increasing ord xs}
               -> {incrFrom ord (ord (ihead xs)) xs}
@-}
lemmaIncr1 :: OrdF a -> IStream a -> Proof
lemmaIncr1 ord xxs@(ICons x xs)
  =   increasing ord xxs
  === (ord x < ord x' && increasing ord xs)
    ? lemmaIncr1 ord xs
  === (ord x + 1 <= ord x' && incrFrom ord (ord x') xs)
    ? lemmaIncrLoose ord (ord x') (ord x + 1) xs
  === (ord x <= ord x && incrFrom ord (ord x + 1) xs)
  === incrFrom ord (ord x) xxs
  *** QED
  where ICons x' xs' = xs

{-@ lemmaFilterPreservesIncrFrom :: ord:_
                                 -> p:_
                                 -> low:_
                                 -> {xs:_ |  incrFrom ord low xs
                                          && alwaysAnother p xs
                                          && low <= ord (ihead xs)}
                                 -> {incrFrom ord low (filter p xs)}
@-}
lemmaFilterPreservesIncrFrom
  :: OrdF a
  -> Pred a
  -> Int
  -> IStream a
  -> Proof
lemmaFilterPreservesIncrFrom ord p low xxs@(ICons x xs)
  | p x
  =   incrFrom ord low xxs
  === (low <= ord x && ord x + 1 <= ord x'
        && incrFrom ord (ord x + 1) xs)
    ? lemmaTailAlwaysAnother p xxs
    ? lemmaFilterPreservesIncrFrom ord p (ord x + 1) xs
  === incrFrom ord low (x `ICons` filter p xs)
  === incrFrom ord low (filter p xxs)
  *** QED

  | otherwise
  =   incrFrom ord low xxs
  === incrFrom ord (ord x + 1) xs
    ? lemmaIncrLoose ord (ord x + 1) low xs
  === incrFrom ord low xs
    ? lemmaTailAlwaysAnother p xxs
    ? lemmaFilterPreservesIncrFrom ord p low xs
  === incrFrom ord low (filter p xxs)
  *** QED
  where (ICons x' xs') = xs


-- This is not an inductive or co-inductive proof so there is not
--   a prefix version.
{-@ theoremFilterPreservesOrdering :: ord:_
                                   -> p:_
                                   -> {xs:_|  increasing ord xs
                                           && alwaysAnother p xs}
                                   -> {increasing ord (filter p xs)}
@-}
theoremFilterPreservesOrdering :: OrdF a -> Pred a -> IStream a -> Proof
theoremFilterPreservesOrdering ord p xxs@(ICons x xs)
  =   increasing ord xxs
    ? lemmaIncr1 ord xxs
  === incrFrom ord (ord x) xxs
    ? lemmaTailAlwaysAnother p xxs
    ? lemmaFilterPreservesIncrFrom ord p (ord x) xxs
  === incrFrom ord (ord x) (filter p xxs)
    ? lemmaIncr0 ord (ord x) (filter p xxs)
  === increasing ord (filter p xxs)
  *** QED
  where (ICons x' xs') = xs
------------------------------------------------------------
-- coinductive to inductive proofs.

{-@ reflect _isSubStreamK @-}
{-@ _isSubStreamK :: Nat -> _ -> _ -> _ @-}
_isSubStreamK :: Eq a => Int -> IStream a -> IStream a -> Bool
_isSubStreamK 0 _ _ = True
_isSubStreamK k (ICons x xs) ys = mem x ys && _isSubStreamK (k-1) xs ys


-- Take care that this is not the desugaring of lemmmaTailSubStream
--   as it uses a prefix predicate in the precondition. It is a stricter
--   property that is useful for FilterIsSubStream.
{-@ lemmaTailSubStreamK :: k:Nat
                         -> s:_
                         -> {u:_| _isSubStreamK k s (itail u)}
                         -> {_isSubStreamK k s u}
@-}
lemmaTailSubStreamK :: Eq a => Int -> IStream a -> IStream a -> Proof
lemmaTailSubStreamK 0 s u
  =   _isSubStreamK 0 s u *** QED
lemmaTailSubStreamK k sss@(ICons s ss) uus@(ICons u us)
  =   _isSubStreamK k sss us
    ? lemmaInTail s uus
    ? lemmaTailSubStreamK (k-1) ss uus
  === _isSubStreamK k sss uus
  *** QED

{-@ reflect _allPK @-}
{-@ _allPK :: Nat -> _ -> _ -> _ @-}
_allPK :: Int -> Pred a -> IStream a -> Bool
_allPK 0 _ _            = True
_allPK k p (ICons x xs) = p x && _allPK (k-1) p xs


{-@ reflect _isAnotherK @-}
{-@ _isAnotherK :: Nat -> _ -> _ -> _ @-}
_isAnotherK :: Int -> Pred a -> IStream a -> Bool
_isAnotherK 0 _ _            = True
_isAnotherK k p (ICons x xs) = p x || _isAnotherK (k-1) p xs

{-@ reflect _alwaysAnotherK @-}
{-@ _alwaysAnotherK :: Nat -> _ -> _ -> _ @-}
_alwaysAnotherK :: Int -> Pred a -> IStream a -> Bool
_alwaysAnotherK 0 _ _ = True
_alwaysAnotherK k p xxs@(ICons x xs) =
  _isAnotherK k p xxs && _alwaysAnotherK (k-1) p xs

{-@ _lemmaAllImpliesAlwaysAnotherK :: k:Nat
                                   -> p:_
                                   -> {xs:_| _allPK k p xs}
                                   -> {_alwaysAnotherK k p xs}
@-}
_lemmaAllImpliesAlwaysAnotherK :: Int -> Pred a -> IStream a -> Proof
_lemmaAllImpliesAlwaysAnotherK 0 p xs
  =   _alwaysAnotherK 0 p xs *** QED
_lemmaAllImpliesAlwaysAnotherK k p xxs@(ICons x xs)
  =   _allPK k p xxs
  -- === (p x && _allPK (k-1) p xs)
  === (_isAnotherK k p xxs && _allPK (k-1) p xs)
    ? _lemmaAllImpliesAlwaysAnotherK (k-1) p xs
  -- === (_isAnotherK k p xxs && _alwaysAnotherK (k-1) p xs)
  === _alwaysAnotherK k p xxs
  *** QED


{-@ _lemmaTailAlwaysAnotherK :: {k:Nat| k>0}
                             -> p:_
                             -> {xs:_| _alwaysAnotherK k p xs}
                             -> {_alwaysAnotherK (k-1) p (itail xs)}
@-}
_lemmaTailAlwaysAnotherK :: Int -> Pred a -> IStream a -> Proof
_lemmaTailAlwaysAnotherK 1 p xxs@(ICons x xs)
  =   _alwaysAnotherK 1 p xxs
  === _alwaysAnotherK 0 p xs
  *** QED
_lemmaTailAlwaysAnotherK k p xxs@(ICons x xs)
  =   _alwaysAnotherK k     p xxs
  === _alwaysAnotherK (k-1) p xs
  *** QED

{-@ _lemmaFilterIsSubStreamK :: k:Nat
                             -> p:_
                             -> {xs:_| alwaysAnother p xs}
                             -> {_isSubStreamK k (filter p xs) xs}
@-}
_lemmaFilterIsSubStreamK :: Eq a => Int -> Pred a -> IStream a -> Proof
_lemmaFilterIsSubStreamK k p xxs@(ICons x xs)
  | k == 0 = _isSubStreamK 0 (filter p xxs) xxs *** QED
  | p x
  =   _isSubStreamK k (filter p xxs) xxs
  === _isSubStreamK k (x `ICons` filter p xs) xxs
  === (mem x xxs && _isSubStreamK (k-1) (filter p xs) xxs)
    ? lemmaTailAlwaysAnother p xxs
    ? _lemmaFilterIsSubStreamK (k-1) p xs
    ? lemmaTailSubStreamK (k-1) (filter p xs) xxs
  *** QED
  | otherwise
  =   _isSubStreamK k (filter p xxs) xxs
  === _isSubStreamK k (filter p xs)  xxs
    ? lemmaTailAlwaysAnother p xxs
    ? _lemmaFilterIsSubStreamK k p xs
    ? lemmaTailSubStreamK k (filter p xs) xxs
  *** QED


{-@ reflect _increasingK @-}
{-@ _increasingK :: Nat -> _ -> _ -> _ @-}
_increasingK :: Int -> OrdF a -> IStream a -> Bool
-- this is True for k = 1 because ordering of one element is trivial
_increasingK k _ _ | k <= 1 = True
_increasingK k ord (ICons x xs) =
  ord x < ord (ihead xs) && _increasingK (k-1) ord xs

{-@ reflect _incrFromK @-}
{-@ _incrFromK :: Nat -> _ -> _ -> _ -> _ @-}
_incrFromK :: Int -> OrdF a -> Int -> IStream a -> Bool
_incrFromK 0 _ _ _ = True
_incrFromK k ord low (ICons x xs) =
  low <= ord x  && _incrFromK (k-1) ord (ord x + 1) xs


{-@ _lemmaIncr0K :: k:Nat
                 -> ord:_
                 -> low:_
                 -> {xs:_| _incrFromK k ord low xs}
                 -> {_increasingK k ord xs}
@-}
_lemmaIncr0K :: Int -> OrdF a -> Int -> IStream a -> Proof
_lemmaIncr0K k ord _ xxs
  | k <= 1
  =   _increasingK k ord xxs
  *** QED
_lemmaIncr0K k ord low xxs@(ICons x xs)
  =   _incrFromK k ord low xxs
  === _incrFromK (k-1) ord (ord x + 1) xs
  === (ord x + 1 <= ord x'
        && _incrFromK (k-1) ord (ord x + 1) xs)
  === (ord x < ord (ihead xs)
        && _incrFromK (k-1) ord (ord x + 1) xs)
    ? _lemmaIncr0K (k-1) ord (ord x + 1) xs
  === (ord x < ord (ihead xs) && _increasingK (k-1) ord xs)
  === _increasingK k ord xxs
  *** QED
  where ICons x' xs' = xs

{-@ _lemmaIncrLooseK :: k:Nat
                     -> ord:_
                     -> low:_
                     -> {lower:_| lower <= low}
                     -> {xs:_| _incrFromK k ord low xs}
                     -> {_incrFromK k ord lower xs}
@-}
_lemmaIncrLooseK :: Int -> OrdF a -> Int -> Int -> IStream a -> Proof
_lemmaIncrLooseK 0 ord _ lower xxs@(ICons x xs)
  =   _incrFromK 0 ord lower xxs
  *** QED
_lemmaIncrLooseK k ord low lower xxs@(ICons x xs)
  =   _incrFromK k ord low xxs
  === (low   <= ord x && _incrFromK (k-1) ord (ord x + 1) xs)
  === (lower <= ord x && _incrFromK (k-1) ord (ord x + 1) xs)
  === _incrFromK k ord lower xxs
  *** QED

{-@ _lemmaIncr1K :: k:Nat
                 -> ord:_
                 -> {xs:_| _increasingK k ord xs}
                 -> {_incrFromK k ord (ord (ihead xs)) xs}
@-}
_lemmaIncr1K :: Int -> OrdF a -> IStream a -> Proof
_lemmaIncr1K 0 ord xxs@(ICons x xs)
  =   _incrFromK 0 ord (ord x) xxs
  *** QED
_lemmaIncr1K 1 ord xxs@(ICons x xs)
  =   _incrFromK 1 ord (ord x) xxs
  === (ord x <= ord x && _incrFromK 0 ord (ord x + 1) xs)
  *** QED
_lemmaIncr1K k ord xxs@(ICons x xs)
  =   _increasingK k ord xxs
  === (ord x < ord x' && _increasingK (k-1) ord xs)
    ? _lemmaIncr1K (k-1) ord xs
  === (ord x + 1 <= ord x' && _incrFromK (k-1) ord (ord x') xs)
    ? _lemmaIncrLooseK (k-1) ord (ord x') (ord x + 1) xs
  === (ord x <= ord x && _incrFromK (k-1) ord (ord x + 1) xs)
  === _incrFromK k ord (ord x) xxs
  *** QED
  where ICons x' xs' = xs


-- Even though there is an inductive call (in the `not p x` branch)
--   which does not decrease k but LH does not throw a termination
--   error. This could be because we recurse in a structurally smaller
--   lazy list (xs = tail xxs). Not sure that this is sound. In the
--   Dafny version it uses `next p xs` as a termination metric, which
--   I have added manually with a liquidAssert.
{-@ _lemmaFilterPreservesIncrFromK :: k:Nat
                                   -> ord:_
                                   -> p:_
                                   -> low:_
                                   -> {xs:_ |  incrFrom ord low xs
                                            && alwaysAnother p xs
                                            && low <= ord (ihead xs)}
                                   -> { _incrFromK k ord low
                                               (filter p xs)}
@-}
_lemmaFilterPreservesIncrFromK
  :: Int
  -> OrdF a
  -> Pred a
  -> Int
  -> IStream a
  -> Proof
_lemmaFilterPreservesIncrFromK 0 ord p low xxs
  =   _incrFromK 0 ord low (filter p xxs)
  *** QED
_lemmaFilterPreservesIncrFromK k ord p low xxs@(ICons x xs)
  | p x
  =   incrFrom ord low xxs
  === (low <= ord x && ord x + 1 <= ord x'
        && incrFrom ord (ord x + 1) xs)
    ? lemmaTailAlwaysAnother p xxs
    ? _lemmaFilterPreservesIncrFromK (k-1) ord p (ord x + 1) xs
  === _incrFromK k ord low (x `ICons` filter p xs)
  === _incrFromK k ord low (filter p xxs)
  *** QED

  | otherwise
  =   incrFrom ord low xxs
  === (low <= ord x && incrFrom ord (ord x + 1) xs)
  === (low <= ord x && ord x + 1 <= ord x'
        && incrFrom ord (ord x + 1) xs)
    ? lemmaTailAlwaysAnother p xxs
    ? lemmaIncrLoose ord (ord x + 1) low xs
    ? liquidAssert (next p xs < next p xxs ? nextLemma p xxs)
      (_lemmaFilterPreservesIncrFromK k ord p low xs)
  === _incrFromK k ord low (filter p xs)
  === _incrFromK k ord low (filter p xxs)
  *** QED
  where (ICons x' xs') = xs

