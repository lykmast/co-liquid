{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--higherorder" @-}

module Filter where

-- The following come from dafny-lang/dafny/Test/dafny3/Filter.dfy
-- in github.
-- They are also referenced in "Co-induction Simply".

import IStream
import Language.Haskell.Liquid.ProofCombinators

{-@ tailN :: Nat -> _ -> _ @-}
tailN :: Int -> IStream a -> IStream a
tailN n s
  | n == 0    = s
  | otherwise = tailN (n-1) (itail s)

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

------------------------------------------------------------
-- coinductive to inductive proofs.

{-@ reflect _isSubStreamK @-}
{-@ _isSubStreamK :: Nat -> _ -> _ -> _ @-}
_isSubStreamK :: Eq a => Int -> IStream a -> IStream a -> Bool
_isSubStreamK 0 _ _ = True
_isSubStreamK k (ICons x xs) ys = mem x ys && _isSubStreamK (k-1) xs ys

{-@ _lemmaTailSubStreamK :: k:Nat
                         -> s:_
                         -> {u:_| _isSubStreamK k s (itail u)}
                         -> {_isSubStreamK k s u}
@-}


_lemmaTailSubStreamK :: Eq a => Int -> IStream a -> IStream a -> Proof
_lemmaTailSubStreamK 0 s u
  =   _isSubStreamK 0 s u *** QED
_lemmaTailSubStreamK k sss@(ICons s ss) uus@(ICons u us)
  =   _isSubStreamK k sss us
    ? lemmaInTail s uus
    ? _lemmaTailSubStreamK (k-1) ss uus
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

