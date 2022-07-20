{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
{-# LANGUAGE GADTs #-}

module Paper.Section5.Tree where

import Prelude hiding (not)
import Language.Haskell.Liquid.ProofCombinators

data Tree a = Bin a (Tree a) (Tree a)

{-@ measure label @-}
label (Bin x _ _) = x

{-@ measure left @-}
left (Bin _ l _) = l

{-@ measure right @-}
right (Bin _ _ r) = r


-- direction of path in tree.
data Dir = L | R

type Path = [Dir]

-- label at path p
{-@ reflect labelP @-}
labelP []    (Bin x _ _) = x
labelP (L:p) (Bin _ l _) = labelP p l
labelP (R:p) (Bin _ _ r) = labelP p r

-- tree indexed equality
{-@ reflect eq @-}
{-@ eq :: Nat -> _ -> _ -> _ @-}
eq :: Eq a => Int -> Tree a -> Tree a -> Bool
eq 0 _ _ = True
eq k (Bin x l1 r1) (Bin y l2 r2) = x == y && eq (k-1) l1 l2 && eq (k-1) r1 r2


-- theorem: if for two trees the label at every path is the same,
--   the trees are equal.
{-@ labelEq :: t1:_ -> t2:_
            -> (p:_ -> {labelP p t1 = labelP p t2})
            -> k:Nat
            -> {eq k t1 t2} @-}
labelEq :: Eq a => Tree a -> Tree a -> (Path -> Proof) -> Int -> Proof
labelEq t1 t2 _ 0 = eq 0 t1 t2 *** QED
labelEq t1@(Bin x l1 r1) t2@(Bin y l2 r2) pr k
  =   eq k t1 t2
  === (x == y && eq (k-1) l1 l2 && eq (k-1) r1 r2)
    ? auxRoot t1 t2 pr
    ? labelEq l1 l2 (auxL t1 t2 pr) (k-1)
    ? labelEq r1 r2 (auxR t1 t2 pr) (k-1)
  *** QED

-- auxilliary proofs:

{-@ auxRoot :: t1:_ -> t2:_ -> (p:_ -> {labelP p t1 = labelP p t2})
            -> {label t1 = label t2} @-}
auxRoot :: Tree a -> Tree a -> (Path -> Proof) -> Proof
auxRoot t1@(Bin x _ _) t2@(Bin y _ _) pr -- = ()
  =   label t1
  === labelP [] t1
    ? pr []
  === labelP [] t2
  === label t2
  *** QED

{-@ auxL :: t1:_ -> t2:_ -> (p:_ -> {labelP p t1 = labelP p t2})
         -> p:_ -> {labelP p (left t1) = labelP p (left t2)} @-}
auxL :: Tree a -> Tree a -> (Path -> Proof) -> (Path -> Proof)
auxL t1@(Bin _ l1 r1) t2@(Bin _ l2 r2) pr p
  =   labelP p l1
  === labelP (L:p) t1
    ? pr (L:p)
  === labelP (L:p) t2
  === labelP p l2
  *** QED

{-@ auxR :: t1:_ -> t2:_ -> (p:_ -> {labelP p t1 = labelP p t2})
         -> p:_ -> {labelP p (right t1) = labelP p (right t2)} @-}
auxR :: Tree a -> Tree a -> (Path -> Proof) -> (Path -> Proof)
auxR t1@(Bin _ l1 r1) t2@(Bin _ l2 r2) pr p -- = ()
  =   labelP p r1
  === labelP (R:p) t1
    ? pr (R:p)
  === labelP (R:p) t2
  === labelP p r2
  *** QED

-- the approx lemma can only be encoded on the indexed equality
--  since we cannot encode approx.
{-@ assume approxLemma :: t1:_ -> t2:_ -> (k:Nat -> {eq k t1 t2}) -> {t1 = t2} @-}
approxLemma :: Tree a -> Tree a -> (Int -> Proof) -> Proof
approxLemma t1 t2 pr = ()

-- original theorem proven with approx lemma and the indexed approach.
{-@ labelEqOrig :: t1:_ -> t2:_
            -> (p:_ -> {labelP p t1 = labelP p t2})
            -> {t1 = t2} @-}
labelEqOrig :: Eq a => Tree a -> Tree a -> (Path -> Proof) -> Proof
labelEqOrig t1 t2 pr = approxLemma t1 t2 (labelEq t1 t2 pr)

-- the same theorem proven constructively:
data Proposition a = Bisimilar  Int (Tree a) (Tree a)

data Bisimilar a where
      Bisim :: Int -> a -> Tree a -> Tree a
            -> Tree a -> Tree a
            -> (Int -> Bisimilar a)
            -> (Int -> Bisimilar a)
            -> Bisimilar a
{-@ data Bisimilar a where
          Bisim :: i:Nat -> x:a -> l1:Tree a -> l2:Tree a
                -> r1:Tree a -> r2:Tree a
                -> (j:{j:Nat | j < i} ->  Prop (Bisimilar j l1 l2))
                -> (j:{j:Nat | j < i} ->  Prop (Bisimilar j r1 r2))
                -> Prop (Bisimilar i (Bin x l1 r1) (Bin x l2 r2)) @-}


{-@ labelEqC :: t1:_ -> t2:_
             -> (p:_ -> {labelP p t1 = labelP p t2})
             -> i:Nat
             -> Prop (Bisimilar i t1 t2) @-}

labelEqC :: Tree a -> Tree a -> (Path -> Proof) -> Int -> Bisimilar a
labelEqC t1@(Bin x l1 r1) t2@(Bin y l2 r2) pr i
  = Bisim i (x ? auxRoot t1 t2 pr) l1 l2 r1 r2
      (labelEqC l1 l2 (auxL t1 t2 pr))
      (labelEqC r1 r2 (auxR t1 t2 pr))

