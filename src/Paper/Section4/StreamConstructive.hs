{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--reflection" @-}

{-# LANGUAGE GADTs #-}
module Paper.Section4.StreamConstructive where

import Language.Haskell.Liquid.ProofCombinators hiding (trivial)

import Prelude hiding (not, take)
import Paper.Section4.Stream

{-@ infixr :> @-}
{-@ infixr . @-}

-- Coinductive predicates

data Proposition a = Bisimilar  Int (Stream a) (Stream a)
                   | Below      Int (Stream a) (Stream a)
                   | TrueStream Int (Stream a)
                   | Dup        Int (Stream a)
                   | NNeg       Int (Stream Int)

data Bisimilar a where
      Bisim :: Int -> a -> Stream a -> Stream a
            -> (Int -> Bisimilar a)
            -> Bisimilar a
{-@ data Bisimilar a where
          Bisim :: i:Nat -> x:a -> xs:Stream a -> ys:Stream a
                -> (j:{j:Nat | j < i} ->  Prop (Bisimilar j xs ys))
                -> Prop (Bisimilar i (x :> xs) (x :> ys)) @-}

{-@ bisimLemma :: x:Stream a -> y:Stream a
                  -> (i:Nat -> Prop (Bisimilar i x y))
                  -> { x = y } @-}
bisimLemma = approx -- proven later with the (axiomatized) take lemma


-- Lexicographic ordering
data Below a where
      Bel0 :: Ord a
           => Int -> a -> Stream a -> Stream a -- if heads are =
           -> (Int -> Below a) -- then streams need to prove they are <=
           -> Below a
      Bel1 :: Ord a
           => Int -> a -> a  -- if heads are <
           -> Stream a -> Stream a
           -> Below  a     -- then the streams are <
{-@ data Below a where
       Bel0 :: Ord a
            => i:Nat -> x:a -> xs:Stream a -> ys:Stream a
            -> (j:{j:Nat | j < i} ->  Prop (Below j xs ys))
            -> Prop (Below i (x :> xs) (x :> ys))
       Bel1 :: Ord a
            => i:Nat -> x:a -> {y:a| x < y}
            -> xs:Stream a -> ys:Stream a
            -> Prop (Below i (x :> xs) (y :> ys)) @-}

{-@ assume belLemma :: Ord a => x:Stream a -> y:Stream a
                    -> (i:Nat -> Prop (Below i x y))
                    -> { below x y } @-}
belLemma :: Stream a -> Stream a -> (Int -> Below a) -> Proof
belLemma x y p = ()


-- Trivial predicate
data TrueStream a where
      TrueS :: Int -> a -> Stream a  -- whatever the head
            -> (Int -> TrueStream a) -- and tail is any
            -> TrueStream a          -- => the whole stream is any
{-@ data TrueStream a where
       TrueS :: i:Nat -> x:a -> xs:Stream a
             -> (j:{j:Nat | j < i} ->  Prop (TrueStream j xs))
             -> Prop (TrueStream i (x :> xs)) @-}

{-@ assume trueSLemma :: x:Stream a
                      -> (i:Nat -> Prop (TrueStream i x))
                      -> { trivial x } @-}
trueSLemma :: Stream a -> (Int -> TrueStream a) -> Proof
trueSLemma x p = ()


data Dup a where
      MkDup :: Int -> a -> Stream a -- whatever the head
            -> (Int -> Dup a)       -- and tail is dup
            -> Dup a                -- => the stream with duplicated
                                    --     head is dup
{-@ data Dup a where
       MkDup  :: i:Nat -> x:a -> xs:Stream a
              -> (j:{j:Nat | j < i} ->  Prop (Dup j xs))
              -> Prop (Dup i (x :> x :> xs)) @-}

{-@ assume dupLemma :: x:Stream a
                      -> (i:Nat -> Prop (Dup i x))
                      -> { dup x } @-}
dupLemma :: Stream a -> (Int -> Dup a) -> Proof
dupLemma x p = ()

data NNeg where
      NNegC :: Int -> Int -> Stream Int
            -> (Int -> NNeg)
            -> NNeg

{-@ data NNeg where
       NNegC :: i:Nat -> {x:Int| x>= 0} -> xs:Stream Int
            -> (j:{j:Nat | j < i} ->  Prop (NNeg j xs))
            -> Prop (NNeg i (x :> xs))
@-}

{-@ assume nnegLemma :: x:Stream Int
                    -> (i:Nat -> Prop (NNeg i x))
                    -> {nneg x} @-}
nnegLemma :: Stream Int -> (Int -> NNeg) -> Proof
nnegLemma x p = ()

---------------------------------------------
-- Proofs

{-@ mapFusionI :: f:_ -> g:_ -> xs:_ -> i:Nat
                 -> Prop (Bisimilar i (smap f (smap g xs)) (smap (f . g) xs))
@-}
mapFusionI f g xxs@(x:>xs) i =
  Bisim i ((f . g) x) (smap f (smap g xs)) (smap (f . g) xs)
        (mapFusionI f g xs) ? expandL ? expandR
  where expandL
          =  smap f (smap g xxs)
         === smap f (g x :> smap g xs)
         === (f (g x)) :> smap f (smap g xs)
         *** QED
        expandR
          =  smap (f . g) xxs
         === (f . g) x :> smap (f . g) xs
         *** QED

{-@ mapFusion :: f:_ -> g:_ -> xs:_
                 -> {smap f (smap g xs) = smap (f . g) xs} @-}
mapFusion :: (b -> c) -> (a -> b) -> Stream a -> Proof
mapFusion f g xs =
  bisimLemma (smap f (smap g xs)) (smap (f . g) xs) (mapFusionI f g xs)


-- | To avoid cluttering we add the rest of the
--   orginal theorem proofs (without indexes by
--   use of axioms) at the end.

{-@ mergeEvenOddI :: xs:Stream a
                  -> i:Nat
                  -> Prop (Bisimilar i  (merge (odds xs) (evens xs)) xs)
@-}
mergeEvenOddI xxs@(x :> xs) i
  = Bisim i x (merge (odds xs) (evens xs)) xs (mergeEvenOddI xs)
     ? ( merge (odds xxs) (evens xxs)
    === merge (x :> odds (stail xs)) (odds (stail xxs))
    === x :> merge (odds (stail xxs)) (odds (stail xs))
    === x :> merge (odds xs) (evens xs)
    *** QED)

{-@ belowSquareI :: xs:_ -> i:Nat
                       -> Prop (Below i xs (mult xs xs)) @-}
belowSquareI xxs@(x :> xs) i
  | x == x*x
  = Bel0 i x xs (mult xs xs) (belowSquareI xs)
  | x < x*x
  = Bel1 i x (x*x) xs (mult xs xs) ? expand
  where
    expand =  mult xxs xxs
          === x*x :> mult xs xs
          *** QED

{-@ trivialAll :: xs:Stream a -> {trivial xs} @-}
trivialAll xs = trueSLemma xs (trivialAllI xs)
  where {-@ trivialAllI :: xs:_ -> i:Nat -> Prop (TrueStream i xs) @-}
        trivialAllI (x :> xs) i = TrueS i x xs (trivialAllI xs)


{-@
morseMergeI :: xs:_ -> i:Nat
              -> Prop (Bisimilar i (ff xs) (merge xs (smap not xs)))
@-}
morseMergeI xxs@(x :> xs) i
  =       Bisim i x (stail (ff xxs)) (stail (merge xxs (smap not xxs)))
  $ \j -> Bisim j (not x) (ff xs) (merge xs (smap not xs))
                (morseMergeI xs) ? expandL ? expandR
  where
    expandL
       =  stail (merge xxs (smap not xxs))
      === stail (x :> merge (smap not xxs) xs)
      === merge (not x :> smap not xs) xs
      === not x :> merge xs (smap not xs)
      *** QED
    expandR
       =  stail (ff xxs)
      === stail (x :> not x :> ff xs)
      === not x :> ff xs
      *** QED

{-@
theoremNotFI :: xs:_ -> i:Nat
             -> Prop (Bisimilar i (smap not (ff xs)) (ff (smap not xs)))
@-}
theoremNotFI xxs@(x :> xs) i
  =       Bisim i (not x) tlLhs tlRhs
  $ \j -> Bisim j (not (not x)) (smap not (ff xs))
                  (ff (smap not xs)) (theoremNotFI xs)
  where
    lhs
      =  smap not (ff xxs)
     === smap not (x :> not x :> ff xs)
     === not x :> smap not (not x :> ff xs)
     === not x :> not (not x) :> smap not (ff xs)
    rhs
      =  ff (smap not xxs)
     === ff (not x :> smap not xs)
     === not x :> not (not x) :> ff (smap not xs)
    tlRhs
      =  stail rhs
     === not (not x) :> ff (smap not xs)
    tlLhs
      =  stail lhs
     === not (not x) :> smap not (ff xs)

{-@ mergeSelfDupI :: xs:_ -> i:Nat -> Prop (Dup i (merge xs xs)) @-}
mergeSelfDupI xxs@(x :> xs) i =
  MkDup i x (merge xs xs) (mergeSelfDupI xs)
  ? ( merge xxs xxs
   === x :> merge xxs xs
   === x :> x :> merge xs xs
   *** QED)

{-@ squareNNegI :: xs:_ -> i:Nat
                       -> Prop (NNeg i (mult xs xs)) @-}
squareNNegI xxs@(x :> xs) i
  =  NNegC i (x*x) (mult xs xs) (squareNNegI xs)
  ?  (mult xxs xxs === x*x :> mult xs xs *** QED)

-- | Original theorems:

{-@ mergeEvenOdd :: xs:_ -> {merge (odds xs) (evens xs) = xs} @-}
mergeEvenOdd xs =
  bisimLemma (merge (odds xs) (evens xs)) xs (mergeEvenOddI xs)

{-@ mergeSelfDup :: xs:_ -> {dup (merge xs xs)} @-}
mergeSelfDup xs = dupLemma (merge xs xs) (mergeSelfDupI xs)

{-@ belowSquare :: xs:Stream Int -> {below xs (mult xs xs)} @-}
belowSquare xs
  = belLemma xs (mult xs xs) (belowSquareI xs)

-- | Note that `morseFix` does not use coinduction (no self call)
-- so there is no need to use `bisim`.
{-@ morseFix :: {ff morse = morse} @-}
morseFix
  =   ff morse
  === shead morse :> not (shead morse) :> ff (stail morse)
    ? morseMerge (stail morse)
  === False :> True :> merge (stail morse) (smap not (stail morse))
  === morse
  *** QED

{-@ morseMerge :: xs:Stream Bool -> {ff xs = merge xs (smap not xs)} @-}
morseMerge xs
  = bisimLemma (ff xs) (merge xs (smap not xs)) (morseMergeI xs)

{-@ fNotCommute ::xs:Stream Bool ->{smap not (ff xs) = ff (smap not xs)}@-}
fNotCommute xs
  = bisimLemma (smap not (ff xs)) (ff (smap not xs)) (theoremNotFI xs)

{-@ squareNNeg :: xs:_ -> {nneg (mult xs xs)} @-}
squareNNeg xs = nnegLemma (mult xs xs) (squareNNegI xs)

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

-- Here we assume that eqKLemma holds. We actually prove it in
--   EqLemma.hs in order not to curry (Eq a) to all theorems.
eqKLemma :: Stream a -> Stream a -> Int -> Bisimilar a -> ()
{-@ assume eqKLemma :: x:Stream a -> y:Stream a
                  -> i:Nat -> Prop (Bisimilar i x y)
                  ->  {take i x = take i y} @-}
eqKLemma x y 0 _ = take 0 x === take 0 y *** QED
eqKLemma _ _ _ (Bisim i x xs ys p) = ()

approx :: Stream a -> Stream a -> (Int -> Bisimilar a) -> ()
{-@ approx :: x:Stream a -> y:Stream a
                  -> (i:Nat -> Prop (Bisimilar i x y))
                  -> { x = y } @-}
approx x y p = takeLemma x y $ \i -> eqKLemma x y i (p i)

-------------------------------------------------
-- | Pitfalls


-- Without Guardedness we can prove false :(
data PropositionNG a = BisimilarNG (Stream a) (Stream a)


--
data BisimilarNG a where
      BisimNG :: a -> Stream a -> Stream a
            -> BisimilarNG a
            -> BisimilarNG a
{-@ data BisimilarNG a where
          BisimNG :: x:a -> xs:Stream a -> ys:Stream a
                -> Prop (BisimilarNG xs ys)
                -> Prop (BisimilarNG (x :> xs) (x :> ys)) @-}

falseProp :: Stream a -> Stream a ->  BisimilarNG a -> ()
{-@ falseProp :: x:Stream a -> y:Stream a -> Prop (BisimilarNG x y) -> {false} @-}
falseProp _ _ (BisimNG a x y p)
  = falseProp x y p

{-@ lazy falseEq @-}
falseEq :: Stream a -> Stream a -> BisimilarNG a
{-@ falseEq :: x:Stream a -> y:Stream a -> Prop (BisimilarNG x y) @-}
falseEq x y = falseEq x y
