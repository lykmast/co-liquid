{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-adt" @-}

{-# LANGUAGE GADTs #-}
module SizedTypes.StreamProofsGADTs where

import Prelude hiding (take, not, map)

import Language.Haskell.Liquid.ProofCombinators

{-@ infixr :> @-}
infixr 5 :>
data Stream a = a :> Stream a

{-@ measure shead @-}
{-@ measure stail @-}

shead :: Stream a -> a
stail :: Stream a -> Stream a
shead (x :> _ ) = x
stail (_ :> xs) = xs



--------------------------------------------
-- Functions

odds :: Stream a -> Stream a
odds (x :> xs) = x :> (odds (stail xs))

evens :: Stream a -> Stream a
evens xs = odds (stail xs)

merge :: Stream a -> Stream a -> Stream a
merge (x :> xs) ys = x :> (merge ys xs)

mult :: Stream Int -> Stream Int -> Stream Int
mult (x :> xs) (y :> ys) = x * y :> mult xs ys

morse :: Stream Bool
morse = False :> True :> merge (stail morse) (map not (stail morse))

f :: Stream Bool -> Stream Bool
f xs = shead xs :> not (shead xs) :> f (stail xs)


{-@ reflect odds  @-}
{-@ reflect evens @-}
{-@ reflect merge @-}
{-@ reflect mult @-}
{-@ reflect f @-}
{-@ reflect morse @-}

-- Predicates
below :: Stream Int -> Stream Int -> Bool
below (x:>xs) (y:>ys) = x <= y
            && ((x == y) `implies` below xs ys)

trueStream (_:>xs) = trueStream xs

dup (x :> y :> xs) = x == y && dup xs

{-@ reflect dup @-}
{-@ reflect trueStream @-}
{-@ reflect below @-}
---------------------------------------------
-- Coinductive predicates

data Proposition a = Bisimilar  Int (Stream a  ) (Stream a  )
                   | Below      Int (Stream Int) (Stream Int)
                   | TrueStream Int (Stream a)
                   | Dup        Int (Stream a)

data Bisimilar a where
      Bisim :: Int -> a -> Stream a -> Stream a
            -> (Int -> Bisimilar a)
            -> Bisimilar a
{-@ data Bisimilar a where
          Bisim :: i:Nat -> x:a -> xs:Stream a -> ys:Stream a
                -> (j:{j:Nat | j < i} ->  Prop (Bisimilar j xs ys))
                -> Prop (Bisimilar i (x :> xs) (x :> ys)) @-}


{-@ bisimAxiom :: x:Stream a -> y:Stream a
                  -> (i:Nat -> Prop (Bisimilar i x y))
                  -> { x = y } @-}
bisimAxiom = approx -- proven later with the (axiomatized) take lemma

-- Lexicographic ordering
data Below where
      Bel0 :: Int -> Int -> Stream Int -> Stream Int -- if heads are =
           -> (Int -> Below) -- then streams need to prove they are <=
           -> Below
      Bel1 :: Int -> Int -> Int  -- if heads are <
           -> Stream Int -> Stream Int
           -> Below       -- then the streams are <
{-@ data Below where
       Bel0 :: i:Nat -> x:Int -> xs:Stream Int -> ys:Stream Int
            -> (j:{j:Nat | j < i} ->  Prop (Below j xs ys))
            -> Prop (Below i (x :> xs) (x :> ys))
       Bel1 :: i:Nat -> x:Int -> {y:Int| x < y}
            -> xs:Stream Int -> ys:Stream Int
            -> Prop (Below i (x :> xs) (y :> ys)) @-}



{-@ assume belAxiom :: x:Stream Int -> y:Stream Int
                    -> (i:Nat -> Prop (Below i x y))
                    -> { below x y } @-}
belAxiom :: Stream Int -> Stream Int -> (Int -> Below) -> Proof
belAxiom x y p = ()

-- Trivial predicate
data TrueStream a where
      TrueS :: Int -> a -> Stream a  -- whatever the head
            -> (Int -> TrueStream a) -- and tail is any
            -> TrueStream a          -- => the whole stream is any
{-@ data TrueStream a where
       TrueS :: i:Nat -> x:a -> xs:Stream a
             -> (j:{j:Nat | j < i} ->  Prop (TrueStream j xs))
             -> Prop (TrueStream i (x :> xs)) @-}



{-@ assume trueSAxiom :: x:Stream a
                      -> (i:Nat -> Prop (TrueStream i x))
                      -> { trueStream x } @-}
trueSAxiom :: Stream a -> (Int -> TrueStream a) -> Proof
trueSAxiom x p = ()


data Dup a where
      MkDup :: Int -> a -> Stream a -- whatever the head
            -> (Int -> Dup a)       -- and tail is dup
            -> Dup a                -- => the stream with duplicated
                                    --     head is dup
{-@ data Dup a where
       MkDup  :: i:Nat -> x:a -> xs:Stream a
              -> (j:{j:Nat | j < i} ->  Prop (Dup j xs))
              -> Prop (Dup i (x :> x :> xs)) @-}


{-@ assume dupAxiom :: x:Stream a
                      -> (i:Nat -> Prop (Dup i x))
                      -> { dup x } @-}
dupAxiom :: Stream a -> (Int -> TrueStream a) -> Proof
dupAxiom x p = ()

---------------------------------------------
-- Proofs

{-@ lemmaEvenOdd :: xs:Stream a
                 -> i:Nat
                 ->  Prop (Bisimilar i  (merge (odds xs) (evens xs)) (xs))
@-}
lemmaEvenOdd xxs@(x :> xs) i
  = Bisim i x (merge (odds xs) (evens xs)) xs (lemmaEvenOdd xs)
     ? ( merge (odds xxs) (evens xxs)
    === merge (x :> odds (stail xs)) (odds (stail xxs))
    === x :> merge (odds (stail xxs)) (odds (stail xs))
    === x :> merge (odds xs) (evens xs)
    *** QED)

{-@ lemmaEvenOddOriginal :: xs:_ -> {merge (odds xs) (evens xs) = xs} @-}
lemmaEvenOddOriginal xs =
  bisimAxiom (merge (odds xs) (evens xs)) xs (lemmaEvenOdd xs)

-----------------
-- | In the rest we don't use the axioms in cases where
--     it is redundant
{-@ infixr . @-}
{-@ streamFusion :: f:_ -> g:_ -> xs:_ -> i:Nat
                 -> Prop (Bisimilar i (map f (map g xs)) (map (f . g) xs))
@-}
streamFusion f g xxs@(x:>xs) i =
  Bisim i ((f . g) x) (map f (map g xs)) (map (f . g) xs)
        (streamFusion f g xs) ? expandL ? expandR
  where expandL
          =  map f (map g xxs)
         === map f (g x :> map g xs)
         === (f (g x)) :> map f (map g xs)
         *** QED
        expandR
          =  map (f . g) xxs
         === (f . g) x :> map (f . g) xs
         *** QED

{-@ theoremBelowSquare :: xs:_ -> i:Nat
                       -> Prop (Below i xs (mult xs xs)) @-}
theoremBelowSquare xxs@(x :> xs) i
  | x == x*x
  = Bel0 i x xs (mult xs xs) (theoremBelowSquare xs)
  | x < x*x
  = Bel1 i x (x*x) xs (mult xs xs) ? expand
  where
    expand =  mult xxs xxs
          === x*x :> mult xs xs
          *** QED

{-@ trueLemma :: xs:_ -> i:Nat -> Prop (TrueStream i xs) @-}
trueLemma (x :> xs) i = TrueS i x xs (trueLemma xs)


{-@
theoremFMerge :: xs:_ -> i:Nat
              -> Prop (Bisimilar i (f xs) (merge xs (map not xs)))
@-}
theoremFMerge xxs@(x :> xs) i
  =       Bisim i x (stail (f xxs)) (stail (merge xxs (map not xxs)))
  $ \j -> Bisim j (not x) (f xs) (merge xs (map not xs))
                (theoremFMerge xs) ? expandL ? expandR
  where
    expandL
       =  stail (merge xxs (map not xxs))
      === stail (x :> merge (map not xxs) xs)
      === merge (not x :> map not xs) xs
      === not x :> merge xs (map not xs)
      *** QED
    expandR
       =  stail (f xxs)
      === stail (x :> not x :> f xs)
      === not x :> f xs
      *** QED
{-@
theoremNotFS :: xs:_ -> i:Nat
             -> Prop (Bisimilar i (map not (f xs)) (f (map not xs)))
@-}
theoremNotFS xxs@(x :> xs) i
  =       Bisim i (not x) tlLhs tlRhs
  $ \j -> Bisim j (not (not x)) (map not (f xs))
                  (f (map not xs)) (theoremNotFS xs)
  where
    lhs
      =  map not (f xxs)
     === map not (x :> not x :> f xs)
     === not x :> map not (not x :> f xs)
     === not x :> not (not x) :> map not (f xs)
    rhs
      =  f (map not xxs)
     === f (not x :> map not xs)
     === not x :> not (not x) :> f (map not xs)
    tlRhs
      =  stail rhs
     === not (not x) :> f (map not xs)
    tlLhs
      =  stail lhs
     === not (not x) :> map not (f xs)

{-@ dupMergeS :: xs:_ -> i:Nat -> Prop (Dup i (merge xs xs)) @-}
dupMergeS xxs@(x :> xs) i =
  MkDup i x (merge xs xs) (dupMergeS xs)
  ? ( merge xxs xxs
   === x :> merge xxs xs
   === x :> x :> merge xs xs
   *** QED)
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

-- | Comment ple version, as it devoured my RAM :(.
-- {-@ ple eqKLemma @-}
-- eqKLemma :: Stream a -> Stream a -> Int -> Bisimilar a -> ()
-- {-@ eqKLemma :: x:Stream a -> y:Stream a
--                   -> i:Nat -> Prop (Bisimilar i x y)
--                   ->  {take i x = take i y} @-}
-- eqKLemma _x _ 0 _ = ()
-- eqKLemma _x _ _i (Bisim i x xs ys p)
--   = eqKLemma xs ys (i-1) (p (i-1))

eqKLemma :: Stream a -> Stream a -> Int -> Bisimilar a -> ()
{-@ assume eqKLemma :: x:Stream a -> y:Stream a
                  -> i:Nat -> Prop (Bisimilar i x y)
                  ->  {take i x = take i y} @-}
eqKLemma x y 0 _ = take 0 x === take 0 y *** QED
eqKLemma _ _ _ (Bisim i x xs ys p) = ()
  -- =   take i (x :> xs)
  -- === x : take (i-1) xs
  --   ? eqKLemma xs ys (i-1) (p (i-1))
  -- === x : take (i-1) ys
  -- === take (i-1) (x:>ys)
  -- *** QED

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
-------------------------------------------------
-- | Utility functions

{-@ reflect map @-}
map :: (a -> b) -> Stream a -> Stream b
map f (x :> xs) = f x :> map f xs

{-@ reflect implies @-}
{-@ implies :: p:Bool -> q:Bool -> {v:_| v <=> (p => q)} @-}
implies False _     = True
implies _     True  = True
implies _     _     = False

{-@ reflect not @-}
not True = False
not False = True

