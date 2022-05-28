{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--prune-unsorted" @-} -- or else weird errors :/
{-@ LIQUID "--higherorder" @-}

{-# LANGUAGE GADTs #-}
module SizedTypes.ListProofsGADTs where

import Prelude hiding ((++), repeat, zipWith, map, isInfinite,not)
import Language.Haskell.Liquid.ProofCombinators

{-@ infix :| @-} -- @-} -- highlighting issue.
data List a = a :| (List a) | Nil
infixr 5 :|

{-@ measure emp @-}
emp Nil = True
emp _   = False

{-@ type ListNE a = {v:List a | not (emp v)} @-}
{-@ type Emp    a = {v:List a | emp v } @-}
{-@ measure hd @-}
{-@ hd :: ListNE _ -> _ @-}
hd (x :| _) = x

{-@ measure tl @-}
{-@ tl :: ListNE _ -> _ @-}
tl (_ :| xs) = xs

------------------------------------------
-- | Functions
{-@ infix ++ @-}

{-@ reflect ++ @-}
Nil       ++ ys = ys
(x :| xs) ++ ys = x :| xs ++ ys
infixr 5 ++

{-@ reflect map @-}
{-@ map :: _ -> xs:_ -> {v:_|emp xs <=> emp v} @-}
map :: (a -> b) -> List a -> List b
map _ Nil       = Nil
map f (x :| xs) = (f x) :| map f xs

-- | Predicates
{-@ reflect isInfinite @-}
isInfinite (x :| xs) = isInfinite xs
isInfinite Nil       = False
------------------------------------------
-- | Coinductive predicates

data Proposition a = Bisimilar Int (List a) (List a)
data Bisimilar a where
      BisimNil :: Int
               -> List a -> List a
               -> Bisimilar a
      Bisim :: Int -> a -> List a -> List a
            -> (Int -> Bisimilar a)
            -> Bisimilar a
{-@ data Bisimilar a where
          BisimNil :: i:Nat
                   -> xs:Emp a -> ys:Emp a
                   -> Prop (Bisimilar i xs ys)
          Bisim :: i:Nat -> x:a -> xs:List a -> ys:List a
                -> (j:{j:Nat | j < i} ->  Prop (Bisimilar j xs ys))
                -> Prop (Bisimilar i (x :| xs) (x :| ys)) @-}


{-@
assume bisimAxiom :: x:List a -> y:List a
                  -> (i:Nat -> Prop (Bisimilar i x y))
                  -> { x = y } @-}
bisimAxiom :: List a -> List a -> (Int -> Bisimilar a) -> Proof
bisimAxiom x y p = ()

data PropInf a = Infinite Int (List a)
data Infinite a where
  Inf :: Int
      -> a
      -> List a
      -> (Int -> Infinite a)
      -> Infinite a

{-@ data Infinite a where
         Inf :: i:Nat -> x:a -> xs:List a
             -> (j:{j:Nat | j < i} ->  Prop (Infinite j xs))
             -> Prop (Infinite i (x :| xs)) @-}

{-@
assume infAxiom :: x:List a
                -> (i:Nat -> Prop (Infinite i x))
                -> { isInfinite x } @-}
infAxiom :: List a -> (Int -> Infinite a) -> Proof
infAxiom x p = ()

------------------------------------------
-- | Proofs
{-@ bisimRefl :: xs:_ -> i:Nat -> Prop (Bisimilar i xs xs) @-}
bisimRefl xs@Nil i = BisimNil i xs xs
bisimRefl xxs@(x:|xs) i = Bisim i x xs xs (bisimRefl xs)

{-@ appendAssocS :: xs:_ -> ys:_ -> zs:_ -> i:Nat
                 -> Prop (Bisimilar i ((xs ++  ys) ++ zs)
                                      ( xs ++ (ys  ++ zs)))
@-}
appendAssocS Nil ys zs i =
  bisimRefl ((Nil ++ ys) ++ zs) i
  ? ( (Nil ++ ys) ++ zs
  === ys ++ zs
  === Nil ++ ys ++ zs
  *** QED)
appendAssocS xxs@(x :| xs) ys zs i =
  Bisim i x ((xs ++ ys) ++ zs) (xs ++ ys ++ zs) (appendAssocS xs ys zs)
  ? expandL ? expandR
  where
    expandL
      =  (xxs ++ ys) ++ zs
     === (x :| xs ++ ys) ++ zs
     === x :| (xs ++ ys) ++ zs
    expandR
      =  xxs ++ ys ++ zs
     === x :| xs ++ ys ++ zs

-- | Paulson proofs

{-@
theoremMapAppendS :: f:_ -> m:_ -> n:_ -> i:Nat
                  -> Prop (Bisimilar i (map f (m ++ n))
                                       (map f m ++ map f n)) @-}
theoremMapAppendS f Nil n i =
  bisimRefl (map f (Nil ++ n)) i
  ? ( map f (Nil ++ n)
  === map f n
  === Nil ++ map f n
  === map f Nil ++ map f n
  *** QED)
theoremMapAppendS f mms@(m :| ms) n i =
  Bisim i (f m) (map f (ms ++ n)) (map f ms ++ map f n)
        (theoremMapAppendS f ms n) ? expandL ? expandR
  where expandL =  map f (mms ++ n)
               === map f (m :| ms ++ n)
               === f m :| map f (ms ++ n)
               *** QED
        expandR =  map f mms ++ map f n
               === (f m :| map f ms) ++ map f n
               === f m :| map f ms ++ map f n
               *** QED

{-@
lemmaMapInfiniteS :: f:_ -> {xs:_| isInfinite xs} -> i:Nat
                  -> Prop (Infinite i (map f xs))@-}
lemmaMapInfiniteS f xs@Nil _ =
  absurd (xs ? (isInfinite xs === False *** QED))
lemmaMapInfiniteS f xxs@(x :| xs) i =
  Inf i (f x) (map f xs) (lemmaMapInfiniteS f (xs ?infTail)) ? expand
  where expand =  map f xxs
              === f x :| map f xs
              *** QED
        infTail = isInfinite xxs
               === isInfinite xs
               *** QED
------------------------------------------
-- | Utility functions

{-@ reflect bottom @-}
{-@ lazy bottom @-}
bottom :: a
bottom = bottom

{-@ reflect absurd @-}
{-@ absurd :: {v:_|false} -> a @-}
absurd v = bottom
