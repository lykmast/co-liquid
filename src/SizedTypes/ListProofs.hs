{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--prune-unsorted" @-} -- or else weird errors :/
{-@ LIQUID "--higherorder" @-}
module SizedTypes.ListProofs where

import Prelude hiding (repeat, zipWith, map, hd, tl, isInfinite,not)
import Language.Haskell.Liquid.ProofCombinators
import SizedTypes.Size

data List a = Cons a (List a) | Nil
{-@ measure emp @-}
emp Nil = True
emp _   = False

{-@ type ListNE a = {v:List a | not (emp v)} @-}

{-@ reflect hd @-}
{-@ hd :: ListNE _ -> _ @-}
hd (Cons x _) = x

{-@ reflect tl @-}
{-@ tl :: ListNE _ -> _ @-}
tl (Cons _ xs) = xs

{-@ reflect repeat @-}
repeat x = Cons x (repeat x)

{-@ lazy map @-}
{-@ reflect map @-}
{-@ map :: _ -> xs:_ -> {v:_|emp xs <=> emp v} @-}
map :: (a -> b) -> List a -> List b
map _ Nil = Nil
map f xs  = Cons (f (hd xs)) $ map f (tl xs)

{-@ reflect append @-}
append :: List a -> List a -> List a
append Nil ys = ys
append xs  ys = hd xs `Cons` append (tl xs) ys


{-@ assume bisim :: i:Size
                 -> xs:_
                 -> ys:_
                 -> ({j:Size| j<i} -> {hd xs = hd ys})
                 -> ({j:Size| j<i} -> {tl xs = tl ys})
                 -> {xs = ys}
@-}
bisim :: Size -> List a -> List a
      -> (Size -> Proof) -> (Size -> Proof)
      -> Proof
bisim i xs ys p1 p2 = ()

{-@ lemma_appCons :: x:_ -> xs:_ -> ys:_
                  -> {append (Cons x xs) ys = Cons x (append xs ys)}
@-}
lemma_appCons :: a -> List a -> List a -> Proof
lemma_appCons x xs ys
  =   Cons x xs `append` ys
  === Cons (hd (Cons x xs)) (tl (Cons x xs) `append` ys)
  === Cons x (xs `append` ys)
  *** QED

{-@ appendAssoc :: i:Size -> xs:_ -> ys:_ -> zs:_
                -> {append xs (append ys zs) = append (append xs ys) zs}
@-}
appendAssoc :: Size -> List a -> List a -> List a -> Proof
appendAssoc i Nil ys zs
  =   append Nil (append ys zs)
  === append ys zs
  === append (append Nil ys) zs
  *** QED
appendAssoc i xs  ys zs = bisim i (append xs (append ys zs))
                                  (append (append xs ys) zs)
                                  thH thT
  where
    thH j
      =   hd (thApp1 j)
      === hd xs
      === hd (thApp2 j)
      *** QED
    thT j
      =   tl (thApp1 j)
      === (tl xs `append` ys) `append` zs
        ? appendAssoc j (tl xs) ys zs
      === tl xs `append` (ys `append` zs)
      === tl (thApp2 j)
      *** QED
    thApp1 j
      =   (xs `append` ys) `append` zs
      === Cons (hd xs) (tl xs `append` ys) `append` zs
        ? lemma_appCons (hd xs) (tl xs `append` ys) zs
      === Cons (hd xs) ((tl xs `append` ys) `append` zs)
    thApp2 j
      =   xs  `append` (ys `append` zs)
      === Cons (hd xs) (tl xs `append` (ys `append` zs))

---------------- Paulson ------------------


{-@ theoremMapAppend :: Size -> f:_ -> m:_ -> n:_
                     -> {map f (append m n)
                          = append (map f m) (map f n) }
@-}
theoremMapAppend :: Size -> (a -> b) -> List a -> List a -> Proof
theoremMapAppend _ f Nil n
  =   map f (append Nil n)
  === map f n
  === Nil `append` map f n
  === map f Nil `append` map f n
  *** QED
theoremMapAppend i f m n = bisim i (map f (append m n))
                               (append (map f m) (map f n))
                               thH thT
  where
    thH j
      =   hd (thMApp1 j)
      === f (hd m)
      === hd (thMApp2 j)
      *** QED
    thT j
      =   tl (thMApp1 j)
      === map f (append (tl m) n)
        ? theoremMapAppend j f (tl m) n
      === map f (tl m) `append` map f n
      === tl (thMApp2 j)
      *** QED
    thMApp1 j
      =   map f (append m n)
      === map f ((hd m) `Cons` append (tl m) n)
      === f (hd ((hd m) `Cons` append (tl m) n))
            `Cons` map f (tl ((hd m) `Cons` append (tl m) n))
      === f (hd m) `Cons` map f (append (tl m) n)
    thMApp2 j
      =   map f m `append` map f n
      === (f (hd m) `Cons` map f (tl m)) `append` map f n
      === hd (f (hd m) `Cons` map f (tl m)) `Cons`
          append (tl (f (hd m) `Cons` map f (tl m))) (map f n)
      === f (hd m) `Cons` append (map f (tl m)) (map f n)

{-@ reflect isInfinite @-}
isInfinite Nil = False
isInfinite xs  = isInfinite (tl xs)



{-@ assume isInfiniteS :: i:Size
                       -> xs:ListNE _
                       -> ({j:Size| j<i} -> {isInfinite (tl xs)})
                       -> {isInfinite xs}
@-}
isInfiniteS :: Size
            -> List a
            -> (Size -> Proof)
            -> Proof
isInfiniteS i xs p = ()

{-@ reflect not @-}
not True  = False
not False = True

{-@ reflect isFinite @-}
isFinite = not . isInfinite

{-@ lemmaMapInfinite :: i:Size
                     -> f:_ -> {xs:_|isInfinite xs}
                     -> {isInfinite (map f xs)}
@-}
lemmaMapInfinite :: Size -> (a -> b) -> List a -> Proof
lemmaMapInfinite i f xs@Nil = isInfinite xs === False *** QED
lemmaMapInfinite i f xs = isInfiniteS i (map f xs) $ \j
  ->  tl (map f xs)
  === tl (Cons (f (hd xs)) (map f (tl xs)))
  === map f (tl xs)
    ? (isInfinite xs === isInfinite (tl xs) *** QED)
    ? lemmaMapInfinite j f (tl xs)
  *** QED

