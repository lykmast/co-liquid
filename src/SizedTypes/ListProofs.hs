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

{-@ measure hd @-}
{-@ hd :: ListNE _ -> _ @-}
hd (Cons x _) = x

{-@ measure tl @-}
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

{-@ measure eqI :: i:Size -> List a -> List a -> Bool @-}
{-@ assume bisim :: i:Size
                 -> xs:_
                 -> ys:_
                 -> ({j:Size| j<i} -> {hd xs = hd ys})
                 -> ({j:Size| j<i} -> {eqI j (tl xs) (tl ys)})
                 -> {eqI i xs ys}
@-}
bisim :: Size -> List a -> List a
      -> (Size -> Proof) -> (Size -> Proof)
      -> Proof
bisim i xs ys p1 p2 = ()

{-@ assume eqINil :: i:Size -> {eqI i Nil Nil} @-}
eqINil :: Size -> Proof
eqINil _ = ()

{-@
 eqIRefl :: xs:_ -> i:Size -> {eqI i xs xs}
@-}
eqIRefl :: List a -> Size -> Proof
eqIRefl Nil i = eqINil i
eqIRefl xxs@(Cons x xs) i = bisim i xxs xxs (const ()) (eqIRefl xs)

{-@ assume eqAxiom :: xs:_ -> ys:_
                   -> (i:Size -> {eqI i xs ys})
                   -> {xs = ys}
@-}
eqAxiom :: List a -> List a -> (Size -> Proof) -> Proof
eqAxiom _ _ _ = ()

{-@ lemma_appCons :: x:_ -> xs:_ -> ys:_
                  -> {append (Cons x xs) ys = Cons x (append xs ys)}
@-}
lemma_appCons :: a -> List a -> List a -> Proof
lemma_appCons x xs ys
  =   Cons x xs `append` ys
  === Cons (hd (Cons x xs)) (tl (Cons x xs) `append` ys)
  === Cons x (xs `append` ys)
  *** QED

{-@ appendAssoc :: xs:_ -> ys:_ -> zs:_
                -> {append xs (append ys zs) = append (append xs ys) zs}
@-}
appendAssoc :: List a -> List a -> List a -> Proof
appendAssoc xs ys zs =
  eqAxiom (append xs (append ys zs))
          (append (append xs ys) zs)
          (\i -> appendAssocS i xs ys zs)

{-@ appendAssocS :: i:Size -> xs:_ -> ys:_ -> zs:_
                -> {eqI i (append xs (append ys zs))
                          (append (append xs ys) zs)}
@-}
appendAssocS i Nil ys zs = eqIRefl lhs i
  where
    lhs
      =   (Nil `append` ys) `append` zs
      === ys `append` zs
      === Nil  `append` (ys `append` zs)
appendAssocS i xxs@(Cons x xs) ys zs =
  bisim i xsAYsZs xsYsAZs (const ()) (\j -> appendAssocS j xs ys zs)
  where
    xsYsAZs
      =   (xxs `append` ys) `append` zs
      === (Cons x xs `append` ys) `append` zs
      === Cons x (xs `append` ys) `append` zs
        ? lemma_appCons x (xs `append` ys) zs
      === Cons x ((xs `append` ys) `append` zs)
    xsAYsZs
      =   xxs  `append` (ys `append` zs)
      === Cons x (xs `append` (ys `append` zs))

---------------- Paulson ------------------

{-@ theoremMapAppend :: f:_ -> m:_ -> n:_
                      -> {  map f (append m n)
                          = append (map f m) (map f n)}
@-}
theoremMapAppend f m n =
  eqAxiom (map f (append m n))
          (append (map f m) (map f n))
          (\i -> theoremMapAppendS i f m n)


{-@ theoremMapAppendS :: i:Size -> f:_ -> m:_ -> n:_
                     -> {eqI i (map f (append m n))
                          (append (map f m) (map f n))}
@-}
theoremMapAppendS :: Size -> (a -> b) -> List a -> List a -> Proof
theoremMapAppendS i f Nil n = eqIRefl lhs i
  where
    lhs
      =   map f (append Nil n)
      === map f n
      === Nil `append` map f n
      === map f Nil `append` map f n
theoremMapAppendS i f m n =
  bisim i lhs rhs (const ()) (\j -> theoremMapAppendS j f (tl m) n)
  where
    lhs
      =   map f (append m n)
      === map f ((hd m) `Cons` append (tl m) n)
      === f (hd ((hd m) `Cons` append (tl m) n))
            `Cons` map f (tl ((hd m) `Cons` append (tl m) n))
      === f (hd m) `Cons` map f (append (tl m) n)
    rhs
      =   map f m `append` map f n
      === (f (hd m) `Cons` map f (tl m)) `append` map f n
      === hd (f (hd m) `Cons` map f (tl m)) `Cons`
          append (tl (f (hd m) `Cons` map f (tl m))) (map f n)
      === f (hd m) `Cons` append (map f (tl m)) (map f n)

{-@ reflect isInfinite @-}
isInfinite Nil = False
isInfinite xs  = isInfinite (tl xs)

{-@ measure isInfiniteI :: Size -> List a -> Bool @-}

{-@ assume isInfiniteS :: i:Size
                       -> xs:ListNE _
                       -> ({j:Size| j<i} -> {isInfiniteI j (tl xs)})
                       -> {isInfiniteI i xs}
@-}
isInfiniteS :: Size
            -> List a
            -> (Size -> Proof)
            -> Proof
isInfiniteS i xs p = ()

{-@ assume isInfiniteAxiom :: xs:_
                           -> (i:Size -> {isInfiniteI i xs})
                           -> {isInfinite xs}
@-}
isInfiniteAxiom :: List a -> (Size -> Proof) -> Proof
isInfiniteAxiom _ _ = ()

{-@ reflect not @-}
not True  = False
not False = True

{-@ reflect isFinite @-}
isFinite = not . isInfinite
{-@ lemmaMapInfinite :: f:_ -> {xs:_|isInfinite xs}
                     -> {isInfinite (map f xs)}
@-}
lemmaMapInfinite f xs =
  isInfiniteAxiom (map f xs) (\i -> lemmaMapInfiniteS i f xs)
{-@ lemmaMapInfiniteS :: i:Size
                     -> f:_ -> {xs:_|isInfinite xs}
                     -> {isInfiniteI i (map f xs)}
@-}
lemmaMapInfiniteS :: Size -> (a -> b) -> List a -> Proof
lemmaMapInfiniteS i f xs@Nil = isInfinite xs === False *** QED
lemmaMapInfiniteS i f xxs@(Cons x xs) = isInfiniteS i (map f xxs) $ \j
  ->  tl (map f xxs)
  === tl (Cons (f x) (map f xs))
  === map f xs
    ? (isInfinite xxs === isInfinite xs *** QED)
    ? lemmaMapInfiniteS j f xs
  *** QED

