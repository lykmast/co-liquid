{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-structural-termination" @-}
{-@ LIQUID "--no-adt" @-}

module Paper.Section3 where

import Prelude hiding (take, map)

import Language.Haskell.Liquid.ProofCombinators hiding (QED, (***))


-- | 3.1 Consistent Approach: Indexed Properties

{-@ ignore falseStream @-}
falseStream :: Stream a -> (Int -> ())
{-@ falseStream :: Stream a -> k:Nat -> {false} / [k] @-}
falseStream _ 0 = ()
falseStream (_ :> xs) i = falseStream xs (i-1)


-- | 3.2 Precise Approach: Indexed Predicates

{-@ reflect eqK @-}
{-@ eqK :: Eq a => Stream a -> Stream a -> Nat -> Bool @-}
eqK :: Eq a => Stream a -> Stream a -> Int -> Bool
eqK _ _ 0 = True
eqK (x :> xs) (y :> ys) i = x == y && eqK xs ys (i-1)



{-@ mapFusionIdx :: xs:Stream a -> f:(b -> c) -> g:(a -> b)
            -> k:Nat -> {v : () | eqK (smap f (smap g xs)) (smap (f . g) xs) k } / [k]@-}
mapFusionIdx :: Eq c => Stream a -> (b -> c) -> (a -> b) -> Int -> ()
mapFusionIdx xs f g 0 = eqK (smap f (smap g xs)) (smap (f . g) xs)  0 *** QED
mapFusionIdx (x :> xs) f g k
  =   smap f (smap g (x :> xs))
  === smap f (g x :> smap g xs)
  === f (g x) :> smap f (smap g xs)
      ? mapFusionIdx xs f g (k-1)
  =#=  k #
      (f . g) x :> smap (f . g) xs
  === smap (f . g) (x :> xs)
  *** QED

-- | Proof Combinators:
infix 0 ***

data QED = QED
_ *** QED = ()

infixr 1 #
(#) = ($)

infix 2 =#=
{-@ (=#=) :: Eq a => x:Stream a -> k:{Nat | 0 < k }
          -> y:{Stream a | eqK (stail x) (stail y) (k-1)  && shead x == shead y }
          -> {v:Stream a | eqK x y k && v == x } @-}
(=#=) :: Eq a => Stream a -> Int -> Stream a -> Stream a
(=#=)  xxs@(x :> xs) k yys@(y :> ys) =
   xxs ? (eqK xxs yys k === (x == y && eqK xs ys (k-1)) *** QED)

-- | 3.3 Take Lemma: Did we prove Equality?

-- | HERE

{-@ reflect take @-}
{-@ take :: Nat -> Stream a -> [a] @-}
take :: Int -> Stream a -> [a]
take 0 _ = []
take i (x :> xs) = x:take (i-1) xs

{-@ assume takeLemma :: x:Stream a -> y:Stream a
                     -> (n:Nat -> {v:() | take n x = take n y})
                     -> {x = y} @-}
takeLemma :: Stream a -> Stream a -> (Int -> ()) -> ()
takeLemma _ _ _ = ()


{-@ eqLemma :: x:Stream a -> y:Stream a -> n:Nat
                     -> {(take n x = take n y) <=> eqK x y n} @-}
eqLemma :: Eq a => Stream a -> Stream a -> Int -> ()
eqLemma xs ys 0
  = eqK xs ys 0 ? take 0 xs ? take 0 ys  *** QED
eqLemma (x :> xs) (y :> ys) i
  =   take i (x :> xs) == take i (y :> ys)
  === (x:take (i-1)xs == y:take (i-1) ys)
  === (x == y && take (i-1) xs == take (i-1) ys)
       ? eqLemma xs ys (i-1)
  === (x == y && eqK xs ys (i-1))
  === eqK (x :> xs) (y :> ys) i
  *** QED

{-@ approx :: x:Stream a -> y:Stream a
           -> (n:Nat -> {v:() | eqK x y n })
           -> { x = y } @-}
approx :: Eq a => Stream a -> Stream a -> (Int -> ()) -> ()
approx xs ys p =  takeLemma xs ys (\n -> (p n ? eqLemma xs ys n))



{-@ mapFusion :: f:(b -> c) -> g:(a -> b) -> xs:Stream a
            -> { smap f (smap g xs) == smap (f . g) xs } @-}
mapFusion :: Eq c => (b -> c) -> (a -> b) -> Stream a -> ()
mapFusion f g xs = approx (smap f (smap g xs)) (smap (f . g) xs) (mapFusionIdx xs f g)

-- | As in Section 2 without boxes
infixr :>
data Stream a =  a :> Stream a

{-@ reflect smap @-}
smap :: (a -> b) -> Stream a -> Stream b
smap f (x :> xs) = f x :> smap f xs
{-@ measure shead @-}
{-@ measure stail @-}

shead :: Stream a -> a
stail :: Stream a -> Stream a
shead (x :> _ ) = x
stail (_ :> xs) = xs


