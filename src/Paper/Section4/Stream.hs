{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

module Paper.Section5.Stream where

import Prelude hiding (not)

data Stream a = a :> Stream a
infixr 5 :>

{-@ measure shead @-}
shead (x :> _ ) = x

{-@ measure stail @-}
stail (_ :> xs) = xs

-- pointwise product of streams
{-@ reflect mult @-}
mult :: Stream Int -> Stream Int -> Stream Int
mult (a :> as) (b :> bs) = a * b :> mult as bs

{-@ reflect implies @-}
{-@ implies :: p:Bool -> q:Bool -> {v:_| v <=> (p => q)} @-}
implies x y = not x || y

-- intercalate
{-@ reflect merge @-}
merge :: Stream a -> Stream a -> Stream a
merge (x :> xs) ys = x :> (merge ys xs)

{-@ reflect odds @-}
odds  :: Stream a -> Stream a
odds (x :> xs) = x :> (odds (stail xs))

{-@ reflect evens @-}
evens :: Stream a -> Stream a
evens xs = odds (stail xs)

{-@ reflect morse @-}
morse :: Stream Bool
morse = False :> True :> merge (stail morse) (smap not (stail morse))

{-@ reflect ff @-}
ff :: Stream Bool -> Stream Bool
ff xs = shead xs :> not (shead xs) :> ff (stail xs)

{-@ reflect smap @-}
smap :: (a -> b) -> Stream a -> Stream b
smap f (x :> xs) = f x :> smap f xs

{-@ reflect not @-}
not False = True
not True  = False
-----------------------------------------
-- | Predicates

{-@ reflect dup @-}
dup (x :> y :> xs) = x == y && dup xs

-- lexicographic comparison
{-@ reflect below @-}
below :: Ord a => Stream a -> Stream a -> Bool
below (x :> xs) (y :> ys)
  = x <= y && ((x == y) `implies` below xs ys )

-- trivial predicate
{-@ reflect trivial @-}
trivial :: Stream a -> Bool
trivial (_ :> xs) = trivial xs

{-@ reflect nneg @-}
nneg :: Stream Int -> Bool
nneg (x :> xs) = x >= 0 && nneg xs
