{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Paper.Section1 where

import Language.Haskell.Liquid.ProofCombinators

-- | 2.1 Inductive Data

infixr :>
data Stream a =  a :> Stream a | E

{-@ measure notEmpty @-}
notEmpty :: Stream a -> Bool
notEmpty E = False
notEmpty _ = True

-- | 2.2 Inductive Light Verification

{-@ reflect smap @-}
{-@ smap :: (a -> b) -> x:Stream a -> {s:Stream b | slen s == slen x }  @-}
smap :: (a -> b) -> Stream a -> Stream b
smap _ E = E
smap f (x :> xs) = f x :> smap f xs

{-@ measure slen @-}
slen :: Stream a -> Int
{-@ slen :: Stream a -> Nat @-}
slen E = 0
slen (_ :> xs) = 1 + slen xs


{-@ type NEStream a = {x:Stream a | notEmpty x} @-}


{-@ measure shead @-}
{-@ measure stail @-}

{-@ shead :: NEStream a -> a @-}
{-@ stail :: NEStream a -> Stream a @-}
shead :: Stream a -> a
stail :: Stream a -> Stream a
shead (x :> _ ) = x
stail (_ :> xs) = xs

safe :: Int -> Stream Int -> Int
safe x xs = shead (smap (+1) (x :> xs))


{-@ ignore unsafe @-}
unsafe :: Stream Int -> Int
unsafe xs = shead xs

-- | 2.3 Inductive Deep Verification

{-@ mapFusion :: f:(b -> c) -> g:(a -> b) -> xs:Stream a
            -> { smap f (smap g xs) == smap (f . g) xs } @-}
mapFusion :: (b -> c) -> (a -> b) -> Stream a -> ()
mapFusion f g E = ()
mapFusion f g (x :> xs)
  =   smap f (smap g (x :> xs))
  === smap f (g x :> smap g xs)
  === f (g x) :> smap f (smap g xs)
      ? mapFusion f g xs
  === (f . g) x :> smap (f . g) xs
  === smap (f . g) (x :> xs)
  *** QED

-- | 2.4 What about coinduction?

falseStream :: Stream a -> ()
{-@ falseStream :: Stream a -> {false} @-}
falseStream (_ :> xs) = falseStream xs
falseStream _ = undefined


{-@ mapFusion' :: f:(b -> c) -> g:(a -> b) -> xs:Stream a
            -> { smap f (smap g xs) == smap (f . g) xs } @-}
mapFusion' :: (b -> c) -> (a -> b) -> Stream a -> ()
mapFusion' f g xs = falseStream xs
