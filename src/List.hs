{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
module List where

import Prelude hiding(map, infinite)
data List a = a :| (List a) | Nil
infixr 5 :|

{-@ infix :| @-}
{-@ measure emp @-}
emp Nil = True
emp _   = False

{-@ type ListNE a = {v:List a | not (emp v)} @-}
{-@ type Emp    a = {v:List a | emp v } @-}

{-@ measure lhead @-}
{-@ lhead :: ListNE _ -> _ @-}
lhead (x :| _ ) = x

{-@ measure ltail @-}
{-@ ltail :: ListNE _ -> _ @-}
ltail (_ :| xs) = xs

{-@ reflect map @-}
{-@ map :: _ -> xs:_ -> {v:_|emp xs <=> emp v} @-}
map :: (a -> b) -> List a -> List b
map _ Nil       = Nil
map f (x :| xs) = (f x) :| map f xs

-- | Predicates
{-@ reflect infinite @-}
infinite (x :| xs) = infinite xs
infinite Nil       = False
