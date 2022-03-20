{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--reflect" @-}
module SizedTypes.List where

import Prelude hiding(map, repeat, head, tail, reverse, length)
import SizedTypes.Size

data List a = Cons a (List a) | Nil
{-@ measure emp @-}
emp Nil = True
emp _   = False

{-@ measure lsize :: List a -> Size @-}
-- linf: is defined for infinite depth.
{-@ measure linf  :: List a -> Bool @-}

{-@ type ListI a = {xs:List a| linf xs} @-}

-- ListG: list with lsize greater than S
{-@ type ListG a S = {xs:List a| lsize xs >= S || linf xs} @-}
-- ListS: list with lsize equal to S
{-@ type ListS a S = {xs:List a| lsize xs  = S} @-}
-- ListNE: non-empty list
{-@ type ListNE a  = {xs:List a| not (emp xs)} @-}

{-@ assume mkNil :: {n:_| n = Nil && linf n} @-}
mkNil :: List a
mkNil = Nil

{-@ assume mkICons :: forall <p::a -> Bool>
                   . a<p>
                  -> ListI a<p>
                  -> ListI a<p>
@-}
mkICons = Cons

{-@ assume mkCons :: forall <p::a -> Bool>
                   . i:Size
                  -> ({j:Size|j<i} -> a<p>)
                  -> ({j:Size|j<i} -> ListG a<p> j)
                  -> v:ListS a<p> i
@-}
mkCons :: Size -> (Size -> a) -> (Size -> List a) -> List a
mkCons i fx fxs = Cons (fx 0) (fxs 0)

{-@ assume out :: forall <p::a -> Bool>
                . j:Size
               -> {xs:ListNE a<p> | j < lsize xs || linf xs}
               -> (_, {v:ListS a<p> j |linf xs ==> linf v})
@-}
out :: Size -> List a -> (a, List a)
out _ Nil         = undefined
out _ (Cons x xs) = (x, xs)

{-@ head :: forall <p::a -> Bool>
          . j:Size
         -> {xs:ListNE a<p> | j < lsize xs || linf xs}
         -> a<p>
@-}
head :: Size -> List a -> a
head j = fst . out j

{-@ tail :: forall <p::a -> Bool>
          . j:Size
         -> {xs:ListNE a<p> | j < lsize xs || linf xs}
         -> {v:ListS a<p> j | linf xs ==> linf v}
@-}
tail :: Size -> List a -> List a
tail j xs = snd $ out j xs

{-@ headi :: forall <p::a->Bool>. {xs:ListNE a<p>|linf xs} -> a<p> @-}
headi = head 0

{-@ taili :: forall <p::a->Bool>. {xs:ListNE a<p>|linf xs}
                               -> ListI a<p> @-}
taili = tail 0

{-@ repeat :: i:Size -> _ -> ListS _ i @-}
repeat :: Size -> a -> List a
repeat i x = mkCons i (const x) $ \j -> repeat j x

{-@ map :: i:Size -> _ -> ListG _ i -> ListG _ i @-}
map :: Size -> (a -> b) -> List a -> List b
map i _ Nil = mkNil
map i f xs  = mkCons i (\j -> f $ head j xs) $ \j -> map j f (tail j xs)

{-@ append :: i:Size -> xs: ListG _ i -> ys: ListG _ i -> ListG _ i @-}
append i Nil ys  = ys
append i xs  ys  = mkCons i (\j -> head j xs)
                          $  \j -> append j (tail j xs) ys
