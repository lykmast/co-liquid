{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

module SizedTypes.CoList where

import Data.Bifunctor
import SizedTypes.Size

data CoList a = CL (Maybe (a, CoList a))

{-@ measure size :: CoList a -> Size @-}

{-@ type CoListS a S = {xs:CoList a| size xs = S} @-}

{-@ assume mCons :: i:Size
                 -> ({j:Size|j<i} -> Maybe (_,{xs:_| size xs >= j}))
                 -> {v:_| size v = i} @-}
mCons :: Size -> (Size -> Maybe (a,CoList a)) -> CoList a
mCons i fxxs = CL (fxxs 0)

{-@ assume out :: j:Size
               -> {xs:CoList a | j < size xs}
               -> Maybe (_, CoListS _ j)
@-}
out :: Size -> CoList a -> Maybe (a, CoList a)
out _ (CL Nothing)       = Nothing
out _ (CL (Just (x,xs))) = Just (x, xs)

{-@ safeHead :: j:Size -> {xs:CoList _ | j < size xs} -> Maybe _ @-}
safeHead :: Size -> CoList a -> Maybe a
safeHead j = fmap fst . out j

{-@ safeTail :: j:Size -> {xs:CoList _ | j < size xs}
             -> Maybe (CoListS _ j)
@-}
safeTail :: Size -> CoList a -> Maybe (CoList a)
safeTail j = fmap snd . out j

{-@ repeat' :: i:Size -> _ -> CoListS _ i @-}
repeat' :: Size -> a -> CoList a
repeat' i x = mCons i $ \j -> Just (x, repeat' j x)


fmap1 :: (a -> c) -> Maybe (a,b) -> Maybe (c,b)
fmap1 = fmap . first

fmap2 :: (b -> d) -> Maybe (a,b) -> Maybe (a,d)
fmap2 = fmap . second

{-@ unfold :: i:Size -> _ -> _ -> CoListS _ i @-}
unfold :: Size -> (s -> Maybe (a,s)) -> s -> CoList a
unfold i f s = mCons i $ \j -> fmap2 (unfold j f) (f s)

newtype Sized a = Sized {fromSized :: a}
{-@ measure ssize :: Sized a -> Size @-}
-- {-@ assume smap :: _ -> x:Sized _ -> SSized _ {ssize x}@-}
-- smap f (Sized x) = Sized (f x)

{-@ type SSized a S = {v:Sized a | ssize v = S} @-}

{-@ assume clFromSized :: s:Sized (CoList _)
                          -> CoListS _ {ssize s} @-}
clFromSized :: Sized (CoList a) -> CoList a
clFromSized (Sized xs) = xs

{-@ assume mkSizedCL :: xs:CoList _ -> SSized _ {size xs} @-}
mkSizedCL :: CoList a -> Sized (CoList a)
mkSizedCL = Sized

repeatUnfold :: a -> CoList a
repeatUnfold a = unfold 0 (\() -> Just(a,())) ()

{-@ unfold' :: i:Size
            -> (k:Size -> {l:Size| l<k}
                  -> s:SSized _ k -> Maybe (_, SSized _ l))
            -> SSized _ i
            -> CoListS _ i
@-}
unfold' :: Size
        -> (Size -> Size -> Sized a -> Maybe (b, Sized a))
        -> Sized a
        -> CoList b
unfold' i f s = mCons i $ \j -> fmap2 (unfold' j f)
                                    (f i j s)

{-@ map :: i:Size -> _ -> CoListS _ i -> CoListS _ i @-}
map :: Size -> (a -> b) -> CoList a -> CoList b
map i f cl =
  unfold' i
      (\k l s -> fmap2 mkSizedCL . fmap1 f . out l . clFromSized $ s)
      (mkSizedCL cl)

{-@ assume sizedUnit :: i:Size -> SSized _ i @-}
sizedUnit :: Size -> Sized ()
sizedUnit _ = Sized ()


repeatUnfold' :: a -> CoList a
repeatUnfold' a = unfold' 0 (\_ l _ -> Just(a,sizedUnit l))
                              (sizedUnit 0)

