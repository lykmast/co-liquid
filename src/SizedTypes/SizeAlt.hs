{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

module SizedTypes.SizeAlt where

-- data Inf = Inf deriving Eq
--
-- data Size = F Int Int | I Inf Int deriving Eq
-- {-@ data Size = F Nat Nat | I Inf Nat @-}
--
-- {-@ fin :: Nat -> Size @-}
-- fin = flip F 0
--
-- inf = I Inf 0

-- bn :: SS -> SS
-- bn (F i n) = F i   n
-- bn (I _ n) = I Inf 1
--
-- {-@ inline val @-}
-- val (F i n) = i + n
--
-- lt :: SS -> SS -> Bool
-- F i n `lt` F j m = i < j && n < m
-- F _ _ `lt` I _   = True
-- I _   `lt` F _ _ = False
-- I n   `lt` I m   = n < m
--
-- {-@ assume newSS :: i:SS -> {j:SS| j < i} @-}
-- newSS :: SS -> SS
-- newSS = undefined
--
-- data IStream a = ICons a (IStream a)
--
-- {-@ measure isz :: IStream a -> SS @-}
--
-- {-@ type IStreamS a S = {xs: IStream a | isz xs = S} @-}
--
-- {-@ ihd :: j:SS -> {xs:IStream _ | j < isz xs} -> _ @-}
-- ihd :: SS -> IStream a -> a
-- ihd _ (ICons x _ ) = x
--
-- {-@ assume itl :: j:SS -> {xs:IStream _ | j < isz xs} -> IStreamS _ j @-}
-- itl :: SS -> IStream a -> IStream a
-- itl _ (ICons _ xs) = xs
--
-- {-@ assume mkIStream :: i:SS
--                     -> ({j:SS|j<i} -> a)
--                     -> ({j:SS|j<i} -> {xs:_| isz xs >= j})
--                     -> IStreamS _ i
-- @-}
-- mkIStream :: SS -> (SS -> a) -> (SS -> IStream a) -> IStream a
-- mkIStream i fx fxs = let j = newSS i
--                     in  ICons (fx j) (fxs j)
--
-- {-@ irepeat :: i:SS -> _ -> IStreamS _ i /[val i] @-}
-- irepeat i x = mkIStream i (const x) (\j -> irepeat j x)
