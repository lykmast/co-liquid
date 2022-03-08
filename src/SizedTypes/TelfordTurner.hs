{-@ LIQUID "--no-adt" @-}
module SizedTypes.TelfordTurner where
import SizedTypes.Size
import SizedTypes.Stream

{-@ comap :: i:Size -> _ -> StreamG _ i -> StreamG _ i @-}
comap i f xs = mkStream i (\j -> f (hd j xs)) (\j -> comap j f (tl j xs))

{-@ evenNums :: i:Size -> StreamG _ i @-}
evenNums i = mkStream i (const 2) (\j -> comap j (+2) (evenNums j))

{-@ iter :: i:Size -> _ -> _ -> StreamG _ i @-}
iter i f x = mkStream i (const x) $ \j -> iter j f (f x)

{-@ mergeOrd :: i:Size -> StreamG _ i -> StreamG _ i -> StreamG _ i @-}
mergeOrd :: Ord a => Size -> Stream a -> Stream a -> Stream a
mergeOrd i xs ys = mkStream i (\j -> min (hd j xs) (hd j ys))
                            $ (\j -> res j xs ys)

  where {-@ res :: {j:Size| j<i} -> StreamG _ i
                -> StreamG _ i ->StreamG _ j @-}
        res j xs ys = case compare (hd j xs)  (hd j ys) of
                        LT -> mergeOrd j (tl j xs) ys
                        EQ -> mergeOrd j (tl j xs) (tl j ys)
                        GT -> mergeOrd j xs        (tl j ys)

{-@ ham :: i:Size -> StreamG _ i @-}
ham i = mkStream i (const 1) $ \j -> mergeOrd j (comap j (*2) (ham j))
                                              $  comap j (*3) (ham j)

