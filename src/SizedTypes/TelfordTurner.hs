{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--reflection" @-}

module SizedTypes.TelfordTurner where
import SizedTypes.Stream

{-@ comap :: i:Nat -> _ -> StreamG _ i -> StreamG _ i @-}
comap i f xs = cons i (\j -> f (shead j xs)) (\j -> comap j f (stail j xs))

{-@ evenNums :: i:Nat -> StreamG _ i @-}
evenNums i = cons i (const 2) (\j -> comap j (+2) (evenNums j))

{-@ iter :: i:Nat -> _ -> _ -> StreamG _ i @-}
iter i f x = cons i (const x) $ \j -> iter j f (f x)

{-@ mergeOrd :: i:Nat -> StreamG _ i -> StreamG _ i -> StreamG _ i @-}
mergeOrd :: Ord a => Int -> Stream a -> Stream a -> Stream a
mergeOrd i xs ys = cons i (\j -> min (shead j xs) (shead j ys))
                            $ (\j -> res j xs ys)

  where {-@ res :: {j:Nat| j<i} -> StreamG _ i
                -> StreamG _ i ->StreamG _ j @-}
        res j xs ys = case compare (shead j xs)  (shead j ys) of
                        LT -> mergeOrd j (stail j xs) ys
                        EQ -> mergeOrd j (stail j xs) (stail j ys)
                        GT -> mergeOrd j xs        (stail j ys)

{-@ ham :: i:Nat -> StreamG _ i @-}
ham i = cons i (const 1) $ \j -> mergeOrd j (comap j (*2) (ham j))
                                              $  comap j (*3) (ham j)

