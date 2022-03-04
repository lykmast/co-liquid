{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

module SizedTypes.BF where

import SizedTypes.Size
import SizedTypes.Stream

type SS a = Stream (Stream a)
{-@ type SS a S = StreamG (StreamI a) S @-}

data Tree a = Node {_label :: a, _left :: Tree a, _right :: Tree a}

{-@ measure tsize :: Tree a -> Size @-}
-- Infinitely deep defined trees are not used here, but I keep
--   tinf and ITree for the sake of completeness.
{-@ measure tinf  :: Tree a -> Bool @-}
{-@ type STree a S = {v:Tree a | tsize v >= S} @-}
{-@ type ITree a   = {v:Tree a | tinf v} @-}

{-@ label :: j:Size -> {t:_ | tsize t > j || tinf t} -> _ @-}
label :: Size -> Tree a -> a
label _ = _label

{-@ assume left :: j:Size
                -> {t:_ | tsize t > j || tinf t}
                -> {l:_| tsize l = j && (tinf t ==> tinf l)}
@-}
left  :: Size -> Tree a -> Tree a
left _ = _left

{-@ assume right :: j:Size
                -> {t:_ | tsize t > j || tinf t}
                -> {r:_| tsize r = j && (tinf t ==> tinf r)}
@-}
right :: Size -> Tree a -> Tree a
right _ = _right


{-@ ilabel :: ITree _ -> _ @-}
ilabel = label 0

{-@ ileft :: ITree _ -> _ @-}
ileft = left 0

{-@ iright :: ITree _ -> _ @-}
iright = right 0


{-@ assume mkTree :: i:Size
                  -> ({j:Size|j<i} -> _)
                  -> ({j:Size|j<i} -> STree _ j)
                  -> ({j:Size|j<i} -> STree _ j)
                  -> {v:_ | tsize v = i}
@-}
mkTree :: Size
       -> (Size -> a)
       -> (Size -> Tree a)
       -> (Size -> Tree a)
       -> Tree a
mkTree i flb fl fr | i >= 0    = let j = newSize i
                                 in  Node (flb j) (fl j) (fr j)
                   | otherwise = undefined

{-@ assume mkITree :: _ -> ITree _ -> ITree _ -> ITree _ @-}
mkITree :: a -> Tree a -> Tree a -> Tree a
mkITree = Node


data Result a = Res {_tree:: Tree a, _rest:: SS a}

{-@ measure rsize :: Result a -> Size @-}
{-@ measure rinf  :: Result a -> Bool @-}

{-@ type ResultI a I = {r:Result a | rsize r = I} @-}

{-@ assume  mkRes :: i:Size -> STree _ i
                  -> SS _ i -> ResultI _ i @-}
mkRes :: Size -> Tree a -> SS a -> Result a
mkRes _ t ss = Res t ss


{-@ assume tree :: r:_ -> STree _ {rsize r} @-}
tree = _tree
{-@ assume rest :: r:_ -> SS   _ {rsize r} @-}
rest = _rest


-- I have no idea how this works, I merely copied it from the
--  wellfounded recursion paper. The fact that it typechecks
--  means that I have probably (hopefully rather) gotten right
--  the underlying system.


{-@ bfs :: i:Size -> SS _ i -> ResultI _ i @-}
bfs i ss = mkRes i (mkTree i v (\j -> tree $ p1 j)
                             $  \j -> tree $ p2 j)
                 $  mkStream i vs $ \j -> rest (p2 j)

           where p1  = \j -> bfs j (vss j)
                 p2  = \j -> bfs j $ rest $ p1 j
                 vss = \j -> tl j ss
                 v   = \j -> hdi (hd j ss)
                 vs  = \j -> tli (hd j ss)


-- bfp below is what we need to tie the knot. In the wellfounded recursion
--   paper the definition of bfp cannot be typechecked because it cannot
--   be written as an observation (with destructors) and therefore there
--   is not a j < i for bfp to recurse with. We on the other hand do
--   not have this problem because the mkStream constructor provides
--   a j<i.
{-@ bf :: i:Size -> StreamI _ -> STree _ i @-}
bf i = tree . bfp i
  where {-@ bfp :: i:Size -> StreamI a -> ResultI a i @-}
        bfp i vs = bfs i $ mkStream i (const vs) $ \j -> rest (bfp j vs)


-- For the sake of completeness we provide the two definitions of bfp
--   found in the paper.
{-@ bfp' :: i:Size -> StreamI _ -> ResultI _ i @-}
bfp' :: Size -> Stream a -> Result a
bfp' i vs = mkRes i (mkTree i  (\j -> label j $ t j)
                              (\j -> left  j $ t j)
                              (\j -> right j $ t j))

                 $ mkStream i (\j -> hd    j $ r j)
                            $  \j -> tl    j $ r j
  where p j = bfs (j+1) $ mkStream (j+1)
                                   (const vs)
                                   (\_ -> rest $ bfp' j vs)
        t j = tree $ p j
        r j = rest $ p j


{-@ fixR :: i:Size
         -> (j:Size -> ResultI _ j -> ResultI _ {j+1})
         -> ResultI _ i
@-}
fixR :: Size -> (Size -> Result a -> Result a) -> Result a
fixR i f =  mkRes i (mkTree i  (\j -> label j $ t j)
                               (\j -> left  j $ t j)
                               (\j -> right j $ t j))

                  $ mkStream i (\j -> hd    j $ r j)
                             $  \j -> tl    j $ r j
  where p j = f j (fixR j f)
        t j = tree $ p j
        r j = rest $ p j

{-@ bfp'' :: i:Size -> StreamI _ -> ResultI _ i @-}
bfp'' :: Size -> Stream a -> Result a
bfp'' i vs = fixR i f
  where f j r = bfs (j+1) $ mkStream (j+1)
                                     (const vs)
                                     (\_ -> rest r)

