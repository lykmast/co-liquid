{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

module SizedTypes.BF where

import SizedTypes.Stream

type SS a = Stream (Stream a)
{-@ type SS a S = StreamG (StreamI a) S @-}

data Tree a = Node {_label :: a, _left :: Tree a, _right :: Tree a}

{-@ measure tsize :: Tree a -> Nat @-}
-- Infinitely deep defined trees are not used here, but I keep
--   tinf and TreeI for the sake of completeness.
{-@ measure tinf  :: Tree a -> Bool @-}
{-@ type TreeG a S = {v:Tree a | tsize v >= S} @-}
{-@ type TreeI a   = {v:Tree a | tinf v} @-}

{-@ label :: j:Nat -> {t:_ | tsize t > j || tinf t} -> _ @-}
label :: Int -> Tree a -> a
label _ = _label

{-@ assume left :: j:Nat
                -> {t:_ | tsize t > j || tinf t}
                -> {l:_| tsize l = j && (tinf t ==> tinf l)}
@-}
left  :: Int -> Tree a -> Tree a
left _ = _left

{-@ assume right :: j:Nat
                -> {t:_ | tsize t > j || tinf t}
                -> {r:_| tsize r = j && (tinf t ==> tinf r)}
@-}
right :: Int -> Tree a -> Tree a
right _ = _right


{-@ ilabel :: TreeI _ -> _ @-}
ilabel = label 0

{-@ ileft :: TreeI _ -> _ @-}
ileft = left 0

{-@ iright :: TreeI _ -> _ @-}
iright = right 0


{-@ assume node :: i:Nat
                  -> ({j:Nat|j<i} -> _)
                  -> ({j:Nat|j<i} -> TreeG _ j)
                  -> ({j:Nat|j<i} -> TreeG _ j)
                  -> {v:_ | tsize v = i}
@-}
node :: Int
       -> (Int -> a)
       -> (Int -> Tree a)
       -> (Int -> Tree a)
       -> Tree a
node i flb fl fr = Node (flb 0) (fl 0) (fr 0)

{-@ assume nodeI :: _ -> TreeI _ -> TreeI _ -> TreeI _ @-}
nodeI :: a -> Tree a -> Tree a -> Tree a
nodeI = Node


data Result a = Res {_tree:: Tree a, _rest:: SS a}

{-@ measure rsize :: Result a -> Nat @-}
{-@ measure rinf  :: Result a -> Bool @-}

{-@ type ResultI a I = {r:Result a | rsize r = I} @-}

{-@ assume  res :: i:Nat -> TreeG _ i
                  -> SS _ i -> ResultI _ i @-}
res :: Int -> Tree a -> SS a -> Result a
res _ t ss = Res t ss


{-@ assume tree :: r:_ -> TreeG _ {rsize r} @-}
tree = _tree
{-@ assume rest :: r:_ -> SS   _ {rsize r} @-}
rest = _rest


-- I have no idea how this works, I merely copied it from the
--  wellfounded recursion paper. The fact that it typechecks
--  means that I have probably (hopefully rather) gotten right
--  the underlying system.


{-@ bfs :: i:Nat -> SS _ i -> ResultI _ i @-}
bfs i ss = res i (node i v (\j -> tree $ p1 j)
                             $  \j -> tree $ p2 j)
                 $  cons i vs $ \j -> rest (p2 j)

           where p1  = \j -> bfs j (vss j)
                 p2  = \j -> bfs j $ rest $ p1 j
                 vss = \j -> stail j ss
                 v   = \j -> ihead (shead j ss)
                 vs  = \j -> itail (shead j ss)


-- bfp below is what we need to tie the knot. In the wellfounded recursion
--   paper the definition of bfp cannot be typechecked because it cannot
--   be written as an observation (with destructors) and therefore there
--   is not a j < i for bfp to recurse with. We on the other hand do
--   not have this problem because the cons constructor provides
--   a j<i.
{-@ bf :: i:Nat -> StreamI _ -> TreeG _ i @-}
bf i = tree . bfp i
  where {-@ bfp :: i:Nat -> StreamI a -> ResultI a i @-}
        bfp i vs = bfs i $ cons i (const vs) $ \j -> rest (bfp j vs)


-- For the sake of completeness we provide the two definitions of bfp
--   found in the paper.
{-@ bfp' :: i:Nat -> StreamI _ -> ResultI _ i @-}
bfp' :: Int -> Stream a -> Result a
bfp' i vs = res i (node i  (\j -> label j $ t j)
                              (\j -> left  j $ t j)
                              (\j -> right j $ t j))

                 $ cons i (\j -> shead    j $ r j)
                            $  \j -> stail    j $ r j
  where p j = bfs (j+1) $ cons (j+1)
                                   (const vs)
                                   (\_ -> rest $ bfp' j vs)
        t j = tree $ p j
        r j = rest $ p j


{-@ fixR :: i:Nat
         -> (j:Nat -> ResultI _ j -> ResultI _ {j+1})
         -> ResultI _ i
@-}
fixR :: Int -> (Int -> Result a -> Result a) -> Result a
fixR i f =  res i (node i  (\j -> label j $ t j)
                               (\j -> left  j $ t j)
                               (\j -> right j $ t j))

                  $ cons i (\j -> shead    j $ r j)
                             $  \j -> stail    j $ r j
  where p j = f j (fixR j f)
        t j = tree $ p j
        r j = rest $ p j

{-@ bfp'' :: i:Nat -> StreamI _ -> ResultI _ i @-}
bfp'' :: Int -> Stream a -> Result a
bfp'' i vs = fixR i f
  where f j r = bfs (j+1) $ cons (j+1)
                                     (const vs)
                                     (\_ -> rest r)

