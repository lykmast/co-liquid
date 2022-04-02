{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--prune-unsorted" @-} -- or else weird errors :/
module SizedTypes.StreamProofs where

import Prelude hiding (repeat, zipWith, map, not)
import Language.Haskell.Liquid.ProofCombinators
import SizedTypes.Size

-- Note that we use unsized streams, due to problems with reflection.
-- Also, without sizes in stream definitions, proofs are much clearer
--   than they would be.
-- Sizes in reflected functions are irrelevant if they have been already
-- accepted as productive/terminating.
data Stream a = a :> Stream a
infixr 5 :>

{-@ measure hd @-}
hd (x :> _ ) = x

{-@ measure tl @-}
tl (_ :> xs) = xs

-- Basically, to translate a co-predicate (predicate on streams) `p`
--   to this system we add an alternate version `pS` which results from
--   the initial predicate as follows:
--     - we give an assumed signature to `pS`
--     - we add all the arguments of `p`
--     - for every claim `c` on the observations of our co-inductive
--     object (stream) in `p` we add a proof term
--     in the signature of `pS`; that is a term `({j:Size|j<i} -> {c})`
--     - we add as a return type the term `{p ...args}`
--  Then in a proof we can prove `p` using `pS i` (co)recursively.
--  In simplified form:
--
--  ```
--  p  :: args -> Bool
--  p = c1 args && c2 args
--  {-@ assume pS :: i:Size -> args
--                -> ({j:Size|j<i} -> {c1 args})
--                -> ({j:Size|j<i} -> {c2 args}) -> {p args}
--  @-}
--  ps _ = ()
--
-- {-@ thP :: i:Size -> args -> {p args} @-}
-- thP args = pS i args (\j -> {- proof of c1 args -} ? ps j)
--                      (\j -> {- proof of c2 args -} ? ps j)
-- ```
-- As examples of such co-predicates we have bisim/= for bisimilarity
-- and belowS/below for lexicographic comparison of streams.

{-@ assume bisim :: i:Size
                 -> xs:_
                 -> ys:_
                 -> ({j:Size| j<i} -> {hd xs = hd ys})
                 -> ({j:Size| j<i} -> {tl xs = tl ys})
                 -> {xs = ys}
@-}
bisim :: Size -> Stream a -> Stream a
      -> (Size -> Proof) -> (Size -> Proof)
      -> Proof
bisim i xs ys p1 p2 = ()

{-@ reflect odds @-}
odds xs = hd xs :> (odds . tl . tl) xs

{-@ reflect evens @-}
evens = odds . tl

{-@ reflect merge @-}
merge xs ys = hd xs :> merge ys (tl xs)
{-@ thMergeEvensOdds :: i:Size -> xs:_
                     -> {merge (odds xs) (evens xs) = xs}
@-}
thMergeEvensOdds i xs
  = bisim i (merge (odds xs) (evens xs)) xs thHead thTail
  where
    thHead j
      =   hd (merge (odds xs) (evens xs))
      === hd (thMerge j)
      === hd (hd xs :> tl xs)
      === hd xs
      *** QED
    thTail j
      =   tl (merge (odds xs) (evens xs))
      === tl (thMerge j)
      === tl (hd xs :> tl xs)
      === tl xs
      *** QED

    thMerge j
      =   merge (odds xs) (evens xs)
      === hd (odds xs) :> merge (evens xs) (tl (odds xs))
      === hd (hd xs :> (odds . tl.tl) xs) :>
               merge (odds . tl $ xs) (tl (odds xs))
      === hd xs :> merge (odds (tl xs)) (odds . tl $tl xs)
      === hd xs :> merge (odds (tl xs)) (evens (tl xs))
        ? thMergeEvensOdds j (tl xs)
      === hd xs :> tl xs

-- should be accepted only with lazy annotation. Now passes because of
-- no-adt.
{-@ reflect below @-}
below :: Stream Int -> Stream Int -> Bool
below xs ys = hd xs <= hd ys
            && ((hd xs == hd ys) `implies` below (tl xs) (tl ys))

{-@ reflect implies @-}
{-@ implies :: p:Bool -> q:Bool -> {v:_| v <=> (p => q)} @-}
implies False _ = True
implies _ True = True
implies _ _ = False

{-@ assume belowS :: i:Size
                 -> xs:_
                 -> ys:_
                 -> ({j:Size| j<i} -> {hd xs <= hd ys})
                 -> ({j:Size| j<i} -> { (hd xs == hd ys) =>
                                        (below (tl xs) (tl ys)) })
                 -> {below xs ys}
@-}
belowS :: Size -> Stream Int -> Stream Int
      -> (Size -> Proof) -> (Size -> Proof)
      -> Proof
belowS i xs ys p1 p2 = ()

{-@ reflect mult @-}
mult :: Stream Int -> Stream Int -> Stream Int
mult xs ys = hd xs * hd ys :> mult (tl xs) (tl ys)


{-@ theoremBelowSquare :: i:Size -> xs:_ -> {below xs (mult xs xs)} @-}
theoremBelowSquare :: Size -> Stream Int -> Proof
theoremBelowSquare i xs = belowS i xs (mult xs xs) thHead thTail
  where
    thHead j
      =   hd (thMult j)
      === hd xs * hd xs
      =>= hd xs
      *** QED
    thTail j
      =   tl (thMult j)
      === mult (tl xs) (tl xs)
        ? theoremBelowSquare j (tl xs)
      *** QED
    thMult j
      =   mult xs xs
      === hd xs * hd xs :> mult (tl xs) (tl xs)

-- trueStream is another (trivial) co-predicate.
{-@ reflect trueStream @-}
trueStream xs = trueStream (tl xs)

{-@ assume trueStreamS :: i:Size -> xs:_
                       -> ({j:Size| j<i} -> ())
                       -> ({j:Size| j<i} -> {trueStream (tl xs)})
                       -> {trueStream xs}
@-}
trueStreamS :: Size -> Stream a
            -> (Size -> Proof)
            -> (Size -> Proof)
            -> Proof
trueStreamS i xs p1 p2 = ()

{-@ thTrueStream :: i:Size -> xs:_ -> {trueStream xs} @-}
thTrueStream i xs = trueStreamS i xs (\j -> ())
                                     (\j -> thTrueStream j (tl xs))

-----------------------------------------------
-- | f morse == morse
-- This example is from `Durel and Lucanu 2009`

{-@ reflect map @-}
map :: (a -> b) -> Stream a -> Stream b
map f xs = f (hd xs) :> map f (tl xs)

{-@ reflect morse @-}
morse :: Stream Bool
morse = False :> True :> merge (tl morse) (map not (tl morse))

{-@ reflect f @-}
f :: Stream Bool -> Stream Bool
f xs = hd xs :> not (hd xs) :> f (tl xs)

{-@ reflect not @-}
not True = False
not False = True

-- | Note that `theoremFMorse` does not use coinduction (no self call)
-- so there is no need to use `bisim`.
{-@ theoremFMorse :: {f morse = morse} @-}
theoremFMorse
  =   f morse
  === hd fMorse :> ht :> tt
  *** QED
  where
    tt
      =   tl tlFMorse
      === f (tl morse)
        ? theoremFMerge 0 (tl morse)
      === merge (tl morse) (map not (tl morse))
      === tl tlMorse

    ht
      =   hd tlFMorse
      === True
      === hd tlMorse

    morse'
      =   morse
      === False :> True :> merge (tl morse) (map not (tl morse))

    fMorse
      =   f morse
      === hd morse :> not (hd morse') :> f (tl morse)
      === hd morse :> True :> f (tl morse)

    tlFMorse = tl fMorse === True :> f (tl morse)

    tlMorse = tl morse' === True :> merge (tl morse) (map not (tl morse))

{-@ theoremFMerge :: i:Size -> xs:_
                  -> {f xs = merge xs (map not xs)}
@-}
theoremFMerge i xs
  = bisim i (f xs) (merge xs (map not xs)) thHead thTail
  where
    thHead _
      =   hd (f xs)
      === hd (hd xs :> not (hd xs) :> f (tl xs))
      === hd xs
      === hd mergeXsNotXs
      *** QED

    thTail j
      =   tl mergeXsNotXs
      === merge (map not xs) (tl xs)
      === merge (not (hd xs) :> map not (tl xs)) (tl xs)
      === not (hd xs) :> merge (tl xs) (map not (tl xs))
        ? theoremFMerge j (tl xs)
      === not (hd xs) :> f (tl xs)
      === tl (f xs)
      *** QED


    mergeXsNotXs
      =   merge xs (map not xs)
      === hd xs :> merge (map not xs) (tl xs)

{-@ theoremNotF :: i:Size -> xs:_
                     -> {map not (f xs) = f (map not xs)}
@-}
theoremNotF i xs
  = bisim i (map not (f xs)) (f (map not xs)) thHead thTail
  where
    mapNotFXS j
      =   map not (f xs)
      === map not (hd xs :> not (hd xs) :> f (tl xs))
      === not (hd xs) :>
        ( -- tail part expanded:
             map not (not (hd xs) :> f (tl xs))
         === not (not (hd xs)) :> map not (f (tl xs))
         ?   theoremNotF j (tl xs)
         === not (not (hd xs)) :> f (map not (tl xs))
        )

    thHead j
      =   hd (mapNotFXS j)
      === not (hd xs)
      === hd (not (hd xs) :> map not (tl xs))
      === hd (map not xs)
      === hd (f (map not xs))
      *** QED

    thTail j
      =   tl (mapNotFXS j)
      === not ( -- expanding this term:
                   not (hd xs)
               === hd (not (hd xs) :> map not (tl xs))
               === hd (map not xs)
              )
                                :> f (map not (tl xs))
      === not (hd (map not xs)) :> f (tl (map not xs))
      === tl (f (map not xs))
      *** QED

