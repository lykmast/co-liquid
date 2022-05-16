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
--   to this system we add an alternate version `pS`
--   an uninterpreted measure `pI`
--   and an axiom `pAxiom` binding `pI` with p,
--   which result from the initial predicate as follows:
--     - `pI` is of type :: Nat -> t, where t is the type of p.
--     - we give an assumed signature to `pS`
--     - we add all the arguments of `p`
--     - for every claim `c` on the observations of our co-inductive
--     object (stream) in `p` we add a proof term
--     in the signature of `pS`; that is a term `({j:Size|j<i} -> {c})`
--     - we add as a return type the term `{pI i ...args}`
--  Then in a proof we can prove `pI i` using `pS i` (co)recursively
--  and finally `p` using `pAxiom`.
--  In simplified form:
--
--  ```
--  p  :: args -> Bool
--  p = c1 args && c2 args
--
--  {-@ measure pI :: Nat -> args -> Bool @-}
--  {-@ assume pS :: i:Size -> args
--                -> ({j:Size|j<i} -> {c1 args})
--                -> ({j:Size|j<i} -> {c2 args}) -> {pI i args}
--  @-}
--  pS _ = ()
--
--  {-@ assume pAxiom :: args -> (i:Nat -> {pI i args}) -> {p args} @-}
--  pAxiom _ _ = ()
--
-- {-@ thPS :: i:Size -> args -> {pI i args} @-}
-- thP args = pS i args (\j -> {- proof of c1 args -} ? ps j)
--                      (\j -> {- proof of c2 args -} ? ps j)
--
-- {-@ thP :: args -> {p args} @-}
-- thP args = pAxiom args (\i -> pS i args)
-- ```
-- As examples of such co-predicates we have bisim/= for bisimilarity
-- and belowS/below for lexicographic comparison of streams.
{-@ measure eqI :: Size -> Stream a -> Stream a -> Bool @-}

{-@ assume eqAxiom :: xs:_ -> ys:_ -> (i:Size -> {eqI i xs ys}) -> {xs = ys} @-}
eqAxiom :: Stream a -> Stream a -> (Size -> Proof) -> Proof
eqAxiom _ _ _ = ()

{-@ assume bisim :: i:Size
                 -> xs:_
                 -> ys:_
                 -> ({j:Size| j<i} -> {hd xs = hd ys})
                 -> ({j:Size| j<i} -> {eqI j (tl xs) (tl ys)})
                 -> {eqI i xs ys}
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

{-@ thMergeEvensOdds :: xs:_ -> {merge (odds xs) (evens xs) = xs} @-}
thMergeEvensOdds :: Stream a -> Proof
thMergeEvensOdds xs
  = eqAxiom (merge (odds xs) (evens xs)) xs (thMergeEvensOddsS xs)

{-@ thMergeEvensOddsS :: xs:_ -> i:Size
                     -> {eqI i (merge (odds xs) (evens xs)) xs}
@-}
thMergeEvensOddsS xxs@(x :> xs) i
  = bisim i lhs xxs (const ()) (thMergeEvensOddsS xs)
  where
    lhs
      =   merge (odds xxs) (evens xxs)
      === hd (odds xxs) :> merge (evens xxs) (tl (odds xxs))
      === hd (x :> (odds . tl.tl) xxs) :>
               merge (odds . tl $ xxs) (tl (odds xxs))
      === x :> merge (odds xs) (odds . tl $xs)
      === x :> merge (odds xs) (evens xs)

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

{-@ measure belowI :: Size -> Stream a -> Stream a -> Bool @-}
{-@ assume belowS :: i:Size
                 -> xs:_
                 -> ys:_
                 -> ({j:Size| j<i} -> {hd xs <= hd ys})
                 -> ({j:Size| j<i} -> { (hd xs == hd ys) =>
                                        (belowI j (tl xs) (tl ys)) })
                 -> {belowI i xs ys}
@-}
belowS :: Size -> Stream Int -> Stream Int
      -> (Size -> Proof) -> (Size -> Proof)
      -> Proof
belowS i xs ys p1 p2 = ()

{-@ reflect mult @-}
mult :: Stream Int -> Stream Int -> Stream Int
mult xs ys = hd xs * hd ys :> mult (tl xs) (tl ys)


{-@ assume belowAxiom :: xs:_
                      -> ys:_
                      -> (i:Size -> {belowI i xs ys})
                      -> {below xs ys} @-}
belowAxiom :: Stream Int -> Stream Int -> (Size -> Proof) -> Proof
belowAxiom _ _ _ = ()

{-@ theoremBelowSquare :: xs:_ -> {below xs (mult xs xs)} @-}
theoremBelowSquare xs =
  belowAxiom xs (mult xs xs) (theoremBelowSquareS xs)

{-@ theoremBelowSquareS :: xs:_ -> i:Size -> {belowI i xs (mult xs xs)} @-}
theoremBelowSquareS xxs@(x:>xs) i =
  belowS i lhs rhs (const ()) (theoremBelowSquareS xs)
  where
    lhs = x:>xs
    rhs
      =   mult xxs xxs
      === x * x :> mult xs xs

{-@ measure trueStreamI :: Size -> Stream a -> Bool @-}
-- trueStream is another (trivial) co-predicate.
{-@ reflect trueStream @-}
trueStream xs = trueStream (tl xs)

{-@ assume trueStreamAxiom :: xs:_
                           -> (i:Size -> {trueStreamI i xs})
                           -> {trueStream xs}
@-}
trueStreamAxiom :: Stream a -> (Size -> Proof) -> Proof
trueStreamAxiom _ _ = ()

{-@ assume trueStreamS :: i:Size -> xs:_
                       -> ({j:Size| j<i} -> ())
                       -> ({j:Size| j<i} -> {trueStreamI j (tl xs)})
                       -> {trueStreamI i xs}
@-}
trueStreamS :: Size -> Stream a
            -> (Size -> Proof)
            -> (Size -> Proof)
            -> Proof
trueStreamS i xs p1 p2 = ()

{-@ thTrueStream :: xs:_ -> {trueStream xs} @-}
thTrueStream xs = trueStreamAxiom xs (thTrueStreamS xs)
  where
    {-@ thTrueStreamS :: xs:_ -> i:Size -> {trueStreamI i xs} @-}
    thTrueStreamS xxs@(_:>xs) i =
      trueStreamS i xxs (const ()) (thTrueStreamS xs)

-- -----------------------------------------------
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
        ? theoremFMerge (tl morse)
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

{-@ theoremFMerge :: xs:_ -> {(f xs) = merge xs (map not xs)} @-}
theoremFMerge xs =
  eqAxiom (f xs) (merge xs (map not xs)) (theoremFMergeS xs)

{-@ theoremFMergeS :: xs:_ -> i:Size
                  -> {eqI i (f xs) (merge xs (map not xs))}
@-}
theoremFMergeS xxs@(x :> xs) i
  = bisim i lhs rhs (const ())
  $ \j -> bisim j tlLhs tlRhs (const ()) (theoremFMergeS xs)
  where
    lhs
      =   f xxs
      === x :> not x :> f xs
    rhs
      =   merge xxs (map not xxs)
      === x :> merge (map not xxs) xs

    tlRhs
      =   tl rhs
      === merge (map not xxs) xs
      === merge (not x :> map not xs) xs
      === not x :> merge xs (map not xs)

    tlLhs
      =   tl lhs
      === not x :> f xs

{-@ theoremNotF :: xs:_ -> {map not (f xs) = f (map not xs)} @-}
theoremNotF xs =
  eqAxiom (map not (f xs)) (f (map not xs)) (theoremNotFS xs)

{-@ theoremNotFS :: xs:_ -> i:Size
                     -> {eqI i (map not (f xs)) (f (map not xs))}
@-}
theoremNotFS xxs@(x :> xs) i
  =       bisim i lhs  rhs    (\_ -> ())
  $ \j -> bisim j tlLhs tlRhs (\_ -> ()) (theoremNotFS xs)
  where
    lhs
      =   map not (f xxs)
      === map not (x :> not x :> f xs)
      === not x :> map not (not x :> f xs)
      === not x :> not (not x) :> map not (f xs)

    rhs
      =   f (map not xxs)
      === f (not x :> map not xs)
      === not x :> not (not x) :> f (map not xs)

    tlRhs
      =   tl rhs
      === not (not x) :> f (map not xs)

    tlLhs
      =   tl lhs
      === not (not x) :> map not (f xs)
