# co-liquid
Coinduction in Liquid Haskell


I write here:
 - summaries of coinduction papers in terms of how they implement various features (i.e. proofs, termination etc.). These are not all-inclusive; I keep mainly what I think is pertinent to the co-liquid project.
 - my take on the implementation of these features with Liquid Haskell.

## 1. [Co-induction Simply](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/coinduction.pdf)
Automatic Co-inductive Proofs in a Program Verifier
K. Rustan M. Leino Michał Moskal"

Keyword summary: Parametric co-induction, No copatterns, decreases clause, syntactic guard, recursive/co-recursive calls.

This paper describes the coinduction implementation in Dafny. The technique is what is described as "parametric coinduction" where coinductive proofs/predicates/functions are transformed (automatically) to inductive ones with the use of a parameter k:Nat (essentialy coinductive objects are syntactic sugar for their inductive counterparts).

### Co-datatypes
Same syntax as datatypes. Semantically they define the greatest fixpoint of the given definition. No grounding checks for codatatypes in contrast to datatypes (check that there is a way to construct a value from the ground up). 

e.g. pseudo-Haskell equivalent to Dafny.

```haskell
codata Stream a = SNil | SCons {head:: a, tail: Stream a}
```

### Co-functions
There are no co-functions; only intra-cluster calls that are classified as either recursive or co-recursive.

#### Recursive calls
They are subject to termination checks. No other obligation.

#### Co-recursive calls
To ensure that they are consistent they must only occur in productive positions (it must be possible to determine each successive piece of the resulting co-datatype value after a finite amount of work). This condition is satisfied if every co-recursive call is syntactically *guarded* by a constructor of a co-datatype.
Co-recursive calls are exempt from termination checks. They also must be lazy (which in haskell is not a problem but in LH we have to denote it).
Each function can have both recursive and co-recursive calls.

e.g. from [IStream.hs](src/IStream.hs)

```haskell
{-@ lazy fivesUp @-}
{-@ fivesUp :: n:_ -> _  @-} 
  -- this does nothing because of lazy: / [fivesUpTerm n] @-}
fivesUp :: Int -> Stream Int
-- the first self call is in a productive position and can therefore
--  be exempt from termination checks (classified as co-inductive).
fivesUp n | n `mod` 5 == 0 = n `SCons` fivesUp (n+1)
-- the second self call is not guarded by a constructor and so it
--  is classified as inductive. The termination check is satisfied
--  by the metric we have provided above. In Dafny this is done
-- automatically while in LH we add a manual assertion.

          | otherwise = 
            liquidAssert (fivesUpTerm (n+1) < fivesUpTerm n)
                         $ fivesUp (n+1)
{-@ inline fivesUpTerm @-}
fivesUpTerm :: Int -> Int
fivesUpTerm n = 4 - (n-1) `mod` 5
```

In the above example we notice that the termination metric is *only* applied to the inductive call.

### Co-predicates
Co-predicates describe properties of co-datatypes. Co-predicates must be monotonic in order to guarantee existence of greatest fix-point. This is enforced by syntactic restriction on the form of the body of co-predicates:
 - 1. Intra-cluster calls of co-predicates must appear only in *positive* positions (i.e. as non negated atoms).
 - 2. To guarantee soundness (?) they must also appear in *co-friendly* positions (i.e. in negation normal form under existential quantification the quantification must be over a finite range - probably not relevant in Haskell).

e.g

```haskell
p1 x y = x && not (p2 y x)  -- intra-cluster call negated 
p2 x y = x && p1 (x || y) y
```

Co-predicate declarations also define a prefix predicate (a finite unrolling of a co-predicate). The prefix predicate is constructed from the co-predicate by:
  - adding a `k:Nat` parameter to denote prefix length
  - adding a `decreases k` clause (automatic in Haskell)
  - replace intra-cluster calls with corresponding prefix predicate with `k-1` as prefix length.
  - adding a case for `k==0` for which the prefix predicate results to true.
Note that equality must also be transformed to prefix form i.e `s==t` becomes `eqK k s t`.

Below is the axiom that connects co-predicates with prefix predicates ported to Liquid Haskell (and generalized for a predicate q):

```haskell
{-@ assume daxiom_q :: x:_ -> (k:Nat -> {_qK k x}) -> {q x} @-}
daxiom_q _ _ = ()

{-@ assume daxiom_q_r :: x:_ -> {q x} -> k:Nat -> {_qK k x} @-}
daxiom_q_r _ _ = ()
```

### Co-methods
Co-methods are coinductive proofs. As with co-predicates, co-methods define prefix methods. A cluster containing a co-method must only contain co-methods and prefix methods. Both co-methods and prefix methods are always ghosts (their code is noly relevant to the verifier and not part of the executable).

A prefix method is constructed by a co-method by:
  - adding a `k:Nat` parameter to denote prefix length.
  - replacing in the comethod's postcondition co-predicates (that are in positive co-friendly positions) with prefix predicates that have `k` as the prefix length parameter(!!not in the precondition).
  - replace intra-cluster calls with the corresponding prefix method with `k-1` as the prefix length. Note that non-intra-cluster calls are not replaced. Also we can still use prefix versions explicitly in comethods (or even lfp theorems; e.g. `lemmaTailSubStreamK` from [Filter.hs](src/Filter.hs)).
  - making the body's execution conditional on `k /= 0`. For `k == 0` the proof will be trivial because of prefix predicates.


### Proof example

As an example of proofs and predicates encoded with this method in Liquid Haskell we provide the `thMergeEvensOdds` and the equality predicate that it uses:

```haskell
{-@ assume dAxiom_eq :: xs:_ -> ys:_
                     -> (k:Nat -> {eqK k xs ys}) -> {xs = ys} @-}
dAxiom_eq :: Eq a => IStream a -> IStream a -> (Int -> Proof) -> Proof
dAxiom_eq _ _ _ = ()

{-@ assume dAxiom_eq_r :: xs:_ -> ys:_ -> {v:Proof| xs = ys}
                       -> k:Nat -> {eqK k xs ys} @-}
dAxiom_eq_r :: Eq a => IStream a -> IStream a -> Proof -> Int -> Proof
dAxiom_eq_r _ _ _ _ = ()

{-@ reflect eqK @-}
{-@ eqK :: k: Nat -> _ -> _ -> _ @-}
eqK :: (Eq a) => Int -> IStream a -> IStream a -> Bool
eqK 0 _ _ = True
eqK k (ICons a as) (ICons b bs) = a == b && eqK (k-1) as bs

{-@ _lemmaEvenOddK :: k: Nat -> xs:_ -> {eqK k (merge (odds xs) (evens xs)) xs} @-}
_lemmaEvenOddK :: (Eq a) => Int -> IStream a -> Proof
_lemmaEvenOddK 0 s
  =   eqK 0 (merge (odds s) (evens s)) s
  *** QED
_lemmaEvenOddK k (ICons x xs)
  =   eqK k (merge (odds (ICons x xs)) (evens (ICons x xs))) (ICons x xs)
  === eqK k (merge (ICons x (odds (itail xs))) ((odds . itail) (ICons x xs))) (ICons x xs)
  === eqK k (merge (ICons x ((odds . itail) xs)) (odds xs)) (ICons x xs)
  === eqK k (ICons x (merge (odds xs) (evens xs))) (ICons x xs)
  === eqK (k-1) (merge (odds xs) (evens xs)) xs
    ? _lemmaEvenOddK (k-1) xs
  *** QED


{-@ lemmaEvenOdd :: xs:_ -> {merge (odds xs) (evens xs) = xs} @-}
lemmaEvenOdd :: Eq a => IStream a -> Proof
-- lemmaEvenOdd (ICons x xs)
--   =   merge (odds (ICons x xs)) (evens (ICons x xs))
--   === merge (ICons x (odds (itail xs))) ((odds . itail) (ICons x xs))
--   === merge (ICons x ((odds . itail) xs)) (odds xs)
--   === ICons x (merge (odds xs) (evens xs))
--     ? lemmaEvenOdd xs
--   === ICons x xs
--   *** QED

lemmaEvenOdd xs = dAxiom_eq (merge (odds xs) (evens xs)) xs
                            (\k -> _lemmaEvenOddK k xs)

```

More examples can be found in the [src](src) directory.

### Limitations
Termination cannot be proven for some functions i.e

```haskell
zipWith :: (a -> b -> c) -> IStream a -> IStream b -> IStream c
zipWith f (ICons x xs) (ICons y ys) = ICons (f x y) $ zipWith f xs ys

fib :: IStream Int
fib = ICons 0 (ICons 1 (zipWith (+) fib (itail fib)))
```

cannot be proven to terminate. In Dafny there is an `{:abstemious}` annotation which is described [here](https://curatedcsharp.com/p/dafny-is-dafny-lang-dafny/index.html) as follows:

"Abstemious functions: Allow functions to be annotated with {:abstemious}. Such a function is checked not to consume too much. More precisely, an abstemious function can only codatatype-destruct parameters and must return with a co-constructor.

Abstemious functions, together with a new computation of a guaranteed minimum number of co-constructor wrappers, expand the number of functions that are considered to be productive. As a result, many new interesting co-recursive functions can be written."

`zipWith` can be so annotated and typechecks in dafny but it is achieved through syntactic checks and is less general than e.g. sized types.

To sum up: termination/productivity checks for functions are achieved through:
  - co-recursion in part of the co-inductive type (e.g. tail of stream).
  - decreases clause (manually added with liquidAssert) in inductive calls.

## 2. Co-Induction with sized types
This approach follows Agda's implementation of co-induction as described in [Well-founded recursion with copatterns and sized types](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/39794AEA4D0F5003C8E9F88E564DA8DD/S0956796816000022a.pdf/well-founded-recursion-with-copatterns-and-sized-types.pdf) and [MiniAgda: Integrating Sized and Dependent Types](https://arxiv.org/abs/1012.4896).

Sizes are ordinals including an `ω : ω >= i forall i`.

This part of the paper gives a high-level idea of size based termination checking, while explaining the definitions of `zipWith` and `fib`:

```agda
zipWith : ∀i∞. |i| ⇒ ∀A:∗. ∀B:∗. ∀C:∗.
(A → B → C) → Streami A → Streami B → Streami C
zipWith i A B C f s t .head j = f (s .head j) (t .head j)
zipWith i A B C f s t .tail j = zipWith j A B C f (s .tail j) (t .tail j)

fib : ∀i. |i| ⇒ Streami
fib i .head j = 0
fib i .tail j .head k = 1
fib i .tail j .tail k = zipWith k (+) (fib k) (fib j .tail k)
```
>When we check a corecursive definition such as the second clause of `zipWith`, we start with traversing the lhs. We first introduce assumption `i≤∞` into the context and now hit the measure annotation `|i|` in the type. At this point, we introduce the assumption `zipWith : ∀j≤∞. |j|<|i| ⇒ ∀A:∗. ∀B:∗. ∀C:∗. (A → B → C) → StreamjA → StreamjB → StreamjC` which will be used to check the recursive call on the rhs. It has a constraint `|j| < |i|`, a lexicographic comparison of size expression tuples (which here just means `j < i`), that is checked before applying `zipWith j` to `A`. Continued checking of the lhs introduces further assumptions `A, B, C : ∗`, `f : A → B → C`, `s : StreamiA`,` t : StreamiB`, and` j < i`. Checking the rhs succeeds since the constraint `|j| < |i|` is satisfied and `s .tail j : StreamjA` and `t .tail j : StreamjB`
The paper has also co-patterns, which I have not used here. I have instead converted all co-patterns to regular patterns.

### Implementation
In general what we need to emulate co-pattern behaviour is for constructors to *provide* a smaller ordinal at each level (analogously to lhs destructors) and for destructors to *need* a smaller ordinal (like rhs destructors in Agda). Also we must restrict functions to recurse only with smaller ordinals, but that is taken care of by the normal termination checking that Liquid Haskell has.

Here we have implemented the above behaviour in Liquid Haskell by hard-coding size properties on constructors and destructors. To see how stream constructors/destructors are implemented visit [Stream.hs](src/SizedTypes/Stream.hs).

With this system in place we can write all the examples from the original paper in Liquid Haskell and get them checked for productivity.


Below are the `zipWith` and `fib` definitions as found in [Stream.hs](src/SizedTypes/Stream.hs).

```haskell
{-@ zipWith :: i:Size -> _
            -> StreamG _ i
            -> StreamG _ i
            -> StreamG _ i
@-}
zipWith :: Size -> (a -> a -> a) -> Stream a -> Stream a -> Stream a
zipWith i f xs ys = mkStream i
                      (\j -> hd j xs `f` hd j ys)
                      $ \j -> zipWith j f (tl j xs) (tl j ys)

{-@ fib :: i:Size -> StreamG _ i @-}
fib :: Num a => Size -> Stream a
fib i = mkStream i (const 0)
          $ \j -> mkStream j (const 1)
          $ \k -> zipWith k (+) (fib k) (tl k (fib j))
```

In the [SizedTypes](src/SizedTypes) directory there are other examples including functions on lazy lists, streams and (infinite) trees. A decently complex example can be found in [BF.hs](src/SizedTypes/BF.hs), where we implement a breadth first labeling of an infinite binary tree with labels from an infinite stream.


### Theorems & Proofs
We use `bisim` from MiniAgda to encode bisimilarity (and through it equality) for co-inductive types. The general idea is that, if all the observables of two co-inductive objects (e.g `hd`, `tl` for streams) are equal, so are the whole objects. In Liquid Haskell we encode bisimilarity like so ([StreamProofs.hs](src/SizedTypes/StreamProofs.hs)):

```haskell
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
```

Here, inspired from MiniAgda, we provide the individual proof functions with a `j<i` so as to allow recursion. This works as a productivity/soundness checker just like in co-inductive constructors. With this system in place we can now perform co-induction by recursing on a proof using the smaller ordinal provided by the co-predicate (i.e. `bisim`). 

To demonstrate the use of `bisim`, I have added below the `thMergeEvensOdds` proof taken from [StreamProofs.hs](src/SizedTypes/StreamProofs.hs):

```haskell
{-@ reflect odds @-}
odds xs = Cons (hd xs) (odds . tl.tl $xs)

{-@ reflect evens @-}
evens = odds . tl

{-@ reflect merge @-}
merge xs ys = Cons (hd xs) $ merge ys (tl xs)
{-@ thMergeEvensOdds :: i:Size -> xs:_
                     -> {merge (odds xs) (evens xs) = xs}
@-}
thMergeEvensOdds i xs
  = bisim i (merge (odds xs) (evens xs)) xs thHead thTail
  where
    thHead j
      =   hd (merge (odds xs) (evens xs))
      === hd (thMerge j)
      === hd (Cons (hd xs) (tl xs))
      === hd xs
      *** QED
    thTail j
      =   tl (merge (odds xs) (evens xs))
      === tl (thMerge j)
      === tl (Cons (hd xs) (tl xs))
      === tl xs
      *** QED

    thMerge j
      =   merge (odds xs) (evens xs)
      === Cons (hd (odds xs)) (merge (evens xs) (tl (odds xs)))
      === Cons (hd (Cons (hd xs) (odds .tl.tl$xs)))
               (merge (odds . tl $xs) (tl (odds xs)))
      === Cons (hd xs) (merge (odds (tl xs)) (odds . tl $tl xs))
      === Cons (hd xs) (merge (odds (tl xs)) (evens (tl xs)))
        ? thMergeEvensOdds j (tl xs)
      === Cons (hd xs) (tl xs)
``` 

As we can see the proof is clear and very near to what we would write with pen and paper. 

Note that in proofs we use definitions without sizes. This is not problematic since the termination/productivity of objects is not necessary in the proofs. The only thing we use sizes for is to establish the productivity of the proof itself, via sizes `j<i` provided by `bisim`.

We can also define other co-predicates (such as `bisim`). Other co-predicates are only briefly mentioned in MiniAgda, so what follows is an interpolation from the definition of `bisim`.

Basically, to translate a co-predicate (predicate on co-inductive objects) `p` into this system we add an alternate version `pS` which results from the initial predicate as follows:
   - we give an assumed signature to `pS`
   - we add all the arguments of `p`
   - for every claim `c` on the observations (on streams: `hd`, `tl`) of our co-inductive object (stream) in `p` we add a proof term in the signature of `pS`; that is a term `({j:Size|j<i} -> {c})`
   - we add as a return type the term `{p ...args}`
Then in a proof we can prove `p` using `pS i` (co)recursively. In simplified form:

```haskell
p  :: args -> Bool
p = c1 args && c2 args
{-@ assume pS :: i:Size -> args
              -> ({j:Size|j<i} -> {c1 args})
              -> ({j:Size|j<i} -> {c2 args}) -> {p args}
@-}
ps _ = ()

{-@ thP :: i:Size -> args -> {p args} @-}
thP args = pS i args (\j -> {- proof of c1 args -} ? ps j)
                     (\j -> {- proof of c2 args -} ? ps j)
```

For example here is a predicate lexicographically comparing two streams:
```haskell
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
```

**Note:** We probably need some way to check that a predicate can be interpreted co-inductively. Since in MiniAgda there are no co-predicates (other than bisimilarity) we can use the criterion of monotonicity as per [Co-induction Simply](#co-predicates). 

## Comparison of the two approaches
Below there is a small comparison of how each approach handles co-recursion in functions and co-inductive proofs.

### Functions

In coinductive functions there is the consideration of productivity (from MiniAgda paper: "always yielding the next piece of the output in finite time"). 

In the approach taken by Co-induction Simply, to ensure productivity/termination, functions are allowed to recurse either inductively with a decreasing metric or co-inductively by guarding the recursion with a co-constructor. This is achieved through a simple syntactic check. 

Inductively recursive branches in co-inductive functions are thusly checked to eventually return to the co-recursive branch, which in turn is guaranteed to always provide a piece of output (through the co-constructor guard) and only then (co-)recurse.

In Agda's approach the co-recursing is conversely ensured by tracking guardedness through sized types. We use sizes to encode the depth at which a co-inductive object is defined and we modify the constructors and destructors to expect/provide smaller sizes as witnesses of depth. Also, sizes are set up to be used as termination metrics. These two properties of sizes allow them to act as a productivity metric.

Agda's types are significantly more expressive than Dafny's syntactic check, as partially demonstrated by the way `zipWith` and `fib` can be implemented in [Dafny](#limitations) and in [Agda](#implementation).


### Proofs
Co-inductive proofs are not well-founded; they don't have a ground truth to eliminate towards. That disallows us from implementing them with normal recursion since we don't have a base case. What we need to ensure is that a proof is productive in some sense.

Dafny tackles this by transforming co-induction to induction on a natural parameter which can be interpreted as the depth of the proof or predicate. Predicates on depth 0 serve as our base case (trivial) and every co-recursion is transformed to a recursion on the one-less-deep proof.

In (Mini)Agda this notion of depth is already captured by sizes, so we can seamlessly use sizes for proofs as well (after setting up the necessary rules). What Agda goes on to express is that we can evoke a proof recursively only if we have provided a partial reason for which the proof holds for our current depth and only in that context can we dive deeply.

In both approaches, proofs are ensured to be well constructed via termination checks on the depth metric. The resulting proofs are in both cases quite near to pen-and-paper proofs.

### Overall

Sized types seem to be more expressive in dealing with co-induction than the parametric approach proposed by Co-induction Simply. 

The main disadvantage of sized types (as currently implemented) is the cluttering of function definitions with size annotations for productivity and the resulting need to rewrite definitions without sizes in order to obtain readable proofs.

There are more arguments to be made regarding the way each approach will be implemented (in terms of desugaring, syntactic checks etc.), but that requires a slightly deeper consideration.
