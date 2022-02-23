# co-liquid
Coinduction in Liquid Haskell


I will write here summaries of coinduction papers in terms of how they implement various features (i.e. proofs, termination etc.). These are not all-inclusive; I keep mainly what I think is pertinent to the co-liquid project.

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
 - 2. To guarantee soundness (?) they must also appeat in *co-friendly* positions (i.e. in negation normal form under existential quantification the quantification must be over a finite range - probably not relevant in Haskell).

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

Below is the theorem that connects co-predicates with prefix predicates:

`forall x. Q(x) <=> forall k. _Qk(x).`

### Co-methods
Co-methods are coinductive proofs. As with co-predicates, co-methods define prefix methods. A cluster containing a co-method must only contain co-methods and prefix methods. Both co-methods and prefix methods are always ghosts (their code is noly relevant to the verifier and not part of the executable).

A prefix method is constructed by a co-method by:
  - adding a `k:Nat` parameter to denote prefix length.
  - replacing in the comethod's postcondition co-predicates (that are in positive co-friendly positions) with prefix predicates that have `k` as the prefix length parameter(!!not in the precondition).
  - replace intra-cluster calls with the corresponding prefix method with `k-1` as the prefix length. Note that non-intra-cluster calls are not replaced. Also we can still use prefix versions explicitly in comethods (or even lfp theorems; e.g. `lemmaTailSubStreamK` from [Filter.hs](src/Filter.hs)).
  - making the body's execution conditional on `k /= 0`. For `k == 0` the proof will be trivial because of prefix predicates.

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

### TODO for Co-induction Simply
- A way to exclude co-recursive calls from termination checks e.g in `fivesUp` above.
- A way to reference full co-inductive lemmas/predicates (not just prefixed versions).
- (Not strictly relevant to co-liquid) Is there a way to reflect `filter'` (from [Filter.hs](src/Filter.hs) along with proof terms? 

## 2. [Well-founded recursion with copatterns and sized types](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/39794AEA4D0F5003C8E9F88E564DA8DD/S0956796816000022a.pdf/well-founded-recursion-with-copatterns-and-sized-types.pdf)

Sizes are ordinals including an `ω : ω >= i forall i`.

This part of the paper gives a high-level idea of size based termination checking:

>When we check a corecursive definition such as the second clause of `zipWith`, we start with traversing the lhs. We first introduce assumption `i≤∞` into the context and now hit the measure annotation `|i|` in the type. At this point, we introduce the assumption `zipWith : ∀j≤∞. |j|<|i| ⇒ ∀A:∗. ∀B:∗. ∀C:∗. (A → B → C) → StreamjA → StreamjB → StreamjC` which will be used to check the recursive call on the rhs. It has a constraint `|j| < |i|`, a lexicographic comparison of size expression tuples (which here just means `j < i`), that is checked before applying `zipWith j` to `A`. Continued checking of the lhs introduces further assumptions `A, B, C : ∗`, `f : A → B → C`, `s : StreamiA`,` t : StreamiB`, and` j < i`. Checking the rhs succeeds since the constraint `|j| < |i|` is satisfied and `s .tail j : StreamjA` and `t .tail j : StreamjB`
The paper has also co-patterns, which I have not used here. I have instead converted all co-patterns to regular patterns.

*Pseudo-haskell below.*


### Infinite Streams

```haskell
data IStream{i} a = ICons{i,(νj<i)} {ihead :: a, itail:: (IStream{j} a)}
```

ICons provides a new `j` the relationship `i>j` and makes it available downstream.

```haskell
ICons{i,(νj<i)} :: a -> IStream{j} a -> IStream{i} a
```


`ihead`, `itail` need a witness `j>i` that in `itail` serves also as the size of the result:

```haskell
ihead{i,j(j<i)} :: IStream{i} a -> a
itail{i,j(j<i)} :: IStream{i} a -> IStream{j} a
```

e.g `xs` has depth/size: `k < j < i = size ys`

```haskell
ys = a `ICons{i,j}` (b `ICons{j,k}` xs)
```

Here in `zipWith` and `repeat`, `ICons{i,j}` creates `j,i>j` and makes them available for `ihead`, `itail` and `zipWith`.

```haskell
repeat{i} :: a -> IStream{i} a
repeat{i} x = x `ICons{i,j}` repeat{j} x

zipWith{i} :: (a->b->c) -> IStream{i} a -> IStream{i} b -> IStream{i} c
zipWith{i} f as bs = 
  f (ihead{i,j} as) (ihead{i,j} bs)
  `ICons{i,j}` zipWith{j} f (itail{i,j} as) (itail{i,j} bs)


fib{i} :: IStream{i} Int
fib{i} =
  0 `ICons{i,j}` (1 `ICons{j,k}` zipWith{k} fib{k} (itail{j,k} fib{j}))
```

The following wrong `zipWith'` will not typecheck because there is not an ordinal available that can be placed at `?`.

```haskell
zipWith'{i} f as bs = 
  f (ihead{j,?} (itail{i,j} as)) (ihead{j,?} (itail{i,j} bs)) 
  `ICons{i,j}` zipWith'{j} f (itail{i,j} as) (itail{i,j} bs)
```


### CoLists

```haskell
data CoList{i} a = MCons{i,(νj<i)}{out :: Maybe(a, CoList{j} a)}

MCons{i,(νj<i)} :: Maybe (a, CoList{j} a) -> CoList{i} a
out{i,j(j<i)} :: CoList{i} a -> Maybe(a, CoList{j} a)

safeHead{i,j(j<i)} :: CoList{i} a -> Maybe a
safeHead{i,j} = fmap fst . out{i,j}

safeTail{i,j(j<i)} :: CoList{i} a -> Maybe (CoList{j} a)
safeTail{i,j} = fmap snd . out{i,j}

repeat'{i} :: a -> CoList{i} a
repeat'{i} x = MCons{i,j} $ Just (x, repeat'{j} x)


fmap1 :: (a -> c) -> Maybe (a,b) -> Maybe (c,b)
fmap1 f = fmap . first

fmap2 :: (b -> d) -> Maybe (a,b) -> Maybe (a,d)
fmap2 f = fmap . second


unfold{i} :: (s -> Maybe (a,s)) -> s -> CoList{i} a
unfold{i} f s = MCons{i,j} $ fmap2 (unfold{j} f) (f{i,j} s)

repeatUnfold :: a -> CoList{ω} a
repeatUnfold a = unfold{ω} (\() -> Just(a,())) ()


map{i} :: (a -> b) -> CoList{i} a -> CoList{i} b
map{i} f (MCons{i,j} (Just (x,xs)))
  = MCons{i,j} (Just (f x, map{j} f xs))
map{i} _ (MCons Nothing)
  = MCons Nothing
```

We can implement `map` with `unfold` if we type `unfold` more precisely:

```haskell
unfold{i} :: (Λ j k<j. s{j} -> Maybe (a,s{k})
          -> (Λ j. s{j})
          -> CoList{i} a
unfold{i} f s = MCons{i,j} $ fmap2 (unfold{j} f) (f{i,j} s)

map{i} f = unfold{i} (\{i,j<i} s -> fmap1 f (out{i,j} s{i}))
```


Below we use LLists which are isomorphic to CoLists but with more familiar syntax:

```haskell
data LList{i} = Cons{i,j} {head :: a, tail :: (List{j} a)} | Nil
```

Here `head`, `tail` and `Cons` are similar to `ihead`, `itail` and `ICons` respectively.

```haskell
repeat{i} :: a -> LList{i} a
repeat{i} x = x `Cons{i,j}` repeat{j} x

map{i} :: (a -> b) -> LList{i} a -> LList{i} b
map{i} _ Nil         = Nil
map{i} f (Cons x xs) = f x `Cons{i,j}` map{j} f xs
```

### Label trees

```haskell
type SS{i} a = IStream{i} (IStream{ω} a)

data Tree{i} = Node{i,(νj<i)}
    { label :: a
    , left  :: Tree{j} a,
    , right :: Tree{j} a
    }

label{i,j<i} :: Tree{i} a -> a
left{i,j<i}  :: Tree{i} a -> Tree{j} a
right{i,j<i} :: Tree{i} a -> Tree{j} a

data Result{i} a = Res{i} {tree :: Tree{i} a, rest :: SS{i} a}


tree{i} :: Result{i} a -> Tree{i} a
rest{i} :: Result{i} a -> SS{i} a
```

This takes a stream of streams and returns a tree that has each level labeled by its correspondent stream.

```haskell
bfs{i} :: SS{i} a -> Result{i} a
bfs{i} ((v `ICons{ω}` vs) `ICons{i,j}` vss) 
  =  Res{i} (Node{i,j} v (tree{j} p1) (tree{j} p2)) $ vs `ICons{i,j}` rest p2
  where
    p1 = bfs{j} vss
    p2 = bfs{j} (rest{j} p1)
```

Here `p1` and `p2` definitions reference `j (<i)` which becomes available to them from `Node{i,j}` and `ICons{i,j}` resp. at their call site.

The size `j` is not important in itself. What we care about is the constraint `j<i`.

The algorithm is completed with `bf` which takes a stream of labels and returns a tree labeled by the stream in breadth-first order:

```haskell
bf{i} :: IStream{ω} a -> Tree{i} a
bf{i} vs = t where Res{i} t vss = bfs{i} (vs `ICons{i,j}` vss)
```

Note that in the rhs of the where clause `vss` can be safely cast to a smalller depth `j` (from the lhs it has depth `i > j`).

### Other examples

Odds and evens can only work on fully defined streams. All destructors without an ordinal use `ω` implicitly. Ordinals `i` and `j` are only used to prove productivity.

```haskell
odds{i} :: IStream{ω} a -> IStream{ω} a
odds{i} xs = ihead xs `ICons{i,j}` odds{j} (itail (itail xs))

evens :: IStream{ω} a -> IStream{ω} a
evens = odds . itail

merge{i} :: IStream{i+1} a -> IStream{i} -> IStream{i} a
merge{i} xs ys = ihead{i+1,i} xs `ICons{i,j}` merge{j} ys (itail{i+1,i} xs)
```

Here `paperfolds` is more difficult to typecheck (despite being productive). We can typecheck it by unfolding `merge` once in its definition.

```haskell
toggle{i} :: IStream{i} a
toggle{i} = 1 `Cons{i,j}` (0 `Cons{j,k}` toggle{j})

-- This would not typecheck because paperfolds does not have a
-- terminating measure.
paperfolds{i} :: IStream{i} a
paperfolds{i} = merge{i} toggle{i+1} paperfolds{?}

-- This is the version that typechecks (applying one 
--   unfolding of merge).
paperfolds{i} = ihead toggle `ICons{i,j}` 
                 merge{j} paperfolds{j} (itail toggle)
```

Mixed induction and coinduction works by using the ordinal and the inductive termination metric as a lexicographic termination metric.

```haskell
{-@ fivesUp{i} :: n:_ -> IStream {v:_ | v >= n} / [i, fivesUpTerm n] @-}
fivesUp :: Int -> IStream Int
-- the first clause has i<j (guarded by coinductive constructor)
fivesUp n | n `mod` 5 == 0 = n `ICons{i,j}` fivesUp{j} (n+1)
-- the second clause has decreasing fivesUpTerm n.
          | otherwise      = fivesUp (n+1)

{-@ inline fivesUpTerm @-}
fivesUpTerm :: Int -> Int
fivesUpTerm n = 4 - ((n-1) `mod` 5)
```

### Theorems & Proofs

In order to implement theorems and proofs we need to:
 1. find a way to implement coinductive predicates; that is predicates that are of the form `CoindType -> Bool`. The problem here is that such predicates are not terminating since (in the general case) we need to observe an infinite object to produce a result.
 2. find a way to implement coinductive proofs on those predicates. This is not straight-forward because we need to provide a context where a coinductive proof can co-recurse on itself (i.e. provide an ordinal...).

An idea is instead of having predicates `:: a -> Bool`, which would not terminate, to use predicates that can be partially observed i.e. embeded in a co-inductive structure. This would also offer a context for co-inductive proofs to recurse. Implementation from [SizedStreamProofs.hs](src/SizedStreamProof.hs):

```haskell
data BS = Bool :&& BS | Bool :|| BS

{-@ reflect evalBS @-}
evalBS :: BS -> Bool
evalBS (b :&& rest) = b && evalBS rest
evalBS (b :|| rest) = b || evalBS rest


{-@ reflect belowS @-}
belowS :: Ord a => IStream a -> IStream a -> BS
belowS (ICons x xs) (ICons y ys)
  = x <= y :&& (x < y :|| belowS xs ys)

{-@ theoremBelowMult :: a:IStream Int -> {evalBS (belowS a (mult a a))}@-}
theoremBelowMult :: IStream Int -> ()
theoremBelowMult (ICons a as)
  = evalBS (
      belowS (ICons a as) (mult (ICons a as) (ICons a as))
  === belowS (ICons a as) (ICons (a * a) (mult as as))
  === (a <= a*a :&& ( a < a*a :|| belowS as (mult as as))))
  ===
    evalBS (a < a*a :|| (belowS as (mult as as) ? theoremBelowMult as))
  *** QED
```

However `evalBS` as it is can prove `{false}`:

```haskell
{-@ reflect falsesOr @-}
falsesOr = False :|| falsesOr

{-@ lemmaFalse :: _ -> {false} @-}
lemmaFalse (ICons x xs)
  =   evalBS falsesOr
  === evalBS (False :|| (falsesOr ? lemmaFalse xs))
  *** QED
```

### TODO for sized types

- Is this typing equivalent to having co-patterns?
- Can sized types be encoded in Liquid Haskell?
- Is there a way to make the predicate/proof implementation sound? 
