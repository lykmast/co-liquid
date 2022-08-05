# Coinduction Inductively
Auxiliary code for **_Coinduction Inductively - Mechanizing Coinductive Proofs in Liquid Haskell_**.

Code is located in `src`:
- `Stream.hs` - Stream functions.
- `StreamIndexed.hs` - Stream proofs with the indexed approach.
- `StreamConstructive.hs` - Stream proofs with the constructive approach.
- `EqLemma.hs` - Prove `eqKLemma` from `StreamConstructive.hs`.
- `List.hs` - List functions.
- `ListIndexed.hs` - List proofs with the indexed approach.
- `ListConstructive.hs` - List proofs with the constructive approach.

### Build command:
```
stack build --fast
```
The code will be compiled with `-fplugin=LiquidHaskell` which will verify our annotated code.
