# Rational canonical API

Version: 1.1.0

Import the independently versioned application facade:

```lean
import NormalForms.Applications.RationalCanonical
```

The package-level `NormalForms` facade remains the frozen 1.0 HNF/SNF core and
does not re-export this application. The compile-time API baseline is
`NormalForms/Tests/RationalCanonical/PublicApi.lean`.

## Presentation and executable factors

For `A : Matrix (Fin n) (Fin n) Rat`:

```lean
endomorphismPresentationMatrix A
endomorphismSmithResult A
endomorphismInvariantFactor A i
endomorphismInvariantFactors A
largestInvariantFactor? A
```

`endomorphismPresentationMatrix A` is the executable `XI - A` matrix and is
proved equal to mathlib's `A.charmatrix`. The strong Smith result carries
mapped left and right transformations, their explicit inverses, the exact
transformation equation, and Smith-normal-form semantics.

The factor list has length `n` and retains unit factors. Its product is exactly
`A.charpoly`. `largestInvariantFactor?` returns `none` in dimension zero and
the last factor otherwise.

The implementation runs the choice-free rational-polynomial Smith kernel and
then maps its data to standard `Rat[X]`. Runtime bridge declarations are
available from the same facade for clients that need to relate the executable
polynomial representation to mathlib polynomials.

## Cyclic module decomposition

```lean
EndomorphismModule A
endomorphismCyclicDecomposition A
endomorphismDisplayInvariantFactors A
```

`EndomorphismModule A` is `Module.AEval'` for the endomorphism represented by
`A`. The decomposition is a `Rat[X]`-linear equivalence with the dependent
product of `Rat[X] / (dᵢ)`. The theorem-facing product retains unit factors and
their zero quotient modules. The display reader alone filters units.

## Companion blocks and explicit similarity

```lean
companionMatrix p
rationalCanonicalBasis A
rationalCanonicalChange A
rationalCanonicalChangeInverse A
rationalCanonicalChangeCertificate A
rationalCanonicalBlockMatrix A
rationalCanonicalResult A
```

`companionMatrix p` uses the power basis `1, X, ..., X^(d-1)`: subdiagonal
entries are one and the final column contains the negated lower coefficients.
For monic `p`, its characteristic polynomial is exactly `p`.

`RationalCanonicalResult A` contains:

```lean
change
changeCertificate
equation
```

The certificate stores a chosen inverse and both inverse identities. Its
equation is

```text
changeCertificate.inverse * A * change =
  rationalCanonicalBlockMatrix A
```

The block matrix is the dependent block diagonal of the companions of every
invariant factor, reindexed by the proved sum-of-degrees equality. Unit
factors contribute zero-dimensional blocks.

## Characteristic and minimal polynomials

```lean
endomorphismInvariantFactors_product
lastInvariantFactor_eq_minpoly
largestInvariantFactor?_eq_minpoly
```

The first theorem identifies the product of all factors with the
characteristic polynomial. In positive dimension, the last factor is exactly
the monic minimal polynomial. The option-valued reader preserves the explicit
zero-dimensional `none` convention.

## Similarity and basis independence

```lean
SimilarityCertificate A B
SimilarityCertificate.refl
SimilarityCertificate.symm
SimilarityCertificate.trans
endomorphismInvariantFactors_eq_of_similarity
rationalCanonicalBlockMatrix_eq_of_similarity
basisSimilarityCertificate
endomorphismInvariantFactors_toMatrix_eq
rationalCanonicalBlockMatrix_toMatrix_eq
```

`SimilarityCertificate` records a change matrix, its explicit inverse
certificate, and the equation `P⁻¹ A P = B`. Mapping the certificate through
polynomial constants gives a two-sided equivalence between `XI - A` and
`XI - B`. Strong Smith uniqueness then yields exact equality of normalized
factors, not merely association.

The basis-level theorems state that the factor list and canonical block matrix
computed from an abstract rational endomorphism do not depend on the chosen
finite basis.

## Trust and execution

Application theorems are checked by Lean's kernel. The semantic quotient and
basis layer may use `Classical.choice`; the v1.1 audit permits only
`propext`, `Quot.sound`, and `Classical.choice`. It rejects project axioms,
`sorryAx`, and native/compiler trust.

The native benchmark is an observational regression:

```sh
lake build normalforms-rational-canonical-benchmark
.lake/build/bin/normalforms-rational-canonical-benchmark invariants
.lake/build/bin/normalforms-rational-canonical-benchmark companion
.lake/build/bin/normalforms-rational-canonical-benchmark total
```

Its success is not a proof. Correctness comes from the strong Smith,
companion, similarity, and basis-independence theorems above.
