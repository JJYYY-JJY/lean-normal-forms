# lean-normal-forms 1.1.0

Version 1.1.0 adds certified executable rational canonical form over `Rat` as
an independent application profile. The 1.0 HNF/SNF core facade and all frozen
core interfaces remain unchanged.

## Rational canonical application

- `endomorphismPresentationMatrix A` computes `XI - A` and is proved exactly
  equal to mathlib's `Matrix.charmatrix`.
- `endomorphismSmithResult A` maps the choice-free polynomial runtime result
  to standard `Rat[X]` while retaining both transformations, chosen inverses,
  inverse identities, the equation, and Smith semantics.
- `endomorphismInvariantFactors A` retains all normalized diagonal entries,
  including units. Its length is the dimension and its product is the
  characteristic polynomial.
- `endomorphismCyclicDecomposition A` identifies `Module.AEval'` with the
  dependent product of cyclic quotient modules.
- `largestInvariantFactor? A` is `none` in dimension zero and the monic
  minimal polynomial in positive dimension.
- `companionMatrix`, `rationalCanonicalBasis`, and
  `rationalCanonicalResult` construct the exact companion-block form and a
  change matrix with an explicit two-sided inverse certificate.
- `SimilarityCertificate` proves exact invariant-factor and canonical-block
  invariance. Basis-level variants make these outputs independent of the
  chosen basis for an abstract endomorphism.

Import the application explicitly:

```lean
import NormalForms.Applications.RationalCanonical
```

The top-level `NormalForms` import does not expose it.

## Reproducibility

- The application API is frozen by
  `NormalForms/Tests/RationalCanonical/PublicApi.lean`.
- The separate axiom audit observes only `propext`, `Quot.sound`, and
  `Classical.choice`.
- A native 2-by-2 rational Jordan profile records factor degrees `[0, 2]`,
  coefficient growth from 2 to 3 bits, 0.07 s median invariant generation,
  and a 0.617 s median for 1,000 isolated companion checks on the captured
  host.
- `scripts/verify.sh rational-canonical` reproduces the code, API, axiom, and
  committed-evidence checks. Publication files remain a separate artifact.

Native benchmark success is observational evidence, not a theorem dependency.
The Lean kernel checks the Smith, cyclic-decomposition, companion,
minimal-polynomial, and similarity proofs.

## Release boundary

These files prepare local release notes, source/paper archives, Zenodo
metadata, and checksums. They do not create a GitHub release, tag, DOI,
deposition, or upstream pull request.
