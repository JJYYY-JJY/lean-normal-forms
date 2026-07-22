# NormalForms public API baseline

Version: 1.2.2

`import NormalForms` exposes stable specifications, strong results,
entry points, uniqueness/invariance theorems, intrinsic Smith data,
finite-free presentations, the PID bridge, and the abelian-group application.
It does not expose recursive state, pivot helpers, operation replay, examples,
FFI/native-trust, or research backends.

The name-level compile-time baseline is `NormalForms/Tests/PublicApi.lean`.
`NormalForms/Tests/CoreFreeze.lean` pins exact constructors, entry-point
types, schema identity, indexing storage, and presentation direction. The
normative external format is
[`CERTIFICATE_SCHEMA_V1.md`](CERTIFICATE_SCHEMA_V1.md). Independent facade
harnesses must fail with exact unknown-identifier diagnostics for private
implementation symbols.

Package version 1.2.2 does not enlarge this facade. Rational canonical form
and finite-free integer homology have their own imports and compile-time
baselines, documented in
[`RATIONAL_CANONICAL_API.md`](RATIONAL_CANONICAL_API.md) and
[`HOMOLOGY_API.md`](HOMOLOGY_API.md).

## Indexing

- `FiniteIndexing` with `.fin`, `.ofEquiv`, `.ordered`, and `.arbitrary`.
- `MatrixIndexing` with matching constructors and `.reindex`.
- explicit row/column permutation matrices and their transport theorem.

No arbitrary-index normal-form predicate hides `Fintype.equivFin`.

## Constructive Euclidean operations

- `XGCDResult`;
- `ComputableEuclideanOps`;
- derived `quot`, `rem`, `isZeroB`, and `dvdB`;
- the public `Int` instance.

The coherent `Polynomial Rat` implementation is imported explicitly from
`NormalForms.Euclidean.PolynomialRat`. The top facade exposes stable
rational-polynomial matrix projections from
`NormalForms.Matrix.PolynomialRat`, while representation and recursive runtime
helpers remain private.

## Certificates

- equation only: `LeftTransformEquation`, `TwoSidedTransformEquation`;
- explicit inverse: `MatrixInverseCertificate`;
- strong transformations: `LeftCertificate`, `TwoSidedCertificate`;
- inverse composition, symmetry, reindexing, transpose, permutation
  certificates, `IsUnit`, and determinant-based `Unimodular` projections.

## External certificate checking

- schema and raw data: `schemaV1`, `CertificateMetadata`, `RawMatrix`,
  `RawHNFCertificate`, `RawSNFCertificate`, and `RawCertificate`;
- parsing: `parseCertificate` with separate `ParseError` cases;
- checking: `checkHNF` and `checkSNF`, each requiring the caller's exact
  expected matrix;
- checked data: `CheckedHNFData` and `CheckedSNFData`;
- failures: `CertError`, `MatrixField`, and `TransformMatrix`;
- soundness: `checkHNF_sound` and `checkSNF_sound`;
- strict-import support: `HNFKernelChecks`, `SNFKernelChecks`, their evidence
  structures, and the corresponding `check*_isOk_of_kernelEvidence` theorems.

`Checked*Data` has no trusted mathematical meaning by itself. Strong HNF/SNF
results arise only from successful checker equations passed to the soundness
constructors. The CLI source emitter and optional FLINT generator are not
facade imports.

## Hermite normal form

- predicates: `IsHermiteNormalFormFin`, `IsHermiteNormalFormWith`,
  `IsHermiteNormalFormOrdered`;
- strong results: `HNFResultFin`, `HNFResult`;
- entry points: `hermiteNormalFormFin`, `hermiteNormalFormWithIndexing`,
  `hermiteNormalFormWithEquiv`, `hermiteNormalFormOrdered`,
  `hermiteNormalForm`;
- derived equation, inverse certificate, normality, and certificate views;
- `HNFResult.leftEquivalentCertificate` for indexing changes;
- uniqueness only at `Fin` or a fixed explicit indexing.

## Smith normal form

- predicates: `IsSmithNormalFormFin`, `IsSmithNormalFormWith`,
  `IsSmithNormalFormOrdered`;
- strong results: `SNFResultFin`, `SNFResult`;
- entry points: `smithNormalFormFin`, `smithNormalFormWithIndexing`,
  `smithNormalFormWithEquiv`, `smithNormalFormOrdered`, `smithNormalForm`;
- `smithInvariantFactorsFin`, `smithInvariantFactorsWith`, and
  `smithColumnSpan`;
- derived equations, inverse certificates, normality, factors, and
  certificate views;
- `SNFResult.finChangeIndexingCertificate`,
  `SNFResult.finResult_S_eq`, and
  `SNFResult.invariantFactors_eq_of_indexing_change`;
- fixed-index two-sided uniqueness and invariant-factor uniqueness.

## Intrinsic Smith data

- `SmithData m n R`: exact rank, complete ordered diagonal, nonzero prefix,
  zero tail, normalization, and divisibility;
- `SmithSignature R`: dimensions, rank, all nonzero associate factors
  including units, factor cardinality, and derived kernel/cokernel ranks;
- `SNFResultFin.smithData`, `SNFResult.smithData`,
  `SNFResultFin.smithSignature`, and `SNFResult.smithSignature`;
- indexing-change and explicit two-sided-equivalence invariance theorems;
- `determinantalIdealFin` and `determinantalIdealWith`;
- zeroth, oversized, prefix-product, rank-tail, transpose, certificate, and
  indexing-change determinantal-ideal theorems;
- `smithRank_eq_of_determinantalIdeals`,
  `smithFactors_eq_of_determinantalIdeals`,
  `smithData_eq_of_determinantalIdeals`, and
  `smithSignature_eq_of_determinantalIdeals`.

## Bridge and application

- semantic PID quotient/decomposition equivalences and executable
  invariant-factor readout;
- `CanonicalPIDSmithBasis`, which adds the normalization and divisibility
  properties needed to compare a mathlib witness with canonical data;
- equality at associate-factor, normalized-factor, and sorted `Int.natAbs`
  levels;
- `Int` presentation submodule/quotient, invariant factors, free rank, and
  torsion-plus-free quotient decomposition.

## Finite-free presentations

- `FiniteFreePresentation R` with `numGenerators`, `numRelations`, and an
  `m × n` relation matrix whose columns define `R^n → R^m`;
- `relationMap`, `relationSubmodule`, and `presentedModule`;
- `smithResult`, `smithData`, `smithSignature`, `smithRank`, `invariantFactor`,
  `invariantFactors`, and `freeRank`;
- `smithDecomposition`, which retains unit factors, plus
  `displayInvariantFactors`, which removes them for display;
- `fittingIdeal` and its generator-count and oversized-minor boundary laws;
- `mathlibRelations`, `mathlibQuotientEquivPresentedModule`, and
  `mathlibPresentation`;
- `Applications.AbelianGroups.presentationOfMatrix` for the `Int`
  specialization.

## Internal-only surfaces

- `NormalForms.Matrix.Elementary`;
- reversible log implementation;
- HNF/SNF transform and recursive algorithm modules;
- Smith pivot/search/stabilization state;
- examples, native-trust, FFI, and research modules;
- strict CLI source-emission implementation and every external adapter.

The facade does expose the stable rational-polynomial matrix projection
surface; its finite-support arithmetic and recursive xgcd implementation do
not become independently reachable through `import NormalForms`.
