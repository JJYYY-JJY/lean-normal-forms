# Changelog

## Unreleased

### Added

- A sign-normalized, per-level coefficient-reduced extended-gcd reference
  implementation with a linear Euclidean-iteration theorem and a closed
  polynomial bit-operation bound.
- A Kannan--Bachem principal HNF cost layer that aligns every arithmetic event
  with its primitive row step, charges exact reference XGCD/division work and
  bounded scalar row arithmetic, and proves a closed bit-operation bound for
  `PrincipalReady` square inputs.
- Deterministic certified row preparation for every nonsingular square input,
  including a constructive inverse permutation matrix, a strong HNF result on
  the original input, and a prepared-kernel bound in the original input width.
- A cached division-free Bird recurrence over materialized vectors, an exact
  schoolbook sign-magnitude arithmetic cost, closed intermediate coefficient
  bounds, a closed determinant-evaluation cost expression, and a generic
  bordered-minor proof that the cached and charged values equal `Matrix.det`.
- A charged first-nonzero minor scan used directly by `Principal.prepare`, its
  recursive aggregate bound, and a closed preparation-plus-kernel HNF
  bit-operation theorem for every nonsingular square input.
- A total faithful Kannan--Bachem SNF semantic path for nonsingular square
  integer matrices. It alternates one-column LHNF and transposed principal HNF,
  clears divisible pivot columns with an explicitly invertible shear,
  implements Step-7 witness injection, and recurses only after a proved strict
  decrease of the pivot absolute value. The outer recursion returns the
  existing strong `SNFResultFin` with both explicit inverse certificates and
  is proved equal to the canonical core result. The fuelled entry remains a
  bounded diagnostic and never falls back to the generic Smith kernel.
- A binary-size pass bound and exact five-class SNF operation counter. The
  counter follows every stabilization and lower-right recursion, preserves a
  common determinant-width budget, and has a closed polynomial bound in the
  original dimension and coefficient width.
- A bounded-XGCD one-column SNF reducer with exact trace length and closed
  bounds for arithmetic operands, transformed matrices, multiplier prefixes,
  and inverse prefixes. The bounds compose through stabilization and the
  lower-right recursion into a single profile for `S`, `U`, `U⁻¹`, `V`, and
  `V⁻¹`.
- An end-to-end SNF bit-operation model that follows every actual
  stabilization branch and lower-right recursive call. It charges bounded
  XGCD, division, row and column arithmetic, prepared HNF, and all four dense
  products in each strong-certificate composition. The dense product is a
  costed sign-magnitude reference whose value is proved equal entrywise to
  `Matrix.mul`; the total bound depends only on the original matrix dimension
  and coefficient width.
- An independent `research/kannan-bachem` 0.1.0 release profile with a native
  three-case executable, four-stage one-warmup/seven-measurement JSON/CSV
  benchmark, 572-name API freeze, 263-root axiom audit, pinned container,
  manuscript, archival metadata, and one-command release gate.
- A total determinant-modulus modular-HNF value kernel with distinct typed
  modulus contracts, exact six-class telemetry, and an augmented-row-lattice
  invariant proving every legal full-column candidate equal to the canonical
  core HNF.
- A strong `modularHNFFullRank` entry returning the existing `HNFResultFin`,
  plus a checked fraction-free rank profile and complete finite integer search
  extending the modular result to rectangular, rank-deficient, rank-zero, and
  empty matrices.
- Closed modular-HNF scalar-operation and intermediate/final coefficient
  bounds, an exact costed mirror of Lean's standard integer XGCD path, and a
  composed schoolbook bit-operation bound for the value kernel.
- An independent `research/modular-hnf` 0.1.0 release profile with a
  three-case native executable, four-stage one-warmup/seven-measurement
  JSON/CSV benchmark, 157-name API freeze, 43-root axiom audit, pinned
  container, manuscript, archival metadata, and one-command release gate.
- Exact integer row-basis LLL at `delta = 3/4` and `eta = 1/2`, backed by the
  source-pinned terminating dense reducer and a synchronized trace of every
  size reduction and adjacent swap.
- Strong full-rank LLL results carrying `U`, a chosen inverse, both inverse
  identities, `U * B = B'`, and exact reducedness, without recovering the
  inverse from a determinant or choice.
- An HNF-based total `integerLLL` wrapper for empty, zero, rectangular, and
  rank-deficient inputs, plus a transpose-only `integerColumnLLL` adapter.
- A profiled full-rank entry with exact event telemetry, a verified fuel-based
  event bound, intermediate basis-and-multiplier height evidence, and a
  composed sign-magnitude reference cost bound.
- An independent `research/lll` 0.1.0 release profile with four native cases,
  five one-warmup/seven-measurement stages, a 114-name API freeze, 20-root
  axiom audit, pinned container, manuscript, archival metadata, and
  one-command release gate.

### Changed

- The principal HNF kernel now executes the same bounded XGCD value projected
  from the costed sign-magnitude reference implementation.
- Consolidated expensive principal execution guards around one shared run,
  reducing the measured target rebuild from 262 seconds to 89 seconds after
  the costed-XGCD integration.
- Refreshed four exact SNF operation-count guards after the bounded-XGCD Step
  4 path changed; the research gate now directly re-elaborates the execution
  file so Lake cache reuse cannot conceal stale `#guard` values.
- Made the constructive source audit's trust boundary explicit: it scans all
  library modules while excluding benchmark and test harnesses, whose native
  fixtures remain observational and whose public theorem roots are audited
  separately.
- Separated the historical bit-cost 0.1.0 API/audit snapshot from the current
  bounded-XGCD surface; its release gate now verifies both 49/21 and 87/34
  without rewriting the archived profile.

### Scope

- This completes the semantic preliminary permutation/general wrapper and all
  four complexity tiers for the full nonsingular square HNF path, including
  the determinant scans in preparation. The cached Bird program and its
  charged integer implementation are proved equal to `Matrix.det`. The
  nonsingular square SNF semantic, ring-operation, coefficient-growth, and
  bit-complexity tiers are complete, with a linear pass bound and explicit
  aggregate operation, certificate-width, and schoolbook bit-operation
  bounds. The standalone paper, benchmark, artifact, and local release
  materials are complete at research version 0.1.0. Rectangular and
  rank-deficient extension work remains outside this profile.
- This completes the modular-HNF 0.1.0 value-kernel profile: semantic
  correctness, canonical equality, total general-rank coverage, scalar
  operations, coefficient growth, and schoolbook bit cost are all
  kernel-checked. The strong transform is transported from the stable core
  after candidate equality, so primitive modular transform construction and
  its bit cost remain explicitly outside this profile.
- The frozen core and the archived `research/bit-cost` 0.1.0 artifact are not
  rewritten by this unreleased research development.
- This completes the LLL 0.1.0 semantic and reproducibility profile. Its
  modeled cost is deliberately a-posteriori and profile-dependent; it does
  not claim an input-only polynomial LLL bit-complexity theorem and excludes
  HNF rank decomposition and accumulated transform-product costs.

## research/bit-cost 0.1.0 - 2026-07-21

### Added

- An independently imported binary integer reference model based on
  mathlib's canonical inductive `ZNum` sign-magnitude representation.
- A four-tier acceptance vocabulary separating semantic correctness,
  ring-operation counts, coefficient bit lengths, and bit complexity.
- `addWithCost`, with explicit carry/borrow accounting, standard-`Int`
  semantics, output-width control, and a proved quadratic budget.
- `mulWithCost`, with schoolbook shift-and-add accounting, exact integer
  semantics, product-width control, and a proved input-width budget.
- `divModWithCost`, computing Euclidean quotient and remainder through one
  shared binary long-division pass, including signed and zero-divisor cases.
- `xgcdWithCost`, a well-founded Euclidean loop with normalized gcd, Bézout
  correctness, path-sensitive coefficient-width bounds, and a composed
  primitive bit-operation budget.
- A 49-declaration API freeze, exact core-facade isolation test, 21-root axiom
  audit, deterministic 13-case native executable, and one-warmup/seven-run
  raw benchmark with source, binary, and hardware fingerprints.
- An independent API document, paper, pinned container artifact, release
  gate, release notes, and archival metadata.

### Trust and compatibility

- The main package remains version 1.2.2 and the frozen `NormalForms` facade
  is unchanged; clients opt in with `NormalForms.Research.BitCost`.
- Executable definitions contain no noncomputable branch. The proof audit
  admits `propext`, `Quot.sound`, and `Classical.choice` through mathlib's
  `ZNum`/`Nat.size` semantic bridge and rejects project axioms, `sorryAx`, and
  native/compiler trust.
- Modeled costs and kernel-checked bounds are formal results. Native wall time
  and RSS are observational data only.
- The profile proves primitive arithmetic costs, not HNF/SNF operation
  counts, coefficient growth, or bit complexity.
- No GitHub release, tag, deposit, DOI, or upstream pull request is created by
  these materials.

## 1.2.2 - 2026-07-22

### Added

- `IntChainComplex.toMathlibChainComplex`, realizing every explicit integer
  matrix complex as `ChainComplex (ModuleCat Int) Nat` with the proved
  differential.
- An exact short-complex comparison that handles the degree-zero distinction
  between the project's map `C₀ → 0` and mathlib's canonical zero
  endomorphism of `C₀`.
- `mathlibHomologyEquiv` and `mathlibHomologyDecomposition`, identifying the
  intrinsic quotient with categorical homology and transporting its complete
  certified decomposition.
- `NormalizedMooreComparison`, a checked realization of finite normalized
  face data by a genuine mathlib simplicial set, including nondegenerate
  enumeration, face and degeneracy semantics, basis generators, and
  differential compatibility.
- Chain isomorphisms with mathlib's nondegenerate normalized chains and
  normalized Moore complex, together with transported homology
  decompositions.
- Dedicated categorical regressions for degree zero, chain isomorphisms, and
  decomposition bijectivity.

### Changed

- Advanced the package and command-line version to 1.2.2.
- Expanded the independent homology API freeze from 38 to 53 declarations
  and its axiom audit from 22 to 37 roots.
- Completed the planned v1.2 application line without changing the frozen
  v1.0 core facade or the independent v1.1 rational-canonical facade.

### Trust and compatibility

- The normalized Moore result requires a `NormalizedMooreComparison`
  realization witness. The weaker v1.2.1 face table and `d² = 0` proof are
  not treated as a complete simplicial set.
- All 37 audited homology roots observe only `propext`, `Quot.sound`, and
  `Classical.choice`; no project axiom, `sorryAx`, or compiler/native trust is
  admitted.
- No GitHub release, tag, deposit, DOI, or upstream pull request is created by
  these materials.

## 1.2.1 - 2026-07-20

### Added

- `FiniteNormalizedSimplicialData`, with explicit finite enumerations of
  nondegenerate simplices and normalized face tables.
- `simplicialFaceSign`, `normalizedFaceTerm`, and
  `normalizedBoundaryMatrix`, deriving integer boundary entries from
  alternating face sums.
- Explicit `none` semantics for degenerate faces, plus theorems for
  degeneracy elimination and nondegenerate signed contributions.
- A proof field validating `d² = 0` for the derived matrices, preventing face
  data and boundary data from drifting.
- `ofDimensionTwo` and a definitionally rank- and boundary-preserving
  conversion to `IntChainComplex`.
- Exact normalized models of the minimal simplicial circle,
  `Δ² / ∂Δ²`, and the filled triangle, with sign, face, matrix,
  chain-equation, and homology regressions.
- Eight additional native homology summaries, bringing the deterministic
  application run to 20 cases.

### Changed

- Advanced the package and command-line version to 1.2.1.
- Extended the independent homology facade, API freeze, paper, artifact,
  release gate, and axiom audit without changing the v1.0 core facade.
- Expanded the homology audit from 16 to 22 declarations while retaining the
  same exact allowlist.

### Trust and compatibility

- The face table is executable data; its boundary matrix is derived rather
  than trusted as a duplicate input.
- Small concrete face tables and chain equations are closed by kernel
  reduction. Native homology success remains observational evidence.
- The mathlib `HomologicalComplex` and normalized Moore comparison remains
  scoped to v1.2.2.
- No GitHub release, tag, deposit, DOI, or upstream pull request is created by
  these materials.

## 1.2.0 - 2026-07-20

### Added

- An independently imported finite-free integer homology application with
  the fixed convention `boundary n = d_(n+1) : C_(n+1) → C_n`.
- Intrinsic cycle, boundary, and ordinary homology quotient definitions for
  bounded finite free integer chain complexes.
- A first strong Smith calculation whose certified right-transform tail gives
  an explicit integral basis of `ker d_n`.
- A proof that the leading coordinates of `V⁻¹ * d_(n+1)` vanish, plus the
  exact restricted kernel-coordinate presentation.
- A second strong Smith calculation and an explicit additive equivalence from
  ordinary homology to complete cyclic and free summands.
- Complete invariant-factor readers, filtered torsion factors, and Betti
  numbers, with unit factors retained in theorem-facing data.
- A theorem-connected executable projection and native regressions for the
  circle, torus, real projective plane, and a finite cellular example with
  `H₁ ≅ ℤ × ℤ/6`.
- A separate API freeze, exact negative core-import test, 16-declaration axiom
  audit, paper, pinned container profile, release gate, release notes, and
  Zenodo metadata.

### Changed

- Advanced the package and command-line version to 1.2.0.
- Kept the v1.0 `NormalForms` facade and all frozen core interfaces unchanged.
- Kept rational canonical form at its independent v1.1 facade and made
  homology opt-in through `NormalForms.Applications.Homology`.

### Trust and compatibility

- The homology audit admits `propext`, `Quot.sound`, and
  `Classical.choice`; it rejects project axioms, `sorryAx`, and
  native/compiler trust.
- Native homology success is observational evidence. Kernel-checked strong
  Smith, kernel-basis, coordinate, quotient, and decomposition theorems carry
  the mathematical claim.
- The finite-simplex frontend and mathlib homology comparison remain scoped to
  v1.2.1 and v1.2.2; v1.2.0 does not claim them.
- No GitHub release, tag, deposit, DOI, or upstream pull request is created by
  these materials.

## 1.1.0 - 2026-07-20

### Added

- An independently imported rational-canonical application for square
  matrices over `Rat`.
- Executable `XI - A`, an exact `Matrix.charmatrix` bridge, and a mapped
  strong polynomial Smith result with explicit inverse certificates.
- Complete normalized invariant factors, their characteristic-polynomial
  product, and a `Module.AEval'` cyclic decomposition retaining unit factors.
- Executable companion matrices, the exact sum-of-degrees indexing, and an
  explicit rational canonical basis and two-sided change-of-basis
  certificate.
- `RationalCanonicalResult`, with the equation
  `P⁻¹ * A * P = rationalCanonicalBlockMatrix A`.
- Exact identification of the final positive-dimensional factor with the
  monic minimal polynomial.
- Explicit similarity certificates, exact factor/block invariance, and
  basis-independent endomorphism APIs.
- Scalar, diagonal, Jordan, coordinate-swap, inverse-identity, and
  zero-dimensional regressions plus an independent compile-time API freeze.
- A native Rat benchmark recording degrees, rational coefficient growth,
  companion verification cost, wall time, RSS, and complete source/hardware
  fingerprints in raw JSON/CSV.
- A separate axiom audit, paper, pinned container artifact, release gate,
  release notes, and Zenodo metadata for the application.

### Changed

- Advanced the package and command-line version to 1.1.0.
- Kept the v1.0 `NormalForms` facade, certificate schema, result structures,
  indexing semantics, and presentation direction unchanged.
- Made rational canonical form opt-in through
  `NormalForms.Applications.RationalCanonical`.

### Trust and compatibility

- The application audit admits `propext`, `Quot.sound`, and
  `Classical.choice`; it rejects project axioms, `sorryAx`, and
  native/compiler trust.
- Native benchmark success is observational evidence, never a theorem
  dependency.
- No GitHub release, tag, deposit, DOI, or upstream pull request is created by
  these materials.

## 1.0.0 - 2026-07-20

### Added

- Exact compile-time freezes for the public facade, certificate constructors,
  indexing storage, strong result dependencies, and presentation direction.
- A strict executable-core axiom audit covering the integer and
  rational-polynomial HNF/SNF roots.
- Constructive finite matrix lemmas and rational algebra that keep executable
  proof payloads free of `Classical.choice`.
- Synchronized release-metadata validation and a complete host release gate.
- A pinned core container profile plus deterministic source/paper/metadata,
  optional FLINT source-correspondence, build-information, and SHA256 archive
  generation.
- Local release notes and Zenodo metadata under `release/v1.0.0`.

### Changed

- Advanced the package and command-line version to 1.0.0.
- Froze `normalforms.cert/v1`, the four indexing layers, explicit-inverse
  result structures, and columns-as-relations presentation semantics.
- Reimplemented the rational-polynomial execution layer over an explicit
  runtime polynomial type while preserving its stable matrix projections and
  deterministic certificate results.
- Closed the core manuscript's implementation, benchmark, trust-boundary, and
  reproducibility status; post-1.0 applications remain separate.

### Trust and compatibility

- The strict executable and strict certificate tiers admit only `propext` and
  `Quot.sound`; they reject `Classical.choice`, project axioms, `sorryAx`, and
  native/compiler trust.
- FLINT remains an optional untrusted Linux x86_64 glibc generator. Neither
  the core facade nor pure checker links it.
- No compatibility wrappers were added for pre-1.0 weak certificates or
  hidden-index predicates.

## 0.4.0 - 2026-07-19

### Added

- `SmithData`, which records the exact rank and complete normalized Smith
  diagonal, including unit entries and the zero tail.
- `SmithSignature`, which records intrinsic associate factors and derives
  left-kernel, right-kernel, and cokernel free ranks.
- Determinantal ideals for every minor size, with proofs for `I₀ = ⊤`,
  prefix-product generators through the Smith rank, vanishing beyond the
  rank, and invariance under certified transforms and reindexing.
- Recovery theorems showing that equal determinantal ideals determine the
  Smith rank and nonzero associate-factor multiset across rectangular shapes.
- `CanonicalPIDSmithBasis` and associates, normalized-factor, and sorted
  `Int.natAbs` comparison theorems for mathlib Smith witnesses.
- Column-oriented `FiniteFreePresentation`, its relation map, cokernel,
  invariant-factor readers, Smith decomposition, and Fitting ideals.
- A bridge from finite relation matrices to mathlib `Module.Relations`,
  quotient equivalence, and `Module.Presentation`.
- Presentation regressions for zero, rectangular, rank-deficient, full-rank,
  unit-factor, minor-boundary, and matrix-direction cases.
- An independent mathlib patch for the generic matrix-to-relations and
  cokernel bridge, prepared against the pinned mathlib revision.

### Changed

- Advanced the package and command-line version to 0.4.0.
- Refactored the integer abelian-group application through
  `presentationOfMatrix` while preserving the existing arbitrary finite-index
  wrapper signatures.
- Extended the public facade and declaration baseline with intrinsic Smith,
  determinantal, PID signature, and finite-free presentation APIs.
- Kept unit invariant factors in theorem-facing decompositions and filtered
  them only in the display reader.

## 0.3.1 - 2026-07-19

### Added

- A separately linked Lean FFI adapter that invokes the exact C computation
  and decimal-protocol implementation used by the process worker, returning
  raw data rather than proofs.
- FFI HNF/SNF entry points that reconstruct `normalforms.cert/v1` and pass
  results through the existing pure checker.
- Fixed-seed internal/FFI and CLI/FFI differential regressions over dense,
  sparse, rectangular, tall, wide, and rank-deficient matrices. They compare
  normalized invariant factors only and reject malformed or mutated data.
- A native benchmark executable and reproducible certificate-path harness
  separating internal Lean, FLINT CLI, FLINT FFI, strict kernel, native
  checker, and end-to-end generation/import costs.
- Raw one-warmup/seven-measurement JSON and CSV data with median/IQR, wall
  time, RSS, integer bit length, certificate size, ratios, source revision,
  and hardware fingerprint.
- Exact facade-isolation and dynamic-link tests proving the optional FFI does
  not enter the portable core or pure checker.

### Changed

- Advanced the package and command-line version to 0.3.1.
- Extended the optional scheduled FLINT job to build and exercise the FFI
  profile; default core CI remains FLINT-free.
- Made unavailable operation, pivot, and gcd telemetry explicit as null in
  benchmark data instead of reporting estimates as measurements.

## 0.3.0 - 2026-07-19

### Added

- The strict `normalforms.cert/v1` JSON parser with canonical decimal integers,
  inert provenance metadata, and separate parse/schema failures.
- Pure HNF/SNF certificate checkers requiring a caller-supplied expected matrix,
  typed checked data, precise validation errors, and soundness constructors for
  the existing strong explicit-inverse results.
- Chunkable kernel-check records and evidence theorems for separately reduced
  strict obligations.
- `normalforms-check emit-lean`, which binds raw certificate literals to a
  named caller matrix, closes obligations with `decide_cbv`, and concludes only
  through checker soundness.
- Deterministic certificate error corpus, strict generated-module compilation,
  and a dedicated axiom audit excluding `Classical.choice` and native/compiler
  trust.
- An optional Linux x86_64 glibc FLINT 3.6.0 CLI generator with pinned GMP
  6.3.0 and MPFR 4.2.2 sources, exact hashes, pinned container digests, dynamic
  linking, and source/license/relink materials.
- End-to-end FLINT tests covering nontrivial, rank-deficient, zero-row, and
  zero-column matrices plus malformed protocol input and tampered inverses.

### Changed

- Advanced the package and command-line version to 0.3.0.
- Kept the FLINT generator, worker protocol, container, and scheduled adapter
  job outside the portable core library and default test dependency graph.

## 0.2.2 - 2026-07-19

### Changed

- Routed every executable HNF/SNF zero, divisibility, quotient, normalization,
  and Bézout branch through `ComputableEuclideanOps`.
- Replaced SNF's factorization-cardinality termination measure with the
  current pivot measure and three dedicated strict-descent theorems.
- Reworked the 2x2 Bézout primitive and its explicit inverse to consume the
  constructive xgcd result rather than generic gcd coefficient data.
- Propagated the executable Euclidean assumption through the PID bridge and
  current abelian-group examples.

### Added

- `XGCDResult`, `ComputableEuclideanOps`, and derived executable
  `quot`/`rem`/`isZeroB`/`dvdB` operations with semantic laws.
- A constructive `Int` instance using `natAbs` as its measure.
- A coherent `Polynomial Rat` runtime with direct finite-support arithmetic,
  long division, monic normalization, direct extended-Euclidean recursion, and
  proofs connecting every operation to mathlib semantics.
- Stable rational-polynomial HNF/SNF matrix projections and certificate
  checks.
- Deterministic edge-case guards, exact-output `#eval` harnesses, and the
  `normalforms-polynomial-smoke` native executable.
- `scripts/ExecutionAudit.sh`, run by CI, to enforce the constructive source
  boundary and execute all F2 baselines.

## 0.2.1 - 2026-07-19

### Changed

- Replaced optional HNF/SNF wrappers with direct-return `Fin`,
  explicit-indexing, caller-equivalence, ordered, and arbitrary-index entry
  points.
- Replaced hidden arbitrary-`Fintype` normal-form predicates with explicit
  `*Fin`, `*With`, and `*Ordered` semantics.
- Renamed equation-only certificates to `LeftTransformEquation` and
  `TwoSidedTransformEquation`.
- Made `HNFResultFin` and `SNFResultFin` carry explicit inverse certificates;
  arbitrary-index results now store only their indexing and strong `Fin`
  result, with original-index data derived.
- Migrated the PID bridge and examples to direct strong results.

### Added

- `MatrixInverseCertificate` with chosen inverse and both inverse identities.
- Strong `LeftCertificate` and `TwoSidedCertificate` structures.
- Constructive inverse composition, reindexing, transpose, permutation,
  elementary-operation, block-lift, and Bézout support.
- Internal reversible logs with four accumulators and append/replay proofs.
- `FiniteIndexing`, `MatrixIndexing`, and explicit permutation transport
  between indexings.
- HNF left-equivalence certificates across indexings.
- Proofs that canonical `Fin` SNF matrices and invariant factors are
  independent of indexing.
- Dedicated zero-dimensional and alternate-enumeration regression tests.

## 0.2.0 - 2026-07-19

### Changed

- Pinned Lean and mathlib to 4.32.0 and updated the Lake manifest.
- Migrated the project to the Lean 4.32 module system.
- Narrowed the top-level `NormalForms` facade to the stable certificate,
  HNF/SNF, PID bridge, and abelian-group application interfaces.
- Kept recursive algorithms, pivot/transform infrastructure, operation replay,
  and examples behind private imports.
- Updated proofs for Lean/mathlib 4.32 elaboration and simplifier changes
  without changing the mathematical statements.

### Added

- A machine-checked public API baseline.
- A real `lake test` driver that compiles the full example suite.
- A negative facade-import harness that accepts only the expected
  unknown-identifier diagnostic for the internal Smith kernel.
- A declaration-discovering JSON axiom audit for the public facade.
- Public API boundary documentation.
