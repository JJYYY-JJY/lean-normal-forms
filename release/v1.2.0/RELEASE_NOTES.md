# lean-normal-forms 1.2.0

Version 1.2.0 adds certified finite-free integer homology as an independent
application profile. The frozen 1.0 HNF/SNF core facade and the separate v1.1
rational-canonical facade remain unchanged.

## Finite-free integer homology

- `IntChainComplex` represents bounded finite free integer chain complexes
  with `boundary n = d_(n+1) : C_(n+1) → C_n`.
- `cycles`, `boundaries`, and `homology` define the intrinsic quotient
  `ker d_n / im d_(n+1)`.
- `outgoingSmithResult` provides the first strong Smith certificate. The tail
  columns of its right transform form `kernelBasisEquiv`.
- `incomingSmithCoordinates_leading_zero` proves that
  `V⁻¹ * d_(n+1)` has no component before the kernel tail.
- `kernelCoordinateMatrix` presents homology in that explicit basis, and
  `homologySmithResult` performs the second strong Smith calculation.
- `homologyPresentationEquiv` identifies ordinary homology with the finite
  presentation cokernel.
- `homologyDecomposition` gives the complete cyclic-plus-free additive
  equivalence. Unit factors remain as zero cyclic summands; the torsion
  display reader filters them separately.
- Runtime readers execute the same matrix path and are connected to the
  theorem-facing rank and restricted matrix by equality and reindexing
  theorems.

Import the application explicitly:

```lean
import NormalForms.Applications.Homology
```

The top-level `NormalForms` import does not expose it.

## Reproducibility

- The public surface is frozen by
  `NormalForms/Tests/Homology/PublicApi.lean`.
- An exact negative harness proves that the v1.2 application is not visible
  from the core facade.
- The native executable checks 12 complete summaries for the circle, torus,
  real projective plane, and a finite cellular example with
  `H₁ ≅ ℤ × ℤ/6`.
- The 16-declaration audit observes only `propext`, `Quot.sound`, and
  `Classical.choice`.
- `scripts/verify.sh homology` reproduces the code, API, axiom, native, and
  committed-evidence checks. Publication files remain separate.

Native success is observational evidence, not a theorem dependency. Lean's
kernel checks the strong Smith, kernel-basis, zero-coordinate, quotient, and
decomposition results.

## Scope

Version 1.2.0 starts from explicit integer boundary matrices. Finite
nondegenerate simplex data and normalized boundary generation are reserved
for v1.2.1. Comparison with mathlib `HomologicalComplex` and normalized Moore
complexes is reserved for v1.2.2.

## Release boundary

These files prepare local release notes, source/paper archives, Zenodo
metadata, and checksums. They do not create a GitHub release, tag, DOI,
deposition, or upstream pull request.
