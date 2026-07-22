# lean-normal-forms 1.2.1

Version 1.2.1 adds finite normalized simplicial input to the independently
imported integer homology application. The frozen v1.0 HNF/SNF core, v1.1
rational-canonical facade, and v1.2.0 explicit-chain interface remain
compatible.

## Normalized simplicial boundaries

- `FiniteNormalizedSimplicialData` explicitly enumerates every nondegenerate
  simplex and records finite support.
- `face n i σ = some τ` names a nondegenerate face.
  `face n i σ = none` marks a degenerate face erased by normalized chains.
- `normalizedBoundaryMatrix` derives each integer entry as the alternating
  sum of all face occurrences. Repeated faces remain separate summands, so
  opposite signs cancel.
- The structure validates `d² = 0` for those derived matrices; it cannot
  contain a second, drifting boundary representation.
- `toIntChainComplex` preserves ranks and boundaries definitionally, so all
  v1.2.0 kernel-coordinate and Smith decomposition results apply directly.
- `ofDimensionTwo` provides a concise constructor for vertex, edge, and
  triangle tables.

## Executable fixtures

- A minimal simplicial circle checks repeated endpoint cancellation.
- `Δ² / ∂Δ²` checks explicit removal of three degenerate faces and computes
  degree-two homology `ℤ`.
- The filled triangle checks the exact matrices

  ```text
  d1 = [-1 -1  0]    d2 = [ 1]
       [ 1  0 -1]         [-1]
       [ 0  1  1]         [ 1]
  ```

  together with `d1 * d2 = 0` and trivial positive-degree homology.

The native profile now checks 20 complete summaries across all cellular and
simplicial examples.

## Reproducibility and trust

- The independent homology API freeze now checks 38 declarations.
- The homology audit covers 22 representative declarations and observes only
  `propext`, `Quot.sound`, and `Classical.choice`.
- Concrete face signs, face targets, degeneracy markers, matrices, and chain
  equations are checked by Lean kernel reduction.
- `scripts/verify.sh homology` reproduces the code, API, axiom, native, and
  committed-evidence checks. Publication files remain separate.

Native success is observational evidence. The derived boundary definition,
chain proof, strong Smith certificates, kernel-basis equivalence, and quotient
decomposition carry the mathematical result.

## Scope

Comparison with mathlib `HomologicalComplex` and normalized Moore complexes
remains the independently gated v1.2.2 milestone.

## Release boundary

These files prepare local release notes, source/paper archives, Zenodo
metadata, and checksums. They do not create a GitHub release, tag, DOI,
deposition, or upstream pull request.
