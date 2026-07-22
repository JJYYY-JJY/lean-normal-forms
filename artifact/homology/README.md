# Finite-free integer homology artifact profile

This profile reproduces the independent v1.2.2 homology application on top
of the frozen v1.0 HNF/SNF and presentation core. It does not change or
re-export the core `NormalForms` facade.

The profile checks:

- the fixed convention `boundary n = d_(n+1)`;
- strong Smith certificates for outgoing differentials;
- the explicit kernel basis formed by tail columns of `V`;
- the proved zero prefix of `V⁻¹ d_(n+1)`;
- the restricted kernel-coordinate boundary matrix;
- the second strong Smith result;
- the quotient equivalence and complete torsion-plus-free decomposition;
- the theorem/runtime reindex bridge;
- circle, torus, real projective plane, and finite cellular examples;
- the independent API freeze and axiom audit;
- normalized boundaries derived from finite nondegenerate-simplex face data;
- alternating signs, repeated-face cancellation, and explicit `none`
  degeneracy elimination;
- exact simplicial circle, collapsed-boundary sphere, and filled-triangle
  fixtures;
- realization as a mathlib `ChainComplex (ModuleCat Int) Nat`;
- the degree-zero short-complex comparison and categorical homology
  equivalence;
- a certified simplicial realization witness with exact nondegenerate-face,
  degenerate-face, basis, and differential compatibility;
- chain isomorphisms with mathlib's nondegenerate normalized chains and
  normalized Moore complex;
- transported certified decompositions of both mathlib homology objects;
- a native 20-case executable smoke target.

## Host reproduction

From the repository root:

```sh
scripts/verify.sh homology
```

The verifier writes the native run and axiom report under
`build/verify/homology`.

## Pinned container

Build and run the code, tests, audit, and native smoke:

```sh
docker build \
  --file artifact/homology/Dockerfile \
  --tag lean-normal-forms-homology:1.2.2 \
  .

docker run --rm lean-normal-forms-homology:1.2.2
```

The image pins the same Debian base, Lean archive hash, and Lake manifest as
the core artifact. It contains no FLINT dependency: this profile uses the
internal certified integer Smith kernel.

## Evidence and trust boundary

The native report records each complete runtime summary and observational
wall time. Absolute wall time is not a portable pass/fail condition.
Correctness comes from the kernel-checked strong Smith, kernel-basis,
coordinate-restriction, quotient, and decomposition theorems. The semantic
application layer admits `Classical.choice` in addition to `propext` and
`Quot.sound`; compiler/native trust and project-defined axioms remain
forbidden.

This v1.2.2 profile accepts explicit finite free boundary matrices and finite
normalized nondegenerate-simplex tables. It compares the former directly with
mathlib categorical homology. Comparison of a face table with normalized
Moore chains additionally requires a checked `NormalizedMooreComparison`
witness; the artifact does not silently assume missing simplicial identities
or degeneracy maps.
