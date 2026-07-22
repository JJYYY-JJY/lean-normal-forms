# Finite matrix presentation bridge

`finite-matrix-presentation.patch` is an independent upstream proposal for
mathlib. It is prepared against mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`, the revision selected by
`mathlib` v4.32.0 in this repository.

The patch adds `Mathlib.Algebra.Module.Presentation.Matrix` with:

- `Module.Relations.ofMatrix`, interpreting matrix columns as relations on
  matrix rows;
- `Module.Relations.ofMatrix_relation_apply`, fixing that orientation
  definitionally; and
- `Module.Relations.ofMatrixQuotientEquiv`, identifying the resulting mathlib
  quotient with the cokernel of `Matrix.mulVecLin`.

This is the generic seam used by
`NormalForms.FiniteFreePresentation.mathlibRelations` and
`mathlibQuotientEquivPresentedModule`. It contains no NormalForms definitions
and does not propose Smith-normal-form APIs for mathlib.

## Reproduce

From a clean checkout of
[`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4):

```sh
git checkout 81a5d257c8e410db227a6665ed08f64fea08e997
git apply --check /path/to/lean-normal-forms/patches/mathlib/finite-matrix-presentation.patch
git apply /path/to/lean-normal-forms/patches/mathlib/finite-matrix-presentation.patch
lake env lean Mathlib/Algebra/Module/Presentation/Matrix.lean
```

The exact proposed declarations were compiled with Lean 4.32.0 before the
patch was packaged. The patch is archival material only: it has not been
applied to the pinned dependency, submitted upstream, or used as a proof
dependency.
