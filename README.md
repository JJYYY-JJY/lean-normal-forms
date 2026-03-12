# lean-normal-forms

Executable Hermite normal form and Smith-normal-form infrastructure in Lean 4
over Euclidean domains, with certified matrix certificates and a planned bridge
to mathlib's PID results.

## Status

This repository currently contains a buildable `NormalForms` Lean library with a
completed recursive row-style Hermite layer, an executable Smith layer with
public correctness and unimodularity extraction theorems, and a minimal PID
bridge helper layer.

- Public API for `IsHermiteNormalForm`, `IsSmithNormalForm`, `HNFResult`,
  `SNFResult`, `smithInvariantFactors`, `smithColumnSpan`,
  `SNFResult.ofCertificate`, and `SNFResult.toCertificate`
- Executable recursive row-style HNF over Euclidean domains, with first-column elimination, lower-right recursion, top-row reduction, and `HNFResult.toCertificate`
- Internal HNF recursion carries explicit unimodular left certificates end-to-end, and the public theorem `hermiteNormalForm_unimodular` exposes that certificate from `hermiteNormalForm`
- HNF correctness and uniqueness are now proved, via `hermiteNormalForm_isHermite` and `isHermiteNormalForm_unique_of_left_equiv`
- `CanonicalMod` instances are available for both `Int` and `Polynomial Rat`
- `NormalForms.Matrix.Smith.Basic` now contains a real public Smith predicate,
  a public invariant-factor reader, an executable recursive Smith kernel,
  public `smithNormalForm` existence and left/right unimodularity extraction,
  and the same-size pivot-state layer (`clearFirstColumnByPivotLoop`,
  `clearFirstRowByPivotLoop`, `clearLeadByPivot`,
  `prepareLeadColumnStepData`, `prepareLeadRowStepData`,
  `prepareLeadColumn`, `prepareLeadRow`, `stabilizePivot`,
  `improvePivotStepData`, `improvePivot`, and
  `improvePivot_strict_descent`)
- `NormalForms.Matrix.Smith.Uniqueness` already proves uniqueness from equal
  invariant factors, proves preservation of the first invariant factor under
  explicit two-sided unimodular equivalence, and now contains a decomposed
  `diagPrefixProduct` / minor-divisibility skeleton for the remaining general-
  `k` public Smith uniqueness theorem
- Elementary row/column operations, mixed-log certificate helpers, and a reusable 2x2 Bezout reduction gadget
- Smoke examples over `Int` and `Q[X]`, including public HNF certificate
  checks, internal Smith diagonal-spec, invariant-factor, and same-size-step
  checks, and public `SNFResult.ofCertificate` packaging smoke, plus the local
  plan in `PLAN.md`
- GitHub Actions, citation metadata, Zenodo metadata, and an axiom-audit smoke script

The current Lean files compute recursive HNF, package explicit certificates, and
prove public HNF correctness and uniqueness. On the Smith side, the repository
has moved well beyond a pure API freeze: the public predicate and invariant-factor
reader are real, the executable recursive kernel and public
`smithNormalForm` existence/isSmith/unimodularity theorems are in place, and the
same-size lead-clearing, lead-preparation, stabilization, and single-step
nondivisible pivot-improvement layers are verified over both `Int` and `Q[X]`.
The remaining Smith work is narrower: fill the decomposed general-`k` minor
divisibility chain in `NormalForms.Matrix.Smith.Uniqueness`, lift first-
invariant-factor preservation to full invariant-factor preservation under
two-sided unimodular equivalence, then complete the public uniqueness theorem
and finally the full PID bridge.

One deliberate implementation boundary is worth calling out: the public Smith
wrappers over arbitrary `Fintype` indices are defined by reindexing through
`Fintype.equivFin`, but the library intentionally does not expose global `[simp]`
bridge lemmas that try to collapse that reindexing on concrete `Fin` matrices.
Those simplifications can trigger very expensive elaboration. As a result, the
example layer keeps concrete Smith computation and same-size step smoke on the
internal `Fin` definitions and reserves the public layer for stable packaging
and API checks.

## Build

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
lake env lean NormalForms/Matrix/Hermite/Basic.lean
lake env lean NormalForms/Matrix/Smith/Basic.lean
lake env lean NormalForms/Examples/AbelianGroups/Basic.lean
```

The committed `lake-manifest.json` pins a compatible mathlib snapshot. On a fresh machine, Lake will still need network access the first time it materializes `.lake/packages`.

## Layout

- `NormalForms/Matrix/Elementary`: row and column operation skeletons, logs, and replay semantics
- `NormalForms/Matrix/Hermite`: executable HNF predicate, internal Fin kernel, public result packaging, uniqueness, and `CanonicalMod`
- `NormalForms/Matrix/Smith`: public Smith diagonal specification,
  invariant-factor reader, certificate/result packaging API, internal recursive
  scaffolding, same-size lead-clearing, lead-preparation, stabilization, and
  pivot-improvement foundations, two-sided transform helpers, and the current
  `SNFResult` /
  `smithNormalForm` boundary
- `NormalForms/Matrix/Certificates`: reusable certificate shapes and unimodularity lemmas
- `NormalForms/Bridge/MathlibPID`: minimal unimodular/column-span bridge helpers toward mathlib's PID results, with the full invariant-factor comparison still pending
- `NormalForms/Examples/AbelianGroups`: sample matrices, executable HNF smoke
  checks, internal `Int` and `Q[X]` Smith spec/invariant-factor/same-size-step
  smoke, and public Smith certificate/result packaging smoke
- `paper/`: manuscript planning notes
- `artifact/`: artifact packaging notes

## Scope

- Executable algorithms are scoped to `EuclideanDomain`
- Exact executable canonicality statements use a lightweight `CanonicalMod` mixin to capture canonical Euclidean remainders
- PID-level statements are scoped to specifications and bridge theorems
- The initial research application is finitely generated abelian groups over `Z`

For the full roadmap, milestones, and submission strategy, see `PLAN.md`.

