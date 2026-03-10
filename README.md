# lean-normal-forms

Executable Hermite normal form and Smith-normal-form infrastructure in Lean 4 over Euclidean domains, with certified matrix certificates and a planned bridge to mathlib's PID results.

## Status

This repository currently contains a buildable `NormalForms` Lean library with a completed recursive row-style Hermite layer, a real Smith specification/infrastructure layer, and a placeholder PID bridge.

- Public API for `IsHermiteNormalForm`, `IsSmithNormalForm`, `HNFResult`, and `SNFResult`
- Executable recursive row-style HNF over Euclidean domains, with first-column elimination, lower-right recursion, top-row reduction, and `HNFResult.toCertificate`
- Internal HNF recursion carries explicit unimodular left certificates end-to-end, and the public theorem `hermiteNormalForm_unimodular` exposes that certificate from `hermiteNormalForm`
- HNF correctness and uniqueness are now proved, via `hermiteNormalForm_isHermite` and `isHermiteNormalForm_unique_of_left_equiv`
- `CanonicalMod` instances are available for both `Int` and `Polynomial Rat`
- `NormalForms.Matrix.Smith.Basic` now contains a real public Smith predicate, an internal recursive Smith predicate/result skeleton, two-sided transform helpers, and the public theorem `smithNormalForm_isSmith`
- The public `smithNormalForm` entrypoint still returns `none`; the executable Smith kernel, left/right unimodularity helper theorems, and Smith uniqueness proofs are still pending
- Elementary row/column operations, mixed-log certificate helpers, and a reusable 2x2 Bezout reduction gadget
- Smoke examples over `Int` and `Q[X]`, including public HNF certificate checks, `Int` Smith two-sided certificate examples, and `Q[X]` Smith diagonal-spec smoke, plus the local plan in `PLAN.md`
- GitHub Actions, citation metadata, Zenodo metadata, and an axiom-audit smoke script

The current Lean files compute recursive HNF, package explicit certificates, and prove public HNF correctness and uniqueness. On the Smith side, the repository has moved beyond a pure API freeze: the public predicate is now a real diagonal specification, the internal recursive predicate and transform shells are in place, and the example layer exercises both `Int` and `Q[X]`. The immediate next phase is still the executable Smith kernel plus its correctness, unimodularity, and uniqueness proofs, followed by the PID bridge.

## Build

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
lake env lean NormalForms/Examples/AbelianGroups/Basic.lean
```

The committed `lake-manifest.json` pins a compatible mathlib snapshot. On a fresh machine, Lake will still need network access the first time it materializes `.lake/packages`.

## Layout

- `NormalForms/Matrix/Elementary`: row and column operation skeletons, logs, and replay semantics
- `NormalForms/Matrix/Hermite`: executable HNF predicate, internal Fin kernel, public result packaging, uniqueness, and `CanonicalMod`
- `NormalForms/Matrix/Smith`: public Smith diagonal specification, internal recursive scaffolding, two-sided transform helpers, and the current `SNFResult` / `smithNormalForm` boundary
- `NormalForms/Matrix/Certificates`: reusable certificate shapes and unimodularity lemmas
- `NormalForms/Bridge/MathlibPID`: placeholder bridge theorem API toward mathlib's PID results
- `NormalForms/Examples/AbelianGroups`: sample matrices, executable HNF smoke checks, `Int` Smith certificate examples, and `Q[X]` Smith spec smoke
- `paper/`: manuscript planning notes
- `artifact/`: artifact packaging notes

## Scope

- Executable algorithms are scoped to `EuclideanDomain`
- Exact executable canonicality statements use a lightweight `CanonicalMod` mixin to capture canonical Euclidean remainders
- PID-level statements are scoped to specifications and bridge theorems
- The initial research application is finitely generated abelian groups over `Z`

For the full roadmap, milestones, and submission strategy, see `PLAN.md`.
