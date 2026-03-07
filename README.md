# lean-normal-forms

Executable Hermite and Smith normal forms in Lean 4 over Euclidean domains, with a certified recursive HNF layer and a bridge to mathlib's PID results.

## Status

This repository currently contains a buildable `NormalForms` Lean library with a real recursive row-style Hermite layer, a frozen Smith public API scaffold, and scaffolded PID follow-through.

- Public API for `IsHermiteNormalForm`, `IsSmithNormalForm`, `HNFResult`, and `SNFResult`
- Executable recursive row-style HNF over Euclidean domains, with first-column elimination, lower-right recursion, top-row reduction, and `HNFResult.toCertificate`
- Internal HNF recursion carries explicit unimodular left certificates end-to-end, and the public theorem `hermiteNormalForm_unimodular` exposes that certificate from `hermiteNormalForm`
- HNF correctness and uniqueness are now proved, via `hermiteNormalForm_isHermite` and `isHermiteNormalForm_unique_of_left_equiv`
- Frozen SNF API scaffold in `NormalForms.Matrix.Smith.Basic`, including `SNFResult`, placeholder `IsSmithNormalForm`, and a public `smithNormalForm` entrypoint that currently returns `none`
- Elementary row/column operations, mixed-log certificate helpers, and a reusable 2x2 Bezout reduction gadget
- Smoke examples over `Int` and `Q[X]`, including public HNF certificate checks, plus the local plan in `PLAN.md`
- GitHub Actions, citation metadata, Zenodo metadata, and an axiom-audit smoke script

The current Lean files now compute recursive HNF, package left certificates, and prove public HNF correctness and uniqueness. The SNF public interface is frozen as the first public checkpoint, so the repository is ready for the arXiv preprint; the immediate next phase is executable Smith normal form plus its proofs, followed by the PID bridge.

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
- `NormalForms/Matrix/Hermite`: executable HNF predicate, internal Fin kernel, and public result packaging
- `NormalForms/Matrix/Smith`: frozen SNF predicate, result, and entrypoint scaffold
- `NormalForms/Matrix/Certificates`: reusable certificate shapes and unimodularity lemmas
- `NormalForms/Bridge/MathlibPID`: placeholder bridge theorem API toward mathlib's PID results
- `NormalForms/Examples/AbelianGroups`: sample matrices, executable HNF smoke checks, and certificate examples
- `paper/`: manuscript planning notes
- `artifact/`: artifact packaging notes

## Scope

- Executable algorithms are scoped to `EuclideanDomain`
- Exact HNF normality statements use a lightweight `CanonicalMod` mixin to capture canonical Euclidean remainders
- PID-level statements are scoped to specifications and bridge theorems
- The initial research application is finitely generated abelian groups over `Z`

For the full roadmap, milestones, and submission strategy, see `PLAN.md`.
