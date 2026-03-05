# lean-normal-forms

Executable Hermite and Smith normal forms in Lean 4 over Euclidean domains, with a bridge to mathlib's PID results.

## Status

This repository currently contains a buildable project skeleton for the `NormalForms` Lean library.

- Public API placeholders for `IsHermiteNormalForm`, `IsSmithNormalForm`, `HNFResult`, and `SNFResult`
- Project layout for the six planned subsystems plus `paper/` and `artifact/`
- GitHub Actions, citation metadata, Zenodo metadata, and an axiom-audit smoke script
- A local canonical plan in `PLAN.md`

The current Lean files establish module boundaries and certificate shapes. They do not yet implement executable HNF or SNF algorithms.

## Build

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
```

The committed `lake-manifest.json` pins a compatible mathlib snapshot. On a fresh machine, Lake will still need network access the first time it materializes `.lake/packages`.

## Layout

- `NormalForms/Matrix/Elementary`: row and column operation skeletons, logs, and replay semantics
- `NormalForms/Matrix/Hermite`: HNF predicate and result API skeleton
- `NormalForms/Matrix/Smith`: SNF predicate and result API skeleton
- `NormalForms/Matrix/Certificates`: reusable certificate shapes and unimodularity predicate
- `NormalForms/Bridge/MathlibPID`: placeholder bridge theorem API toward mathlib's PID results
- `NormalForms/Examples/AbelianGroups`: sample matrices for the eventual abelian-group showcase
- `paper/`: manuscript planning notes
- `artifact/`: artifact packaging notes

## Scope

- Executable algorithms are scoped to `EuclideanDomain`
- PID-level statements are scoped to specifications and bridge theorems
- The initial research application is finitely generated abelian groups over `Z`

For the full roadmap, milestones, and submission strategy, see `PLAN.md`.
