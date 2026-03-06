# lean-normal-forms

Executable Hermite and Smith normal forms in Lean 4 over Euclidean domains, with a bridge to mathlib's PID results.

## Status

This repository currently contains a buildable `NormalForms` Lean library with an executable Hermite layer and scaffolded Smith / PID follow-through.

- Public API for `IsHermiteNormalForm`, `IsSmithNormalForm`, `HNFResult`, and `SNFResult`
- Executable row-style HNF over Euclidean domains, plus `HNFResult.toCertificate`
- Elementary row/column operations, mixed-log certificate helpers, and a reusable 2x2 Bezout reduction gadget
- Smoke examples over `Int` and `Q[X]`, plus the local plan in `PLAN.md`
- GitHub Actions, citation metadata, Zenodo metadata, and an axiom-audit smoke script

The current Lean files now compute HNF and package left certificates. Smith normal form, the PID bridge, and stronger correctness / uniqueness layers remain in progress.

## Build

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
```

The committed `lake-manifest.json` pins a compatible mathlib snapshot. On a fresh machine, Lake will still need network access the first time it materializes `.lake/packages`.

## Layout

- `NormalForms/Matrix/Elementary`: row and column operation skeletons, logs, and replay semantics
- `NormalForms/Matrix/Hermite`: executable HNF predicate, internal Fin kernel, and public result packaging
- `NormalForms/Matrix/Smith`: SNF predicate and result API scaffold
- `NormalForms/Matrix/Certificates`: reusable certificate shapes and unimodularity lemmas
- `NormalForms/Bridge/MathlibPID`: placeholder bridge theorem API toward mathlib's PID results
- `NormalForms/Examples/AbelianGroups`: sample matrices, executable HNF smoke checks, and certificate examples
- `paper/`: manuscript planning notes
- `artifact/`: artifact packaging notes

## Scope

- Executable algorithms are scoped to `EuclideanDomain`
- PID-level statements are scoped to specifications and bridge theorems
- The initial research application is finitely generated abelian groups over `Z`

For the full roadmap, milestones, and submission strategy, see `PLAN.md`.


