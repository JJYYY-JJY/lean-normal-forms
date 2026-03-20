# lean-normal-forms

Executable Hermite normal form and Smith-normal-form infrastructure in Lean 4
over Euclidean domains, with certified matrix certificates and a semantic PID
bridge to mathlib's quotient/decomposition results.

## Status

**🌟 Zero Warnings Milestone:** The entire codebase currently builds with **zero warnings and zero errors** (`lake build`), signifying complete logical verification of the implemented layers and strong proof stability.

This repository currently contains a buildable `NormalForms` Lean library with a
completed recursive row-style Hermite layer, a completed executable Smith layer
with public correctness, uniqueness, and unimodularity extraction theorems, a
semantic PID quotient bridge layer, and an initial full-rank `Int`
witness-list comparison layer.

- Public API for `IsHermiteNormalForm`, `IsSmithNormalForm`, `HNFResult`,
  `SNFResult`, `smithInvariantFactors`, `smithColumnSpan`,
  `SNFResult.ofCertificate`, and `SNFResult.toCertificate`
- Executable recursive row-style HNF over Euclidean domains, with first-column elimination, lower-right recursion, top-row reduction, and `HNFResult.toCertificate`
- Internal HNF recursion carries explicit unimodular left certificates end-to-end, and the public theorem `hermiteNormalForm_unimodular` exposes that certificate from `hermiteNormalForm`
- HNF correctness and uniqueness are now proved, via `hermiteNormalForm_isHermite` and `isHermiteNormalForm_unique_of_left_equiv`
- `CanonicalMod` instances are available for both `Int` and `Polynomial Rat`
- `NormalForms.Matrix.Hermite` is now split across `Defs`, `Transform`,
  `Bezout`, `Algorithm`, and `Basic`, separating predicates, transform
  certificates, Bezout gadgets, the recursive Fin kernel, and the public
  wrapper layer
- `NormalForms.Matrix.Smith` is now split across `Defs`, `Transform`,
  `Algorithm`, and `Basic`, so the public Smith specification, two-sided
  transport layer, recursive executable kernel, and result-packaging API no
  longer live in one monolithic file
- `NormalForms.Matrix.Smith.Uniqueness` now proves uniqueness from equal
  invariant factors, preservation of the first invariant factor under explicit
  two-sided unimodular equivalence, the completed decomposed
  `diagPrefixProduct` / minor-divisibility chain, the internal theorem
  `isSmithNormalFormFin_unique_of_two_sided_equiv`, and the public theorem
  `isSmithNormalForm_unique_of_two_sided_equiv`
- `NormalForms.Bridge.MathlibPID.Basic` now exposes raw bridge helpers together
  with executable-side and mathlib-side normalized `Int` coefficient-list
  readouts, including `pidExecutableSmithCoeffNatAbsList` and
  `pidFullRankMathlibSmithCoeffNatAbsList`
- `NormalForms.Bridge.MathlibPID.Quotient` now proves the semantic PID bridge:
  executable invariant-factor readout, quotient transport through the chosen
  executable `SNFResult`, quotient decomposition into torsion-plus-free parts,
  `ℤ`-specific `ZMod` specialization, the full-rank count theorem
  `pidExecutableInvariantFactorCount_eq_card_rows_of_finrank_eq_card`, and
  full-rank compatibility equivalences with mathlib's `quotientEquivPiSpan` /
  `quotientEquivDirectSum` / `quotientEquivPiZMod`
- Elementary row/column operations, mixed-log certificate helpers, and a reusable 2x2 Bezout reduction gadget
- Smoke examples over `Int` and `Q[X]`, including public HNF certificate
  checks, internal Smith diagonal-spec, invariant-factor, and same-size-step
  checks, public `SNFResult.ofCertificate` packaging smoke, semantic
  quotient/direct-sum/`PiZMod` bridge instantiations, and normalized
  executable-vs-mathlib coefficient-list length comparisons, plus the local
  plan in `PLAN.md`
- GitHub Actions, citation metadata, Zenodo metadata, and an axiom-audit smoke script

The current Lean files compute recursive HNF, package explicit certificates, and
prove public HNF correctness and uniqueness. The former monolithic Hermite and
Smith implementation files are now physically split by concern, so the public
facades sit on top of dedicated definition, transform, Bezout, and algorithm
submodules. On the Smith side, the public predicate and invariant-factor reader
are real, the executable recursive kernel and public
`smithNormalForm` existence/isSmith/unimodularity/uniqueness theorems are in
place, and the same-size lead-clearing, lead-preparation, stabilization, and
single-step nondivisible pivot-improvement layers are verified over both `Int`
and `Q[X]`. The Smith Phase 3 uniqueness closure is now done, and the current
PID bridge now consists of two layers: a semantic quotient/decomposition layer
and a first coefficient-facing layer for full-rank `Int` matrices. Quotients
are transported to the executable Smith result and decomposed into torsion
factors plus a free part; full-rank cases are related back to mathlib's PID
quotient theorems via `PiSpan`, `DirectSum`, and `PiZMod` equivalences; and the
bridge now exposes normalized `natAbs` coefficient-list readouts on both the
executable and mathlib sides. The remaining project work shifts to stronger
coefficient-level comparison theorems beyond this normalized readout/length
layer, together with the application layer.

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
lake build # Must output 0 warnings
lake env lean scripts/AxiomAudit.lean
lake env lean NormalForms/Matrix/Hermite/Algorithm.lean
lake env lean NormalForms/Matrix/Hermite/Basic.lean
lake env lean NormalForms/Matrix/Smith/Defs.lean
lake env lean NormalForms/Matrix/Smith/Algorithm.lean
lake env lean NormalForms/Matrix/Smith/Basic.lean
lake env lean NormalForms/Matrix/Smith/Uniqueness.lean
lake env lean NormalForms/Bridge/MathlibPID/Basic.lean
lake env lean NormalForms/Bridge/MathlibPID/Quotient.lean
lake env lean NormalForms/Examples/AbelianGroups/Basic.lean
```

The committed `lake-manifest.json` pins a compatible mathlib snapshot. On a fresh machine, Lake will still need network access the first time it materializes `.lake/packages`.

## Layout

- `NormalForms/Matrix/Elementary`: row and column operation skeletons, logs, and replay semantics
- `NormalForms/Matrix/Hermite`: split HNF stack with `Defs`, `Transform`, `Bezout`, `Algorithm`, `Basic`, and `Uniqueness`
- `NormalForms/Matrix/Smith`: split SNF stack with `Defs`, `Transform`, `Algorithm`, `Basic`, and `Uniqueness`
- `NormalForms/Matrix/Certificates`: reusable certificate shapes and unimodularity lemmas
- `NormalForms/Bridge/MathlibPID`: raw PID bridge helpers and normalized
  coefficient-list readouts in `Basic`, plus semantic quotient/decomposition
  and full-rank executable-vs-mathlib bridge theorems in `Quotient`
- `NormalForms/Examples/AbelianGroups`: sample matrices, executable HNF smoke
  checks, internal `Int` and `Q[X]` Smith spec/invariant-factor/same-size-step
  smoke, public Smith certificate/result packaging smoke, and the current
  bridge-facing examples
- `paper/`: manuscript planning notes
- `artifact/`: artifact packaging notes

## Scope

- Executable algorithms are scoped to `EuclideanDomain`
- Exact executable canonicality statements use a lightweight `CanonicalMod` mixin to capture canonical Euclidean remainders
- PID-level statements are scoped to specifications and bridge theorems; the
  currently completed bridge includes semantic quotient/direct-sum results and
  a first normalized `Int` witness-list comparison layer; direct coefficient-list
  equality against mathlib's chosen `smithNormalFormCoeffs` remains future work
- The initial research application is finitely generated abelian groups over `Z`

For the full roadmap, milestones, and submission strategy, see `PLAN.md`.
