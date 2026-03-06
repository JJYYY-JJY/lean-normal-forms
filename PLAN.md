# lean-normal-forms Plan

## Local Scaffold Status

- Repository name: `lean-normal-forms`
- Lean package name: `NormalForms`
- License: `Apache-2.0`
- Initial scaffold present for `README`, `LICENSE`, `CITATION.cff`, GitHub Actions, `lake build`, an axiom-audit smoke script, and Zenodo metadata
- Local environment baseline verified on March 6, 2026 with `lake exe cache get`, `lake build`, and `lake env lean scripts/AxiomAudit.lean`
- The top-level SNF public API is still a compile-time stub; the HNF surface now has a real recursive predicate, an executable Fin-indexed kernel under `NormalForms.Matrix.Hermite.Internal`, and a public `hermiteNormalForm` entrypoint that returns `some result`
- The repository now fixes the planned subsystem boundaries, mixed-log certificate helpers, a reusable 2x2 Bezout elimination gadget, and smoke theorems over `Int` and `Q[X]`

## Summary

- Working title: `Executable Hermite and Smith Normal Forms in Lean 4 over Euclidean Domains, with a PID bridge to mathlib`
- Core claim: not "the first formalization of HNF/SNF" in general, but the first Lean 4 and mathlib-oriented package that combines executable normal-form algorithms, unimodular certificates, uniqueness theorems, and a bridge to the existing PID library theorems
- Executable algorithms are scoped to `EuclideanDomain`
- PID-level statements are scoped to specification and bridge theorems
- The paper narrative should focus on formalization architecture, canonicality, and the connection to mathlib; benchmarks and artifact quality matter, but they are not the main scientific claim

## Venue Path And Submission Rules

- Primary route: `arXiv/CoRR` preprint plus `ITP 2027`, unless the project naturally grows into a journal-first submission
- Journal fallback: `JAR` or `LMCS`
- Community exposure fallback: `arXiv/CoRR` plus `Lean Together` or another talk-only venue, then a journal submission
- The `ITP 2026` deadline on February 19, 2026 has already passed, so the next realistic conference target is the following cycle
- Do not submit the same archival manuscript to more than one of `ITP`, `CPP`, `JAR`, `LMCS`, or `JFR` at the same time
- Allowed parallel combinations are limited to `preprint + one archival venue`, `talk-only venue + one archival venue`, or `conference version followed by a substantially extended journal version`

## Novelty And Collision

- The strongest prior art sits in Isabelle rather than Lean: executable HNF and SNF formalizations already exist there
- Reimplementing HNF and SNF in Lean without more would not be a strong enough novelty claim
- The Lean-specific novelty must therefore come from three things:
- a reusable matrix-normal-form API
- a bridge to mathlib's PID results
- a concrete mathematical application layer
- The current mathlib baseline already contains PID-side Smith normal form structure theorems and transvection-based diagonalization over fields
- Therefore the contribution must be framed as `algorithmic + canonical + bridge`, not as the first appearance of Smith normal form in Lean

## Public API Commitments

- Expose exactly four top-level public objects as the stable API surface:
- `IsHermiteNormalForm`
- `IsSmithNormalForm`
- `HNFResult`
- `SNFResult`
- `HNFResult` must contain `U` and `H` with the equation `U * A = H`
- `SNFResult` must contain `U`, `S`, and `V` with the equation `U * A * V = S`
- The primary algorithmic interfaces are row-style HNF and two-sided SNF
- Do not maintain separate row-style and column-style implementations as co-equal entry points; obtain column-style views by transposition
- Canonicalization should ultimately rely on `NormalizationMonoid.normalize` plus Euclidean remainder conventions so the final theorems state exact equality rather than equality up to associates

## Repository Structure

- `NormalForms/Matrix/Elementary`
- `NormalForms/Matrix/Hermite`
- `NormalForms/Matrix/Smith`
- `NormalForms/Matrix/Certificates`
- `NormalForms/Bridge/MathlibPID`
- `NormalForms/Examples/AbelianGroups`
- `paper/`
- `artifact/`

## Progress Snapshot

- Current phase status on March 6, 2026: `Phase 2 pushed to executable HNF; remaining work narrowed`
- Phase 1 is complete in `NormalForms/Matrix/Elementary`: executable row and column `swap` / `add` / `smul`, elementary-matrix realizations of each step, mixed-log left/right accumulators, the theorem `U(log) * A * V(log) = replayLog A log`, and a reusable 2x2 Bezout reduction matrix with determinant and transpose lemmas
- Phase 1 is complete in `NormalForms/Matrix/Certificates`: `Unimodular` as `IsUnit det`, unimodular step/log closure theorems, row-only and two-sided log-to-certificate helpers, and the executable-versus-certificate boundary for non-unit `smul`
- Phase 1 is complete in `NormalForms/Examples/AbelianGroups`: `Int`-based matrix-action smoke theorems, mixed-log certificate instantiations, non-unit scaling boundary checks, and Bezout examples over `Int` and `Q[X]`
- Phase 2 smoke coverage is now in `NormalForms/Examples/AbelianGroups`: concrete `Int` HNF outputs for zero / full-rank / rank-deficient / unit-boundary inputs, a presentation-matrix smoke check, public `hermiteNormalForm` existence checks, and a `HNFResult.toCertificate` example
- Phase 2 is materially complete in `NormalForms/Matrix/Hermite`: `IsHermiteNormalFormFin` is a real recursive predicate, the public `IsHermiteNormalForm` wrapper is in place, the module contains `RowTransform`, log/reindex lifting helpers, `tailCols` / `lowerRight` replay transport lemmas, and an executable Fin-indexed HNF kernel that now feeds the public `hermiteNormalForm` result packaging
- The repo narrative is now synchronized with the executable HNF core: README status text and example coverage reflect the new reality, and the remaining work is correctness strengthening, uniqueness/canonicality, SNF, the PID bridge, and the application layer
- Phases 3 through 5 have not started in the sense of algorithmic or theorem-level content; their current files remain API or theorem scaffolds

## Phase Plan

- Phase 1, completed: elementary row and column operations, unimodularity predicates, operation logs, small-step semantics, mixed-log certificates, a 2x2 Bezout elimination gadget, and the standard lemmas needed by the algorithms
- Phase 2, four weeks: row-style HNF consuming the Phase 1 log-certificate and Bezout-elimination layer, with pivot search, pivot normalization, reduction above and below pivots, a real `IsHermiteNormalForm` predicate, and a first correctness/uniqueness proof skeleton
- Phase 3, six weeks: SNF on top of the HNF layer with column operations, diagonalization, divisibility cleanup between neighboring diagonal entries, and proofs of correctness, Smith-form satisfaction, and uniqueness
- Phase 4, three weeks: PID bridge theorem aligning the executable invariant factors with mathlib's `Submodule.smithNormalForm...` results up to normalization
- Phase 5, two weeks: finitely generated abelian groups over `Z` via presentation matrices as the mandatory mathematical showcase

## Upstream Strategy

- Keep the main development in this standalone repository
- Upstream only reusable infrastructure and generic lemmas later
- Do not make large mathlib upstreaming a blocking objective during the main research phase

## Regression And Demo Plan

- Required recurring checks:
- `lake build`
- axiom audit
- all demo modules compile
- all eventual `#eval` examples run on `Z` and `Q[X]`
- Example coverage must include:
- zero matrices
- small full-rank matrices
- rank-deficient matrices
- unit-boundary canonicalization cases
- a `Z` presentation matrix
- a `Q[X]` Euclidean-domain example

## Acceptance Criteria

- HNF correctness and uniqueness
- SNF correctness and uniqueness
- explicit unimodular certificates
- PID bridge theorem
- one clear abelian-group application

## Public Milestones

- First public checkpoint: after HNF uniqueness is stable and the SNF interface is frozen, publish an `arXiv` preprint and give a community-facing talk
- `ITP` freeze point: eight weeks before the target submission deadline, all major theorems must already be done and only writing, experiments, and API cleanups remain
- If SNF uniqueness or the PID bridge is still unstable at the freeze point, do not force an `ITP` regular submission; switch to `arXiv + talk + JAR/LMCS`
- After submission, use a dedicated `submission-fix` branch for reviewer-blocker changes only
- After acceptance, tag the repo, archive the artifact in Zenodo, update the accepted preprint, and prepare an explicit mathlib split plan

## Assumptions And Defaults

- Assume a solo repository and solo paper unless collaboration changes concretely
- Do not copy unpublished proof text or code text from the existing group repository into this project
- Frame the first paper around `Lean 4 + executable normal forms + mathlib bridge`, not generic formal linear algebra
- Do not promise executable algorithms over arbitrary PIDs; executable scope stays with Euclidean domains and PID stays at the bridge and specification layer






