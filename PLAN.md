# lean-normal-forms Plan

## Local Scaffold Status

- Repository name: `lean-normal-forms`
- Lean package name: `NormalForms`
- License: `Apache-2.0`
- Initial scaffold present for `README`, `LICENSE`, `CITATION.cff`, GitHub Actions, `lake build`, an axiom-audit smoke script, and Zenodo metadata
- Local environment baseline re-verified on March 7, 2026 with `lake build`, `lake env lean scripts/AxiomAudit.lean`, and `lake env lean NormalForms/Examples/AbelianGroups/Basic.lean`
- The top-level SNF public API is now frozen as a compile-time scaffold: `IsSmithNormalForm` remains a placeholder predicate, `SNFResult` packages the two-sided equation `U * A * V = S`, and the public `smithNormalForm` entrypoint remains `none` until the later Phase 3 algorithm and proof work lands
- HNF uniqueness is complete and the SNF interface is frozen; the repository has reached its first public checkpoint and is ready for the arXiv preprint.
- The HNF kernel now follows the intended three-stage recursion: first-column elimination, lower-right recursion, and top-row reduction, with an explicit unimodular left-certificate invariant carried through the internal transform/result structures
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
- Canonicalization should rely on `NormalizationMonoid.normalize` plus explicit canonical-remainder assumptions so the final theorems state exact equality rather than equality up to associates

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

- Current phase status on March 7, 2026: `Phase 2 is complete, including public HNF correctness and uniqueness; the Phase 3 SNF public API is frozen, and the next work is the executable Smith algorithm plus proofs`
- Phase 1 is complete in `NormalForms/Matrix/Elementary`: executable row and column `swap` / `add` / `smul`, elementary-matrix realizations of each step, mixed-log left/right accumulators, the theorem `U(log) * A * V(log) = replayLog A log`, and a reusable 2x2 Bezout reduction matrix with determinant and transpose lemmas
- Phase 1 is complete in `NormalForms/Matrix/Certificates`: `Unimodular` as `IsUnit det`, unimodular step/log closure theorems, row-only and two-sided log-to-certificate helpers, and the executable-versus-certificate boundary for non-unit `smul`
- Phase 1 is complete in `NormalForms/Examples/AbelianGroups`: `Int`-based matrix-action smoke theorems, mixed-log certificate instantiations, non-unit scaling boundary checks, and Bezout examples over `Int` and `Q[X]`
- Phase 2 smoke coverage is now in `NormalForms/Examples/AbelianGroups`: concrete `Int` HNF outputs for zero / full-rank / rank-deficient / unit-boundary inputs, a nontrivial lower-right presentation-matrix smoke check, public `hermiteNormalForm` existence checks, a public HNF correctness smoke theorem, a public uniqueness smoke theorem, a public unimodularity smoke theorem, and a `HNFResult.toCertificate` example
- Phase 2 is complete in `NormalForms/Matrix/Hermite`: `IsHermiteNormalFormFin` is a real recursive predicate, the public `IsHermiteNormalForm` wrapper is in place, the module contains `RowTransform`, `LeftTransform`, block-lift / Bezout transport lemmas, `tailCols` / `lowerRight` replay transport lemmas, an executable Fin-indexed HNF kernel, the public theorems `hermiteNormalForm_isHermite` and `isHermiteNormalForm_unique_of_left_equiv`, and a public `hermiteNormalForm_unimodular` helper theorem
- The repo narrative is now synchronized with the completed HNF phase and frozen SNF interface: README status text and example coverage reflect correctness plus uniqueness, while the remaining implementation work is SNF algorithms and proofs, the PID bridge, and the application layer
- Phase 3 has now started at the public-interface level: the SNF API is frozen, while the algorithmic and theorem-level content for Phases 3 through 5 remains scaffolded

## Phase Plan

- Phase 1, completed: elementary row and column operations, unimodularity predicates, operation logs, small-step semantics, mixed-log certificates, a 2x2 Bezout elimination gadget, and the standard lemmas needed by the algorithms
- Phase 2, completed: recursive row-style HNF on top of the Phase 1 log-certificate and Bezout-elimination layer, together with certified normality, public correctness extraction, uniqueness, and the documented `CanonicalMod` boundary for exact canonical representatives
- Phase 3, current focus for the next six weeks: SNF abstraction skeleton and executable algorithm on top of the HNF layer, with column operations, diagonalization, divisibility cleanup between neighboring diagonal entries, and proofs of correctness, Smith-form satisfaction, and uniqueness
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

- First public checkpoint, reached on March 7, 2026: HNF uniqueness is stable and the SNF interface is frozen; the repository is ready for an `arXiv` preprint and a community-facing talk
- `ITP` freeze point: eight weeks before the target submission deadline, all major theorems must already be done and only writing, experiments, and API cleanups remain
- If SNF uniqueness or the PID bridge is still unstable at the freeze point, do not force an `ITP` regular submission; switch to `arXiv + talk + JAR/LMCS`
- After submission, use a dedicated `submission-fix` branch for reviewer-blocker changes only
- After acceptance, tag the repo, archive the artifact in Zenodo, update the accepted preprint, and prepare an explicit mathlib split plan

## Assumptions And Defaults

- Assume a solo repository and solo paper unless collaboration changes concretely
- Do not copy unpublished proof text or code text from the existing group repository into this project
- Frame the first paper around `Lean 4 + executable normal forms + mathlib bridge`, not generic formal linear algebra
- Do not promise executable algorithms over arbitrary PIDs; executable scope stays with Euclidean domains and PID stays at the bridge and specification layer



