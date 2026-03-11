# lean-normal-forms Plan

## Local Scaffold Status

- Repository name: `lean-normal-forms`
- Lean package name: `NormalForms`
- License: `Apache-2.0`
- Initial scaffold present for `README`, `LICENSE`, `CITATION.cff`, GitHub Actions, `lake build`, an axiom-audit smoke script, and Zenodo metadata
- Local environment baseline re-verified on March 11, 2026 with `lake build`, `lake env lean scripts/AxiomAudit.lean`, `lake env lean NormalForms/Matrix/Smith/Basic.lean`, and `lake env lean NormalForms/Examples/AbelianGroups/Basic.lean`
- The top-level SNF API is now stable but no longer placeholder-only: public `IsSmithNormalForm` is a real diagonal specification, `smithInvariantFactors` and `smithColumnSpan` are available, `SNFResult` packages the two-sided equation `U * A * V = S`, and `SNFResult.ofCertificate` / `SNFResult.toCertificate` provide the current public certificate boundary; the public `smithNormalForm` entrypoint still remains `none` until the executable Phase 3 kernel lands
- HNF uniqueness is complete, and the repository now has a concrete Smith Phase 3 base: internal recursive Smith predicates/results, two-sided transform scaffolding, same-size lead-reduction foundations, and example coverage are in place even though the executable kernel and uniqueness proofs are still pending
- The HNF kernel now follows the intended three-stage recursion: first-column elimination, lower-right recursion, and top-row reduction, with an explicit unimodular left-certificate invariant carried through the internal transform/result structures
- `CanonicalMod` is now instantiated for both `Int` and `Polynomial Rat`, so the current exactness boundary already covers the two main executable example domains
- The repository now fixes the planned subsystem boundaries, mixed-log certificate helpers, a reusable 2x2 Bezout elimination gadget, and smoke theorems over `Int` and `Q[X]`
- Public Smith examples intentionally stop at packaging-level checks: concrete Smith diagonal and invariant-factor computation remains on the internal `Fin` layer to avoid elaboration blow-ups from aggressive `Fintype.equivFin` simplification

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

- Keep the core public objects stable:
- `IsHermiteNormalForm`
- `IsSmithNormalForm`
- `HNFResult`
- `SNFResult`
- Keep the current helper readout and packaging boundary stable:
- `smithInvariantFactors`
- `smithColumnSpan`
- `HNFResult.toCertificate`
- `SNFResult.ofCertificate`
- `SNFResult.toCertificate`
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

- Current phase status on March 11, 2026: Phase 2 is complete, including public HNF correctness and uniqueness; Phase 3 is partially complete with a real Smith specification layer, public invariant-factor and certificate-packaging helpers, same-size lead-reduction foundations, and `CanonicalMod (Polynomial Rat)`; the next work is the nondivisible pivot-improvement layer, the outer recursive executable Smith algorithm, its public theorems, and Smith uniqueness
- Phase 1 is complete in `NormalForms/Matrix/Elementary`: executable row and column `swap` / `add` / `smul`, elementary-matrix realizations of each step, mixed-log left/right accumulators, the theorem `U(log) * A * V(log) = replayLog A log`, and a reusable 2x2 Bezout reduction matrix with determinant and transpose lemmas
- Phase 1 is complete in `NormalForms/Matrix/Certificates`: `Unimodular` as `IsUnit det`, unimodular step/log closure theorems, row-only and two-sided log-to-certificate helpers, and the executable-versus-certificate boundary for non-unit `smul`
- Phase 1 is complete in `NormalForms/Examples/AbelianGroups`: `Int`-based matrix-action smoke theorems, mixed-log certificate instantiations, non-unit scaling boundary checks, and Bezout examples over `Int` and `Q[X]`
- Phase 2 smoke coverage is now in `NormalForms/Examples/AbelianGroups`: concrete `Int` HNF outputs for zero / full-rank / rank-deficient / unit-boundary inputs, a nontrivial lower-right presentation-matrix smoke check, public `hermiteNormalForm` existence checks, a public HNF correctness smoke theorem, a public uniqueness smoke theorem, a public unimodularity smoke theorem, and a `HNFResult.toCertificate` example
- Phase 2 is complete in `NormalForms/Matrix/Hermite`: `IsHermiteNormalFormFin` is a real recursive predicate, the public `IsHermiteNormalForm` wrapper is in place, the module contains `RowTransform`, `LeftTransform`, block-lift / Bezout transport lemmas, `tailCols` / `lowerRight` replay transport lemmas, an executable Fin-indexed HNF kernel, the public theorems `hermiteNormalForm_isHermite` and `isHermiteNormalForm_unique_of_left_equiv`, a public `hermiteNormalForm_unimodular` helper theorem, and `CanonicalMod` instances for `Int` and `Polynomial Rat`
- Phase 3 groundwork is now in `NormalForms/Matrix/Smith`: the public `IsSmithNormalForm` wrapper is a real diagonal specification, `smithInvariantFactors` and `smithColumnSpan` are exposed, `Internal.IsSmithNormalFormFin` and `Internal.FinSNFResult` are in place, `TwoSidedTransform` exposes row/column/block-lift helpers, `SNFResult.ofCertificate` / `SNFResult.toCertificate` define the current public packaging boundary, `smithNormalForm_isSmith` is available, and the examples cover internal `Int` / `Q[X]` Smith diagonal-spec and invariant-factor smoke together with public certificate-packaging smoke
- Phase 3A.1 is now complete inside `NormalForms/Matrix/Smith`: `PivotState`, `LeadClearedState`, `PivotDivisibleState`, raw `clearFirstColumnByPivotStepData` / `clearFirstRowByPivotStepData`, pure-data `clearFirstColumnByPivotLoop` / `clearFirstRowByPivotLoop`, external invariance theorems, and the wrapper `clearLeadByPivot` all compile and are verified; the missing Smith pieces are still nondivisible pivot improvement, outer recursion, public existence/unimodularity extraction, and uniqueness
- The repo narrative is now synchronized with the completed HNF phase and partial Smith Phase 3 implementation: the remaining implementation work is the executable Smith kernel and proof layer, the PID bridge, and the application layer

## Phase Plan

- Phase 1, completed: elementary row and column operations, unimodularity predicates, operation logs, small-step semantics, mixed-log certificates, a 2x2 Bezout elimination gadget, and the standard lemmas needed by the algorithms
- Phase 2, completed: recursive row-style HNF on top of the Phase 1 log-certificate and Bezout-elimination layer, together with certified normality, public correctness extraction, uniqueness, and the documented `CanonicalMod` boundary for exact canonical representatives
- Phase 3, current focus for the next six weeks: finish the executable SNF kernel in staged form on top of the already-landed Smith specification and transform scaffolding; the next substeps are nondivisible pivot improvement with a strict descent argument, outer recursion for `smithNormalFormFin`, public existence/correctness and left/right unimodularity theorems, and finally Smith uniqueness
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
- `lake env lean NormalForms/Matrix/Smith/Basic.lean`
- all demo modules compile
- all eventual `#eval` examples run on `Z` and `Q[X]`
- Example coverage must include:
- zero matrices
- small full-rank matrices
- rank-deficient matrices
- unit-boundary canonicalization cases
- a `Z` presentation matrix
- a `Q[X]` Euclidean-domain example
- Public Smith smoke should prefer packaging theorems over concrete `simp` through `Fintype.equivFin`; concrete diagonal and invariant-factor checks should stay on the internal `Fin` layer unless a dedicated `Fin`-public API is introduced later

## Acceptance Criteria

- HNF correctness and uniqueness
- SNF correctness and uniqueness
- explicit unimodular certificates
- PID bridge theorem
- one clear abelian-group application

## Public Milestones

- First public checkpoint, reached on March 7, 2026: HNF uniqueness is stable and the SNF interface is frozen; the repository is ready for an `arXiv` preprint and a community-facing talk
- Current local milestone, reached on March 11, 2026: the Smith layer now has a real public specification, public invariant-factor and certificate-packaging helpers, internal recursive scaffolding, verified same-size lead-reduction foundations, and `Q[X]` canonical remainder support; the main remaining blockers are nondivisible pivot improvement, the outer recursive Smith kernel, Smith public proof extraction, Smith uniqueness, and the PID bridge
- `ITP` freeze point: eight weeks before the target submission deadline, all major theorems must already be done and only writing, experiments, and API cleanups remain
- If SNF uniqueness or the PID bridge is still unstable at the freeze point, do not force an `ITP` regular submission; switch to `arXiv + talk + JAR/LMCS`
- After submission, use a dedicated `submission-fix` branch for reviewer-blocker changes only
- After acceptance, tag the repo, archive the artifact in Zenodo, update the accepted preprint, and prepare an explicit mathlib split plan

## Assumptions And Defaults

- Assume a solo repository and solo paper unless collaboration changes concretely
- Do not copy unpublished proof text or code text from the existing group repository into this project
- Frame the first paper around `Lean 4 + executable normal forms + mathlib bridge`, not generic formal linear algebra
- Do not promise executable algorithms over arbitrary PIDs; executable scope stays with Euclidean domains and PID stays at the bridge and specification layer
