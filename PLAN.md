# lean-normal-forms Plan

## Local Scaffold Status

- Repository name: `lean-normal-forms`
- Lean package name: `NormalForms`
- License: `Apache-2.0`
- Initial scaffold present for `README`, `LICENSE`, `CITATION.cff`, GitHub Actions, `lake build`, an axiom-audit smoke script, and Zenodo metadata
- **Zero Warnings Milestone:** The library currently builds with exactly zero warnings and zero errors.
- Local environment baseline re-verified on March 21, 2026 with `lake build`, `lake env lean scripts/AxiomAudit.lean`, `lake env lean NormalForms/Matrix/Hermite/Algorithm.lean`, `lake env lean NormalForms/Matrix/Hermite/Basic.lean`, `lake env lean NormalForms/Matrix/Smith/Defs.lean`, `lake env lean NormalForms/Matrix/Smith/Algorithm.lean`, `lake env lean NormalForms/Matrix/Smith/Basic.lean`, `lake env lean NormalForms/Matrix/Smith/Uniqueness.lean`, `lake env lean NormalForms/Bridge/MathlibPID/Basic.lean`, `lake env lean NormalForms/Bridge/MathlibPID/Quotient.lean`, `lake env lean NormalForms/Applications/AbelianGroups/Basic.lean`, and `lake env lean NormalForms/Examples/AbelianGroups/Basic.lean`
- The top-level SNF API is now stable and no longer placeholder-only: public `IsSmithNormalForm` is a real diagonal specification, `smithInvariantFactors` and `smithColumnSpan` are available, `SNFResult` packages the two-sided equation `U * A * V = S`, and `SNFResult.ofCertificate` / `SNFResult.toCertificate` provide the current public certificate boundary; the public `smithNormalForm` entrypoint is executable, `isSmithNormalForm_eq_of_invariantFactors_eq` is available, `first_invariantFactor_eq_of_two_sided_equiv` has landed in `NormalForms.Matrix.Smith.Uniqueness`, and the full public Smith uniqueness theorem `isSmithNormalForm_unique_of_two_sided_equiv` is now proved via the completed decomposed `diagPrefixProduct` / minor-divisibility chain
- HNF uniqueness is complete, and the repository now has a concrete completed Smith Phase 3 layer together with a Phase 4 bridge layer: internal recursive Smith predicates/results, an executable recursive driver, two-sided transform scaffolding, same-size lead-clearing, lead-preparation, single-step pivot-improvement foundations, example coverage, diagonal-entry length/nonzero/zero lemmas, first-invariant-factor preservation under two-sided unimodular equivalence, the completed `diagPrefixProduct`-based general-`k` minor chain in `NormalForms.Matrix.Smith.Uniqueness`, the internal theorem `isSmithNormalFormFin_unique_of_two_sided_equiv`, the public theorem `isSmithNormalForm_unique_of_two_sided_equiv`, the raw `MathlibPID.Basic` helper layer, executable-side normalized `Int` coefficient-list readout, the full-rank executable invariant-factor count theorem, and the `MathlibPID.Quotient` semantic quotient/decomposition plus full-rank compatibility bridge
- The HNF kernel now follows the intended three-stage recursion: first-column elimination, lower-right recursion, and top-row reduction, with an explicit unimodular left-certificate invariant carried through the internal transform/result structures
- `CanonicalMod` is now instantiated for both `Int` and `Polynomial Rat`, so the current exactness boundary already covers the two main executable example domains
- The repository now fixes the planned subsystem boundaries, including the post-Phase-3 split of the former Hermite/Smith monoliths into dedicated `Defs` / transport / algorithm facades, together with mixed-log certificate helpers, a reusable 2x2 Bezout elimination gadget, and smoke theorems over `Int` and `Q[X]`
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
- Keep the current `Int` abelian-group application boundary stable:
- `presentationSubmodule`
- `presentationQuotient`
- `presentationInvariantFactorCount`
- `presentationInvariantFactorFn`
- `presentationInvariantFactors`
- `presentationFreeRank`
- `presentationQuotientEquivPiZModProd`
- `presentationQuotientEquivPiZMod_of_fullRank`
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
- `NormalForms/Applications/AbelianGroups`
- `NormalForms/Examples/AbelianGroups`
- `paper/`
- `artifact/`

## Progress Snapshot

- Current phase status on March 21, 2026: Phase 2 is complete, including public HNF correctness and uniqueness; Phase 3 is complete as well, including the real Smith specification layer, public invariant-factor and certificate-packaging helpers, a full executable recursive `smithNormalFormFin` kernel, public `smithNormalForm` existence/isSmith/left-right-unimodular theorems, invariant-factor-based Smith uniqueness, `first_invariantFactor_eq_of_two_sided_equiv`, the completed decomposed `diagPrefixProduct` / general-`k` minor chain, and the final public Smith uniqueness theorem under explicit two-sided unimodular equivalence; Phase 4 now has a semantic bridge layer in `NormalForms.Bridge.MathlibPID.Quotient` with executable invariant-factor readout, quotient transport through the chosen executable Smith result, coordinatewise `Submodule.pi` identification for Smith matrices, general torsion-plus-free quotient decompositions, `ℤ`-specialized `ZMod` decompositions, the full-rank theorem `pidExecutableInvariantFactorCount_eq_card_rows_of_finrank_eq_card`, and full-rank compatibility equivalences with mathlib's `quotientEquivPiSpan` / `quotientEquivDirectSum` / `quotientEquivPiZMod`; `NormalForms.Bridge.MathlibPID.Basic` now also exposes executable-side and mathlib-side normalized `Int` coefficient-list readouts. Phase 5 is now complete for the current `Int`-focused scope: `NormalForms.Applications.AbelianGroups` exposes the presentation quotient/submodule wrappers, executable invariant-factor and free-rank readouts, the public torsion-plus-free equivalence `presentationQuotientEquivPiZModProd`, and the full-rank specialization `presentationQuotientEquivPiZMod_of_fullRank`, while the examples instantiate that API on the current full-rank, unit-boundary, and mixed torsion-plus-free showcase matrices. No abstract theorem `pidFullRankMathlibSmithCoeffNatAbsList_eq_executable` landed; the remaining generic blocker is still missing mathlib witness canonicality for `smithNormalFormCoeffs`, but that no longer blocks the current application-layer milestone
- The project has hit the **Zero Warnings** milestone across all currently implemented modules.
- Phase 1 is complete in `NormalForms/Matrix/Elementary`: executable row and column `swap` / `add` / `smul`, elementary-matrix realizations of each step, mixed-log left/right accumulators, the theorem `U(log) * A * V(log) = replayLog A log`, and a reusable 2x2 Bezout reduction matrix with determinant and transpose lemmas
- Phase 1 is complete in `NormalForms/Matrix/Certificates`: `Unimodular` as `IsUnit det`, unimodular step/log closure theorems, row-only and two-sided log-to-certificate helpers, and the executable-versus-certificate boundary for non-unit `smul`
- Phase 1 is complete in `NormalForms/Examples/AbelianGroups`: `Int`-based matrix-action smoke theorems, mixed-log certificate instantiations, non-unit scaling boundary checks, and Bezout examples over `Int` and `Q[X]`
- Phase 2 smoke coverage is now in `NormalForms/Examples/AbelianGroups`: concrete `Int` HNF outputs for zero / full-rank / rank-deficient / unit-boundary inputs, a nontrivial lower-right presentation-matrix smoke check, public `hermiteNormalForm` existence checks, a public HNF correctness smoke theorem, a public uniqueness smoke theorem, a public unimodularity smoke theorem, and a `HNFResult.toCertificate` example
- Phase 2 is complete in `NormalForms/Matrix/Hermite`: `IsHermiteNormalFormFin` is a real recursive predicate, the public `IsHermiteNormalForm` wrapper is in place, the old monolith is now split across `Defs`, `Transform`, `Bezout`, `Algorithm`, and `Basic`, the executable Fin-indexed HNF kernel lives in `Algorithm`, the public theorems `hermiteNormalForm_isHermite` and `isHermiteNormalForm_unique_of_left_equiv` are available, `hermiteNormalForm_unimodular` exposes the left certificate, and `CanonicalMod` instances exist for `Int` and `Polynomial Rat`
- Phase 3 is now complete in `NormalForms/Matrix/Smith`: the public `IsSmithNormalForm` wrapper is a real diagonal specification, `smithInvariantFactors` and `smithColumnSpan` are exposed, the former Smith monolith is now split across `Defs`, `Transform`, `Algorithm`, and `Basic`, `Internal.IsSmithNormalFormFin` / `Internal.FinSNFResult` and the executable `Internal.smithNormalFormFin` kernel are in place, `TwoSidedTransform` exposes row/column/block-lift helpers, `SNFResult.ofCertificate` / `SNFResult.toCertificate` define the current public packaging boundary, `smithNormalForm_exists` / `smithNormalForm_isSmith` / left-right unimodularity extraction are available, `isSmithNormalForm_eq_of_invariantFactors_eq` is available, `first_invariantFactor_eq_of_two_sided_equiv` is proved, `isSmithNormalFormFin_unique_of_two_sided_equiv` and `isSmithNormalForm_unique_of_two_sided_equiv` are proved, and the examples cover internal `Int` / `Q[X]` Smith diagonal-spec, invariant-factor, same-size-step, and executable-kernel smoke together with public Smith API smoke
- Phase 4 bridge coverage is now in `NormalForms/Examples/AbelianGroups`: presentation-matrix quotient / `PiSpan` / `DirectSum` / `PiZMod` smoke, mixed torsion-plus-free `PiSpanProd` / `PiZModProd` smoke, full-rank executable invariant-factor-count smoke, full-rank mathlib-vs-executable quotient / `DirectSum` / `PiZMod` equivalence smoke, and example-level normalized coefficient-list equality smoke for `fullRankMatrixZ`, `unitBoundaryMatrixZ`, and `presentationMatrixZ`
- Phase 5 is now complete in `NormalForms/Applications/AbelianGroups`: `Int` presentation matrices have public wrappers for the presented submodule, the quotient `ℤ^m / im(A)`, executable invariant-factor and free-rank readouts, the torsion-plus-free decomposition `presentationQuotientEquivPiZModProd`, and the full-rank specialization `presentationQuotientEquivPiZMod_of_fullRank`
- Phase 5 smoke coverage is now in `NormalForms/Examples/AbelianGroups`: public application-layer quotient decompositions for `presentationMatrixZ`, `mixedTorsionFreeMatrixZ`, and `unitBoundaryMatrixZ`, together with public invariant-factor readout smoke over the same examples
- Phase 3A.1 is now complete inside `NormalForms/Matrix/Smith`: `PivotState`, `LeadClearedState`, `PivotDivisibleState`, raw `clearFirstColumnByPivotStepData` / `clearFirstRowByPivotStepData`, pure-data `clearFirstColumnByPivotLoop` / `clearFirstRowByPivotLoop`, external invariance theorems, and the wrapper `clearLeadByPivot` all compile and are verified
- Phase 3A.2 is now complete inside `NormalForms/Matrix/Smith`: the pure algebra gcd/mod kernel, the HNF-to-Smith top-left bridge theorem, row/column `prepareLead...StepData` wrappers, lower-right witness injection, `improvePivotStepData`, `improvePivot`, and the single-step strict-descent theorem bundle are now factored and verified on the same-size layer
- Phase 3A.3 is now complete inside `NormalForms/Matrix/Smith`: first-undivisible search correctness wrappers for the first column, first row, and lower-right block, same-size `prepareLeadColumn` / `prepareLeadRow` state wrappers, factor-count strict-descent lemmas, and the generic same-size `stabilizePivot` driver are now in place, together with internal `Int` smoke coverage for column, row, lower-right-improvement, and already-divisible cases; outer recursion, public existence/unimodularity extraction, and the final Smith uniqueness closure have all landed
- The repo narrative is now synchronized with the completed HNF phase, completed executable Smith Phase 3 layer, completed Phase 4 bridge layer, and the completed current-scope Phase 5 `Int` application layer: semantic quotient/decomposition theorems, normalized `Int` witness-list readouts, public presentation-quotient decomposition wrappers, and bridge/application smoke examples are all in place; generic coefficient-level comparison against mathlib witness lists remains blocked only on upstream canonicality

## Phase Plan

- Phase 1, completed: elementary row and column operations, unimodularity predicates, operation logs, small-step semantics, mixed-log certificates, a 2x2 Bezout elimination gadget, and the standard lemmas needed by the algorithms
- Phase 2, completed: recursive row-style HNF on top of the Phase 1 log-certificate and Bezout-elimination layer, together with certified normality, public correctness extraction, uniqueness, and the documented `CanonicalMod` boundary for exact canonical representatives
- Phase 3, completed: close the public Smith uniqueness gap on top of the executable SNF kernel and minor/diagonal-entry groundwork, culminating in the completed decomposed general-`k` minor-divisibility chain in `NormalForms.Matrix.Smith.Uniqueness` and the final public two-sided uniqueness theorem
- Phase 4, completed at the example level: semantic PID bridge plus normalized `natAbs` readouts on both the executable and mathlib sides, shared full-rank count control, executable-vs-mathlib quotient/direct-sum/`PiZMod` compatibility, and example-level structural-counting proofs of full-rank coefficient-list equality for the current `Int` showcase matrices; the remaining generic coefficient-comparison work is blocked on upstream witness canonicality
- Phase 5, completed for the current repository scope: finitely generated abelian groups over `Z` via presentation matrices now have a public `Int` application API and concrete showcase decompositions, including torsion-plus-free and full-rank specializations

## Upstream Strategy

- Keep the main development in this standalone repository
- Upstream only reusable infrastructure and generic lemmas later
- Do not make large mathlib upstreaming a blocking objective during the main research phase

## Regression And Demo Plan

- Required recurring checks:
- `lake build` (must maintain zero errors and zero warnings)
- axiom audit
- `lake env lean NormalForms/Matrix/Hermite/Algorithm.lean`
- `lake env lean NormalForms/Matrix/Hermite/Basic.lean`
- `lake env lean NormalForms/Matrix/Smith/Defs.lean`
- `lake env lean NormalForms/Matrix/Smith/Algorithm.lean`
- `lake env lean NormalForms/Matrix/Smith/Basic.lean`
- `lake env lean NormalForms/Bridge/MathlibPID/Basic.lean`
- `lake env lean NormalForms/Bridge/MathlibPID/Quotient.lean`
- `lake env lean NormalForms/Applications/AbelianGroups/Basic.lean`
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
- PID bridge theorem, at minimum in semantic quotient/direct-sum form
- one clear abelian-group application

## Public Milestones

- First public checkpoint, reached on March 7, 2026: HNF uniqueness is stable and the SNF interface is frozen; the repository is ready for an `arXiv` preprint and a community-facing talk
- Current local milestone, reached on March 21, 2026: The repository still maintains the **Zero Warnings** milestone. The Smith layer has a real public specification, public invariant-factor and certificate-packaging helpers, an executable recursive Smith kernel, public existence/isSmith/left-right-unimodular extraction, invariant-factor-based uniqueness, the final public two-sided uniqueness theorem, verified same-size lead-clearing/lead-preparation/stabilization, executable-kernel smoke over `Int`, `Q[X]` canonical remainder support, the completed minor-divisibility uniqueness chain, normalized executable/mathlib `Int` coefficient-list readouts in `MathlibPID.Basic`, a semantic quotient/decomposition plus full-rank `PiSpan` / `DirectSum` / `PiZMod` bridge in `MathlibPID.Quotient`, and a completed current-scope Phase 5 application layer in `NormalForms.Applications.AbelianGroups` with public presentation-quotient decomposition theorems and example instantiations for full-rank, unit-boundary, and torsion-plus-free `Int` matrices; the remaining generic coefficient-comparison blocker is still upstream witness canonicality for `smithNormalFormCoeffs`, but the abelian-group application milestone is no longer blocked on it
- `ITP` freeze point: eight weeks before the target submission deadline, all major theorems must already be done and only writing, experiments, and API cleanups remain
- If the PID bridge or application layer is still unstable at the freeze point, do not force an `ITP` regular submission; switch to `arXiv + talk + JAR/LMCS`
- After submission, use a dedicated `submission-fix` branch for reviewer-blocker changes only
- After acceptance, tag the repo, archive the artifact in Zenodo, update the accepted preprint, and prepare an explicit mathlib split plan

## Assumptions And Defaults

- Assume a solo repository and solo paper unless collaboration changes concretely
- Do not copy unpublished proof text or code text from the existing group repository into this project
- Frame the first paper around `Lean 4 + executable normal forms + mathlib bridge`, not generic formal linear algebra
- Do not promise executable algorithms over arbitrary PIDs; executable scope stays with Euclidean domains and PID stays at the bridge and specification layer
