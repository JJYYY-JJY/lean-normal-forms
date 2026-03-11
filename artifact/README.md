# artifact

This directory is reserved for the reproducibility bundle that accompanies the paper.

Planned contents:

- build instructions and exact toolchain snapshot
- demo modules for `Z` and `Q[X]`
- example matrices that exercise zero, full-rank, rank-deficient, and unit-boundary cases
- release checklist for Zenodo archival

Current status:

- executable row-style HNF is complete, including the recursive kernel,
  explicit left certificates via `LeftTransform`, and public certificate
  packaging through `HNFResult.toCertificate`
- HNF correctness and uniqueness are proved, with exact uniqueness isolated
  behind the `CanonicalMod` interface for canonical remainder representatives
- `CanonicalMod` is currently instantiated for both `Int` and `Polynomial Rat`
- the Smith layer is no longer placeholder-only: `IsSmithNormalForm` is a real
  diagonal specification, `smithInvariantFactors` and `smithColumnSpan` are
  available, the internal recursive predicate/result shell is in place,
  `TwoSidedTransform` provides reusable two-sided certificate scaffolding, and
  `SNFResult.ofCertificate` / `SNFResult.toCertificate` define the current
  public certificate boundary
- the current internal Smith milestone is a verified same-size lead-reduction
  foundation: pivot-state records, raw first-row/first-column clearing steps,
  pure-data clearing loops, external invariant theorems, and `clearLeadByPivot`
- `smithNormalForm` currently still returns `none`, so the executable Smith
  kernel is not yet end-to-end; the remaining work is nondivisible pivot
  improvement, outer recursion, public unimodularity helper theorems, and Smith
  uniqueness
- the PID bridge remains a placeholder API for future work rather than a
  completed comparison theorem layer
- the example layer already includes internal Smith diagonal/invariant-factor
  smoke theorems over `Int` and `Q[X]` together with public packaging smoke for
  `SNFResult.ofCertificate`; concrete public `simp` across `Fintype.equivFin`
  is intentionally avoided for elaboration stability
- the current local verification baseline on March 11, 2026 includes
  `lake build`, `lake env lean scripts/AxiomAudit.lean`,
  `lake env lean NormalForms/Matrix/Smith/Basic.lean`, and
  `lake env lean NormalForms/Examples/AbelianGroups/Basic.lean`
