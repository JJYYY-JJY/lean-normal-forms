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
- the SNF boundary is frozen but still placeholder-only: `IsSmithNormalForm`
  remains a placeholder predicate, `SNFResult` is defined, and
  `smithNormalForm` currently returns `none`
- the PID bridge remains a placeholder API for future work rather than a
  completed comparison theorem layer
- the artifact bundle itself is still being assembled, and the axiom audit
  remains a smoke script over the current public API surface
