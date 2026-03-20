# artifact

This directory is reserved for the reproducibility bundle that accompanies the paper.

Planned contents:

- build instructions and exact toolchain snapshot
- demo modules for `Z` and `Q[X]`
- example matrices that exercise zero, full-rank, rank-deficient, and unit-boundary cases
- release checklist for Zenodo archival

Current status:

- executable row-style HNF is complete, including the recursive kernel,
  explicit left certificates via `LeftTransform`, public correctness, public
  uniqueness, and certificate packaging through `HNFResult.toCertificate`
- `CanonicalMod` is instantiated for both `Int` and `Polynomial Rat`
- the executable Smith layer is complete through public existence/isSmith,
  left/right unimodularity extraction, invariant-factor-based uniqueness, and
  the final public theorem
  `isSmithNormalForm_unique_of_two_sided_equiv`
- `smithNormalForm` is executable and end-to-end; `SNFResult` packages the
  two-sided equation `U * A * V = S`, and `SNFResult.ofCertificate` /
  `SNFResult.toCertificate` define the current public certificate boundary
- the same-size Smith support layer is verified: pivot states, raw first-row /
  first-column clearing steps, pure-data clearing loops, lead preparation,
  single-step improvement, and stabilization are all in place
- the PID bridge is no longer placeholder-only:
  - `NormalForms.Bridge.MathlibPID.Basic` provides the raw column-span and
    `smithNormalFormOfLE` helper layer together with executable-side and
    mathlib-side normalized `Int` coefficient-list readouts
  - `NormalForms.Bridge.MathlibPID.Quotient` provides the semantic bridge:
    executable invariant-factor readout, quotient transport through the chosen
    executable Smith result, coordinatewise `Submodule.pi` identification for
    Smith matrices, general torsion-plus-free quotient decompositions,
    `ℤ`-specialized `ZMod` decompositions, the full-rank executable
    invariant-factor count theorem, and full-rank compatibility equivalences
    with mathlib's `quotientEquivPiSpan` / `quotientEquivDirectSum` /
    `quotientEquivPiZMod`
- the example layer now includes internal Smith diagonal/invariant-factor smoke
  over `Int` and `Q[X]`, public packaging smoke, semantic quotient bridge
  smoke, full-rank executable-vs-mathlib `PiZMod` compatibility smoke, and
  normalized executable-vs-mathlib coefficient-list length-comparison smoke
- the current local verification baseline on March 20, 2026 includes
  `lake build`, `lake env lean scripts/AxiomAudit.lean`,
  `lake env lean NormalForms/Bridge/MathlibPID/Basic.lean`,
  `lake env lean NormalForms/Bridge/MathlibPID/Quotient.lean`, and
  `lake env lean NormalForms/Examples/AbelianGroups/Basic.lean`
