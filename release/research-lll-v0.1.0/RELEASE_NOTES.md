# lean-normal-forms research/lll 0.1.0

Research version 0.1.0 completes the independently gated exact-integer LLL
line. It is additive on top of lean-normal-forms 1.2.2 and leaves the stable
core facade unchanged.

## Verified algorithm

- Row vectors use exact rational Gram--Schmidt data with fixed
  `delta = 3/4` and `eta = 1/2`.
- A source-pinned terminating dense reducer supplies the reduced basis, while
  a synchronized trace accumulates every row addition and adjacent swap.
- The full-rank result returns `U`, a chosen inverse, both inverse identities,
  `U * B = B'`, and exact LLL reducedness.
- An HNF rank decomposition extends the entry to empty, zero, rectangular,
  and rank-deficient inputs with a reduced independent prefix and zero tail.
- The column entry is only the transpose adapter, so no second basis
  convention or algorithm can drift from the row implementation.

## Complexity evidence

- Exact telemetry counts size reductions, swaps, and state refreshes along the
  terminating trace.
- Every profile proves its event total is bounded by the verified fuel times
  `2 * rows + 2`.
- The trace records a monotone height covering every transformed basis and
  every actual row multiplier.
- The shared verified sign-magnitude arithmetic model prices the recorded
  events at the observed working width.
- This is an a-posteriori profile-dependent reference budget, not an
  input-only polynomial LLL complexity theorem. It excludes the HNF rank
  decomposition and accumulated transform-matrix multiplication costs.

## Reproducibility

- The research facade freeze contains 114 checked entries.
- The JSON axiom audit covers 20 theorem roots and observes exactly
  `Classical.choice`, `Quot.sound`, and `propext`.
- Four deterministic native cases cover small and dense full-rank inputs, a
  dependent row input, and the transpose column adapter.
- Five benchmark stages retain one warmup and seven raw observations each,
  together with source, binary, software, and hardware fingerprints.
- `scripts/verify.sh lll` rebuilds the profile, re-elaborates execution
  guards, runs the full test suite, validates committed evidence, and audits
  axioms. Fresh timing and publication builds remain separate operations.

## Scope and trust

Kernel theorems establish semantic correctness, explicit inverse equations,
rank handling, and the formal profile bounds. Native wall time and RSS are
observational only. Executable-only fixtures may use native decision
procedures, but audited public theorem roots contain no native/compiler trust.
FLINT is neither linked nor trusted.

These are local release materials. They do not create a GitHub release, tag,
DOI, deposition, or upstream pull request.
