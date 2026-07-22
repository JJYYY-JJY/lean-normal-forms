# lean-normal-forms research/kannan-bachem 0.1.0

Research version 0.1.0 completes the four formal complexity tiers for the
nonsingular-square integer Kannan--Bachem HNF and SNF paths. It is an
independent profile on top of lean-normal-forms 1.2.2 and does not enlarge or
change the stable core facade.

## Verified algorithms

- Deterministic row preparation turns every nonsingular square input into the
  leading-principal-minor invariant required by the HNF kernel.
- The preparation scan executes a cached, division-free Bird determinant
  through the verified sign-magnitude arithmetic model.
- Prepared HNF returns the existing strong `HNFResultFin`, including an
  explicit inverse and equality with the canonical core HNF.
- Total Smith stabilization implements the alternating one-column LHNF,
  transposed prepared HNF, divisible-column clear, and Step 7 injection
  schedule without a fallback.
- Binary pivot-size decrease proves termination, and lower-right structural
  recursion returns the existing strong `SNFResultFin`.
- The Smith result is proved equal to the canonical core Smith matrix.

## Complexity evidence

- Exact counters mirror additions, multiplications, XGCD calls,
  normalizations, and exact divisions across the full recursion.
- Closed polynomial bounds cover active matrices, arithmetic operands,
  forward transforms, inverses, and recursive certificate composition.
- `smithCoefficientProfile` bounds `S`, `U`, `U^-1`, `V`, and `V^-1` from
  the original dimension and input coefficient width.
- The bit-cost recurrence charges the actual costed binary scalar program,
  prepared determinant scans, clearing, injection, and all four dense products
  used to compose strong certificates.
- `smithBitOperationCost_le_polynomial` is the final square-SNF endpoint.

## Reproducibility

- The research facade freeze contains 572 declarations.
- The axiom audit covers 263 theorem roots and observes exactly `propext`,
  `Quot.sound`, and `Classical.choice`.
- Three deterministic cases cover prepared HNF, repeated Smith passes, and
  Step 7 injection.
- Four stages record one warmup and seven measurements each, with raw
  JSON/CSV timing and RSS plus deterministic formal telemetry and full source,
  binary, software, and hardware fingerprints.
- The captured host medians are 4.20 s prepared HNF, 0.06 s repeated-pass
  SNF, 2.25 s injection SNF, and 6.38 s for the complete corpus; these values
  are observational and not portable thresholds.
- `scripts/verify.sh kannan-bachem` forces direct re-elaboration of the
  execution guards, runs the full test suite, validates the audit and
  committed benchmark, and reruns the deterministic native corpus. Fresh
  timing and publication builds remain separate operations.

## Scope and trust

This version covers nonsingular square integer matrices. Rectangular and
rank-deficient inputs remain supported by the stable core algorithm but do
not yet have a Kannan--Bachem complexity wrapper.

Formal claims are Lean kernel theorems. Native wall time and RSS are
observational only. The profile forbids project axioms, `sorryAx`, and
native/compiler trust and has no FLINT dependency.

These files are local release materials. They do not create a GitHub release,
tag, DOI, deposition, or upstream pull request.
