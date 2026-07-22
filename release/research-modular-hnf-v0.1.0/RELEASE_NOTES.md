# lean-normal-forms research/modular-hnf 0.1.0

Research version 0.1.0 completes the independently gated modular-HNF line. It
is additive on top of lean-normal-forms 1.2.2 and leaves the stable core facade
unchanged.

## Verified algorithm

- Distinct determinant-modulus and elementary-divisor contracts prevent a
  modulus valid for one algorithm from entering the other.
- The pure full-column-rank DKT value kernel returns its candidate, modulus
  schedule, and six-class operation telemetry.
- An augmented-row-lattice invariant and fixed-shape uniqueness theorem prove
  that every legal candidate is the canonical core HNF.
- `modularHNFFullRank` returns the existing strong `HNFResultFin`, including
  an explicit inverse and both inverse identities.
- A checked fraction-free rank profile lifts the result across pivot gaps,
  rectangular inputs, rank deficiency, rank zero, and empty dimensions.
- Exhaustive finite profile search is proved complete and uses only integer
  candidate data at runtime.

## Complexity evidence

- Every raw run has a closed dimension-only scalar-operation bound.
- Explicit prefix envelopes bound all stored intermediate matrices, and legal
  final entries are bounded sharply by the determinant modulus.
- A costed mirror follows the actual `Nat.xgcdAux` path behind
  `Int.gcdA`/`Int.gcdB` and is proved value-equal to the executable XGCD.
- The six telemetry classes are priced in the shared schoolbook binary model,
  yielding a closed bit-operation budget for the modular value kernel.
- The transform fields are recovered only after canonical equality; their
  construction cost is explicitly outside this profile's modular cost claim.

## Reproducibility

- The research facade freeze contains 157 checked entries.
- The JSON axiom audit covers 43 theorem roots and observes exactly
  `Classical.choice`, `Quot.sound`, and `propext`.
- Three deterministic native cases cover scalar, tall, and square
  determinant-modulus runs.
- Four benchmark stages retain one warmup and seven raw observations each,
  including timing, RSS, exact telemetry, coefficient widths, modeled-cost
  widths, and full source/binary/hardware fingerprints.
- `scripts/verify.sh modular-hnf` rebuilds the profile, re-elaborates every
  execution guard, runs the full test suite, validates committed evidence,
  and audits axioms. Fresh timing and publication builds remain separate
  operations.

## Scope and trust

Kernel theorems establish correctness and formal bounds. Native timing is
observational only. FLINT is neither linked nor trusted. The automatic rank
profile is complete but exhaustive. Primitive modular transform tracing and
its bit cost remain outside version 0.1.0; the returned strong transform is
the stable core transform transported after proved matrix equality.

These are local release materials. They do not create a GitHub release, tag,
DOI, deposition, or upstream pull request.
