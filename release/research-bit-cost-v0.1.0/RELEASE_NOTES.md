# lean-normal-forms research/bit-cost 0.1.0

Research version 0.1.0 establishes a verified binary reference model for the
integer primitives needed by later normal-form complexity proofs. It is an
independent profile on top of lean-normal-forms 1.2.2 and does not enlarge the
frozen core facade.

## Verified model

- `SignMagnitude` exposes mathlib's canonical inductive `ZNum` encoding and
  proves round trips with `Int`.
- `addWithCost` mirrors binary carry and borrow propagation.
- `mulWithCost` mirrors schoolbook shift-and-add multiplication.
- `divModWithCost` computes the signed Euclidean quotient and remainder in
  one shared binary long-division pass.
- `xgcdWithCost` is a well-founded Euclidean recursion that returns a
  normalized gcd and signed Bézout coefficients.
- Every primitive has value-correctness, output-width, and exact-cost versus
  explicit-budget theorems.
- Extended gcd has a path-sensitive coefficient-width budget and a composed
  bit-operation budget driven only by the Euclidean quotient path.

## Reproducibility

- The research facade freeze checks 49 declarations.
- The axiom audit covers 21 proof roots and observes exactly `propext`,
  `Quot.sound`, and `Classical.choice`.
- The native executable validates 13 signed and edge cases.
- The fixed-host JSON/CSV profile records one warmup and seven measurements,
  complete deterministic case data, median/IQR, RSS, and
  source/binary/hardware fingerprints.
- `scripts/verify.sh bit-cost` rebuilds the facade, runs the whole default
  test suite, checks facade isolation, audits axioms, reruns the deterministic
  corpus, and validates the committed benchmark. Fresh timing and publication
  builds remain separate operations.

## Scope and trust

This profile proves bit-operation bounds for primitive binary integer
arithmetic and extended gcd. It does not claim the operation count,
coefficient growth, or bit complexity of HNF, SNF, Kannan--Bachem, modular
HNF, or LLL.

The executable definitions contain no noncomputable branch. The semantic
proof bridge through mathlib's `ZNum` and `Nat.size` theorems accounts for the
registered three-axiom allowlist. Native wall time is observational only;
theorems are checked by Lean's kernel.

These files prepare local release materials. They do not create a GitHub
release, tag, DOI, deposition, or upstream pull request.
