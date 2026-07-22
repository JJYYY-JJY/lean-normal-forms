# Modular-HNF research API

Research version: 0.1.0

Core package compatibility: 1.2.2

Lean/mathlib: 4.32.0

Import the independent facade with:

```lean
import NormalForms.Research.ModularHNF
```

The stable `NormalForms` facade does not import this module.

## Contracts

```lean
selectedSquareMinor
FullColumnRankWitness
DeterminantModulusWitness
largestElementaryDivisor
ElementaryDivisorModulusWitness
ModulusWitness
```

`DeterminantModulusWitness` records a positive modulus divisible by the
absolute determinant of one explicitly nonsingular selected square minor.
The value kernel follows the modulo-determinant algorithm class of
[Domich--Kannan--Trotter](https://doi.org/10.1287/moor.12.1.50) and accepts this
contract. `ElementaryDivisorModulusWitness`
is intentionally distinct and is not accepted by that entry point.

## Raw value kernel

```lean
ModularOperationCount
ModularStageEvent
RawModularRun
runRaw
runWithDeterminantWitness
```

`runRaw` is total for an arbitrary modulus but returns only a candidate and
telemetry. Trusted mathematical conclusions require a typed witness and the
soundness theorems. `ModularOperationCount` separates additions,
multiplications, XGCD calls, exact divisions, modular reductions, and
comparisons.

## Semantics and strong full-rank result

```lean
rowSpan
suffixModule
augmentedRowSpan
RowsCongruentOnSuffix
fullColumnShape_unique_of_rowSpan_eq
runWithDeterminantWitness_candidate_eq_reference
modularHNFFullRank
modularHNFFullRank_eq_reference
modularHNFFullRank_inverse_equation
```

`modularHNFFullRank` returns the existing core `HNFResultFin A`, including the
chosen inverse and both inverse identities. Its `H` field is the modular
candidate. Transform fields are transported from the stable core after the
candidate/reference equality theorem; no second result type is introduced.

## General-rank wrapper

```lean
FractionFreeRankProfile
RankProfileSelection
RankProfileSelection.IsValid
searchRankProfile?
searchRankProfile_valid
fractionFreeRankProfile
integerHermiteNormalFormModularWithProfile
integerHermiteNormalFormModular
integerHermiteNormalFormModular_eq_reference
```

The profile stores integer Cramer numerators and a selected nonzero minor. Its
column identities and lexicographic zero-support law lift the selected-column
modular result to the full rectangular input. The total executable search
enumerates finite candidates and checks all integer obligations. Rational
linear algebra occurs only in the erased completeness proof.

## Operation and coefficient bounds

```lean
modularStageOperationBound
modularOperationBound
runRaw_operations_total_le
runWithDeterminantWitness_operations_total_le
integerBitLength
matrixHeight
matrixBitLength
EntriesBounded
coefficientGrowth
coefficientSteps
runRawPrefix
modularIntermediateHeightBound
runRawPrefix_matrixHeight_le
runRaw_matrixHeight_le_intermediateBound
runWithDeterminantWitness_entry_natAbs_le
runWithDeterminantWitness_matrixHeight_le
```

For `m` rows and `n` columns, every raw run has at most

```text
n * (12 * m * n + 5 * m + 3 * n + 4)
```

counted scalar operations. The intermediate envelope iterates
`B ↦ B + B * B` through at most `m * n` row updates. A legal final candidate
has every entry bounded by the modulus magnitude.

## Exact standard-XGCD mirror

The namespace `StandardXGCD` exposes:

```lean
natAuxWithCost
natAuxWithCost_value
natAuxWithCost_coefficient_natAbs_le
natAuxWithCost_cost_le_closed
standardIntXGCDWithCost
standardIntXGCDWithCost_value
standardIntXGCDWithCost_coefficient_natAbs_le_uniform
standardIntXGCDUniformBitOperationBound
standardIntXGCDWithCost_cost_le_uniform
```

The mirror follows the `Nat.xgcdAux` remainder and coefficient updates used by
`Int.gcdA`/`Int.gcdB`. Its value theorem is equality with the actual
`ComputableEuclideanOps.xgcd` instance.

## Bit-operation budget

```lean
modularWorkingBitWidth
modularComparisonCostForBitLength
modularScalarBitOperationCharge
ModularOperationCount.bitOperationCost
ModularOperationCount.bitOperationCost_le_total_mul_charge
modularKernelHeightBound
modularKernelBitOperationBound
runRaw_bitOperationCost_le
runWithDeterminantWitness_bitOperationCost_le
```

This schoolbook sign-magnitude budget prices the exact value-kernel telemetry.
It does not include construction of the strong transform matrices recovered
after canonical equality.

## Reproduction

```sh
scripts/verify.sh modular-hnf
```

The verifier compiles the 157-entry manifest at
`NormalForms/Tests/Research/ModularHNF/PublicApi.lean`, audits 43 theorem roots,
runs deterministic execution guards, validates the one-warmup/seven-run
JSON/CSV baseline, and leaves fresh measurement to
`scripts/bench.py modular-hnf`.
