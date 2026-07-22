# Exact integer LLL research API

Research version: 0.1.0

Core package compatibility: 1.2.2

Lean/mathlib: 4.32.0

Executable backend: [HexLLL at `a73f188`](https://github.com/leanprover/hex-lll/tree/a73f188bbd7ea48c4a1bb1e6d608b4f131026512)

Proof backend: [HexLLLMathlib at `c10d668`](https://github.com/leanprover/hex-lll-mathlib/tree/c10d6681dee9a4f963c1035bcbe34fc3eb60a769)

Import the independent facade with:

```lean
import NormalForms.Research.LLL
```

The stable `NormalForms` facade does not import this module. Recursive state,
rank-profile proofs, prefix lifts, and operation replay remain outside the
research facade.

## Convention and predicate

Rows are lattice vectors. The fixed parameters are:

```lean
delta : Rat  -- 3 / 4
eta   : Rat  -- 1 / 2
```

They specialize the reducedness conditions in the
[original LLL paper](https://doi.org/10.1007/BF01457454).

The exact predicate is split into:

```lean
HasPositiveGramSchmidtLengths B
IsSizeReduced B
SatisfiesLovasz B
IsLLLReduced B
isLLLReducedB B
isLLLReducedB_sound B
```

`IsLLLReduced` uses exact rational Gram--Schmidt data. It contains no floating
point comparison. `isLLLReducedB` is the executable checker, and its soundness
theorem promotes Boolean acceptance to the proposition.

## Strong full-row-rank entry

```lean
FullRowRankWitness B
FullRankLLLResult B
fullRankLLLPositive B rowsPositive fullRank
```

The result stores:

```lean
U            : Matrix (Fin m) (Fin m) Int
U_cert       : MatrixInverseCertificate U
reducedBasis : Matrix (Fin m) (Fin n) Int
equation     : U * B = reducedBasis
reduced      : IsLLLReduced reducedBasis
```

The chosen inverse is accumulated from every elementary row step. Neither
`Matrix.inv`, determinants, `nonsing_inv`, nor a choice-based inverse recovery
appears on the algorithm path.

The terminating value reducer comes from the pinned HexLLL source, while the
reducedness and fuel-sufficiency theorems come from pinned HexLLLMathlib.
`toDense` and `ofDense` are the representation boundary, with
proved round trips and row-add/swap compatibility. The local trace follows the
same dense control flow and accumulates the project certificate.

## Total row and column entries

```lean
LLLResult B
integerLLL B

ColumnLLLResult B
integerColumnLLL B
```

`integerLLL` accepts all dimensions and ranks. It first computes a strong HNF
rank decomposition, whose nonzero prefix is proved independent and whose tail
is literally zero. The full-rank LLL transform is lifted block-diagonally and
composed with the HNF transform. The result contains:

- the exact rank and `rank <= rows`;
- `U`, its explicit inverse certificate, and `U * B = reducedBasis`;
- `IsLLLReduced` for `rowPrefix rank_le_rows reducedBasis`;
- a proof that every later row is zero.

`integerColumnLLL` is only the transpose adapter. It returns `V`, its explicit
inverse, `B * V = reducedBasis`, reduced transposed rows, and a zero column
tail. There is no independent column algorithm or second convention.

## Profile and four evidence layers

```lean
FullRankLLLProfile B
fullRankLLLProfilePositive B rowsPositive fullRank
```

The profile contains the same strong result plus:

```lean
fuel
fuel_eq
operations
operation_bound
intermediateCoefficientHeight
result_height_le
```

The fuel is exactly the verified Hex termination fuel. A successful size
reduction records one row event and one dense-state refresh; an adjacent swap
does the same. One outer transition visits at most `m` earlier rows and swaps
at most once, giving:

```text
operations.total <= fuel * (2 * m + 2)
```

The trace updates `intermediateCoefficientHeight` at every row mutation. It
covers all transformed basis entries and each actual nearest-quotient row
multiplier; `result_bitLength_le` proves that the returned basis fits the
recorded width.

The cost API is:

```lean
lllWorkingBitWidth
lllScalarBitOperationCharge
lllScalarPositionsPerEvent
LLLOperationCount.bitOperationCost
lllKernelBitOperationBound
FullRankLLLProfile.bitOperationCost_le
```

`PrimitiveCost` proves that the shared sign-magnitude `addWithCost`,
`mulWithCost`, and `divModWithCost` calls fit the common scalar charge at the
stated working width. The composed theorem bounds the specified reference
price by the tracked-event fuel bound.

This fourth layer is an a-posteriori, profile-dependent reference bound. It is
not an input-only polynomial complexity theorem. It does not price the HNF
rank decomposition, accumulated transform-matrix products, Lean allocation,
or compiler/runtime implementation. Native time is reported separately.

## Diagnostics

The bounded exploratory reducer is intentionally outside the stable research
facade:

```lean
import NormalForms.Research.LLL.Diagnostics

fullRankLLLWithFuel B fuel
fullRankLLLWithFuel? B fuel
```

Fuel exhaustion remains observable and cannot manufacture a strong result.
This diagnostic implementation is useful for transition experiments but is
not the total verified backend.

## Reproduction

```sh
scripts/verify.sh lll
```

The verifier compiles the 114-entry manifest at
`NormalForms/Tests/Research/LLL/PublicApi.lean`, audits 20 theorem roots, runs
the exact facade-isolation harness and deterministic native corpus, validates
the one-warmup/seven-run JSON/CSV baseline, and leaves fresh measurement to
`scripts/bench.py lll`.
