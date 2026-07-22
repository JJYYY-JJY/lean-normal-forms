# Binary bit-cost research API 0.1.0 and current additive surface

The independent facade is imported explicitly:

```lean
import NormalForms.Research.BitCost
```

It is not re-exported by `NormalForms`. This keeps the stable normal-form API
separate from the experimental complexity model.

## Claim levels

`AcceptanceTier` fixes four names that must not be conflated:

1. `semanticCorrectness`: the returned value satisfies its mathematical
   specification;
2. `ringOperationCount`: abstract ring operations have been counted;
3. `coefficientBitLength`: every intermediate coefficient has a proved width
   bound;
4. `bitComplexity`: concrete binary primitives have explicit operation
   bounds.

The facade supplies the fourth tier for integer addition, multiplication,
Euclidean division, and extended gcd. The current additive surface also has a
sign-normalized extended gcd that reduces coefficients after every recursive
update. It remains a primitive reference model; the separate
`NormalForms.Research.KannanBachem` facade composes it into a theorem for the
principal HNF kernel after verified row preparation. The same facade uses
these primitives in a cached Bird recurrence, proves its closed arithmetic
cost and equality with `Matrix.det`, and uses its value projection for every
minor inspected by preparation. The recursive scan and principal-kernel costs
compose into a closed nonsingular square HNF bound. No Kannan--Bachem SNF
bit-complexity claim is made yet.

## Representation and result carriers

```lean
SignMagnitude
SignMagnitude.value
SignMagnitude.ofInt
SignMagnitude.bitLength
SignMagnitude.magnitude

WithCost α
DivModResult
XGCDResult
```

`SignMagnitude` is an abbreviation for mathlib's inductive `ZNum`: zero is a
dedicated constructor and nonzero values carry a canonical positive binary
word plus a sign. `value` interprets a word as `Int`; `ofInt` is its inverse.
`bitLength` is the width of the unsigned magnitude and is zero exactly at
zero.

`WithCost` pairs a computed value with the exact count assigned by this
reference model. A count is meaningful only together with the matching
implementation and its `cost_le` theorem.

## Costed primitives

| Primitive | Semantic theorem | Width theorem | Cost theorem |
| --- | --- | --- | --- |
| `addWithCost` | `addWithCost_value` | `addWithCost_value_bitLength_le` | `addWithCost_cost_le` |
| `mulWithCost` | `mulWithCost_value` | `mulWithCost_value_bitLength_le` | `mulWithCost_cost_le` |
| `divModWithCost` | `divModWithCost_quotient_value`, `divModWithCost_remainder_value` | quotient/remainder `*_bitLength_le` | `divModWithCost_cost_le` |
| `xgcdWithCost` | `xgcdWithCost_spec`, `*_gcd_value`, `*_bezout` | `xgcdWithCost_coefficient_bitLength_le` | `xgcdWithCost_cost_le` |
| `boundedXGCDWithCost` | `boundedXGCDWithCost_spec` | `boundedXGCDWithCost_coefficient_natAbs_le`, recursive `*_bitLength_le` | `boundedXGCDWithCost_cost_le`, `*_cost_le_uniform` |

The public primitive budgets are:

```lean
addBitOperationBound
mulBitOperationBound
divModBitOperationBound
xgcdCoefficientBitBound
xgcdBitOperationBound
```

If the two input widths are `l` and `r`, addition is bounded by
`1 + 2 * (l + r + 1)^2`. Schoolbook multiplication scans the right operand
and is bounded by `1 + r * (1 + (2*l + r + 2)^2)`. Signed division uses one
shared binary long-division pass and has a bilinear bound plus linear sign
normalization work.

## Division convention

`divModWithCost numerator divisor` agrees exactly with Lean's integer `/` and
`%`, including negative inputs and the zero-divisor convention. For a
nonzero divisor, its remainder has no more bits than the divisor and its
unsigned magnitude is strictly smaller:

```lean
divModWithCost_remainder_bitLength_le
divModWithCost_remainder_measure_lt
```

The strict measure theorem drives the well-founded extended-gcd recursion.
Quotient and remainder are produced by the same modeled pass; the API does
not charge two independent divisions.

## Extended gcd

```lean
xgcdWithCost left right : WithCost XGCDResult
```

The result contains a nonnegative normalized gcd and two signed
coefficients. `xgcdWithCost_spec` proves both equality with `Int.gcd` and the
Bézout equation over the original signed inputs.

`xgcdCoefficientBitBound` follows the Euclidean quotient path and bounds both
coefficients at every recursive return. `xgcdBitOperationBound` composes the
division, multiplication, and addition budgets using that independent width
bound. It does not inspect the coefficients computed by `xgcdWithCost` to
manufacture an after-the-fact budget.

For polynomial iteration accounting, use `boundedXGCDWithCost`. It first
normalizes both operands to nonnegative magnitudes, applies the Appendix
Bézout-coefficient reduction at every recursive level, and restores input
signs on the final coefficients. `euclideanIterations_le_bitLengths` proves
at most `size(left) + size(right) + 1` divisions. The recursive coefficient
width and per-step schoolbook charges then yield
`boundedXGCDWithCost_cost_le`; `boundedXGCDWithCost_cost_le_uniform` is the
uniform-width form used by matrix algorithms.

## Stability and trust

`NormalForms/Tests/Research/BitCost/PublicApi.lean` currently freezes 87
declarations. Internal recursive counters and helper lemmas are implementation
details even when their modules expose them for proof composition. The pinned
0.1.0 artifact remains a historical 49-declaration snapshot.

The executable definitions have no noncomputable branch. The separate
34-root proof audit observes `propext`, `Quot.sound`, and
`Classical.choice`, inherited through the mathlib `ZNum`/`Nat.size` semantic
bridge. It rejects project axioms, `sorryAx`, and compiler/native trust.

Native execution is regression evidence only. Formal complexity claims are
the kernel-checked semantic, width, and `cost_le` theorems. The archived 0.1.0
paper, image, and raw benchmark remain under `artifact/bit-cost`; they are not
silently rewritten to describe the current additive surface. Run the current
code verifier with:

```sh
scripts/verify.sh bit-cost
```

Run `scripts/bench.py bit-cost` for fresh timing in `build/benchmarks/`.
