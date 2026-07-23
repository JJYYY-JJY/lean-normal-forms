# Kannan--Bachem research API

Research version: 0.2.0-dev.

```lean
import NormalForms.Research.KannanBachem
```

This opt-in research facade covers nonsingular square integer matrices. It
does not add rectangular, rank-deficient, modular, LLL, FLINT, or checked
wrapper APIs.

## Value-producing execution

`smithExecution A hdet` is the single instrumented dimension recursion. It
returns the Smith result and a flat list of arithmetic leaves. Its result
contains `S`, `U`, `U⁻¹`, `V`, and `V⁻¹`; the public closure theorems include:

```lean
smithExecution_value
smithExecution_replay
smithExecution_trace_wellFormed
smithExecution_chargeComplete
smithWithCost_cost_eq_traceBitCost
smithOperationCount_eq_traceOperationCount
```

The execution branches on costed zero, magnitude, division, and divisibility
runs. HNF preparation executes each determinant scan once. Certificate
composition executes four dense products. Composite steps only concatenate
their child charge lists.

`KannanBachemArithmeticCharge` is constructed through smart constructors.
Every leaf stores its operands and primitive run together with a proposition
that the stored run is the named primitive. Bounded XGCD is one opaque macro
leaf for the entire `boundedBezoutBlockWithCost` run: one bounded XGCD, one
gcd zero-test, and, in the nonzero branch, two exact divisions. Its internal
arithmetic is included in its bit cost and is not duplicated by descendant
charges.

`ArithmeticOperationCount` is derived from the same flat list:

```lean
additions
multiplications
xgcdCalls
normalizations
standaloneDivModCalls
```

Zero tests and magnitude comparisons contribute to bit cost but not to this
macro total.

## Concrete binary encoding

Integers use a canonical sign/magnitude payload and pair framing. Packed
matrix and five-matrix Smith decoders are prefix decoders and preserve an
arbitrary suffix:

```lean
decodePackedMatrixPrefix_encode_append
decodePackedSmithOutputPrefix_encode_append
```

The exact symbol-count equalities are:

```lean
matrixEncodingLength packed = 2 * matrixBinarySize packed + 2
smithOutputEncodingLength result = 2 * smithOutputBinarySize result + 2
```

These lengths count symbols in the abstract binary alphabet. They do not
describe the memory footprint of Lean `List Bool`.

## Fixed-polynomial endpoint

The stable complexity claim is fixed-polynomial binary arithmetic cost in the
length of the concrete self-delimiting input encoding:

```lean
smithWithCost
smithExecution_cost_le_work
smithExecution_cost_le_polynomial
smithWithCost_cost_le_workBound
smithCost_polynomial_in_encodingLength
verifiedSmithPolynomialBitCost
```

`verifiedSmithPolynomialBitCost A hdet` bundles the produced result, both
transform equations, both inverse identities for each side, the Smith
predicate, canonical reference equality, the exact leaf-cost fold, and fixed
polynomial bounds for arithmetic cost and the five-matrix data encoding.

The older `smithBitOperationCost` structural recurrence and its work bounds
remain exported for source compatibility. They are not 0.2 execution-cost
endpoints.

The model excludes decoding, serialization, matrix storage, index traversal,
copying, allocation, garbage collection, Lean compiler/runtime behavior, and
wall-clock time. It makes no unqualified `PolynomialTime` claim.

## Historical 0.1.0 note

The 0.1.0 theorem remains valid for the cost function defined in that release.
That instrumentation omitted some control-flow and certificate-construction
arithmetic, and its release notes described the link to executable computation
too strongly. The committed v1 measurements remain historical v1
instrumentation. Version 0.2.0-dev uses the expanded leaf model aligned with
the value-producing execution; it does not claim that the 0.1.0 theorem was
false.

## Verification profile

```sh
scripts/verify.sh kannan-bachem
scripts/bench.py kannan-bachem
```

The benchmark schema is `normalforms.kannan-bachem-benchmark/v2` and the
profile is `research-kannan-bachem-v0.2.0-dev`. Native timing and RSS are
observational only. The profile source identity is computed from
`artifact/kannan-bachem/source-manifest.txt`.
