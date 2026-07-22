# Kannan--Bachem research API

Research version: 0.1.0.

Import the independent research facade explicitly:

```lean
import NormalForms.Research.KannanBachem
```

It is not re-exported by `NormalForms` and does not alter the frozen core API.

## Nonsingular square HNF

`principalRun` executes the row-oriented transpose of the column-HNF schedule
in [Kannan--Bachem, Algorithm HNF](https://doi.org/10.1137/0208040), with primitive
row operations and directly accumulated transforms and inverses. For every
nonsingular square integer input, `principalHermiteNormalForm` returns the
existing strong `HNFResultFin` type.

The coefficient and bit-operation bounds use:

```lean
Principal.PrincipalReady A
```

which states that every canonical leading principal submatrix of `A` has
nonzero determinant.

## Certified preparation

`Principal.prepare A hdet` removes that caller obligation. It recursively
examines complementary last-column minors, chooses the least row with nonzero
minor, and places that row last. The resulting permutation is deterministic.
`Principal.lastColumnScan` is the charged left-to-right implementation: every
candidate uses `DivisionFreeDeterminant.evaluateWithCost`, and the scan adds
one structural zero-test charge per inspected row.

```lean
Principal.Preparation.rowPermutation
Principal.Preparation.matrix
Principal.Preparation.transform
Principal.Preparation.transformCertificate
Principal.Preparation.ready
Principal.Preparation.equation
```

The transform is the corresponding permutation matrix. Its inverse is the
inverse permutation matrix, with both multiplication identities proved
directly. `Principal.preparedPrincipalHermiteNormalForm A hdet` runs the
principal kernel on the prepared matrix and composes this inverse certificate
back to the original input. Its output is proved equal to the canonical
semantic reference HNF.

The zero-dimensional case and a nonsingular matrix with zero initial leading
entry are executable regressions. The latter forces an actual row swap and
checks the transform equation and both inverse identities.

## Total square SNF semantics

The SNF namespace implements the row-HNF transpose of
[Kannan--Bachem Steps 4--7](https://doi.org/10.1137/0208040) on a nonsingular
square active block:

```lean
Smith.leftHermitePhase
Smith.rightHermitePhase
Smith.pass
Smith.injectLowerWitness
Smith.clearDivisibleFirstColumn
Smith.stabilize
Smith.smith
Smith.stabilize?
Smith.smith?
```

`leftHermitePhase` applies the verified one-column LHNF multiplier to the
entire block. `rightHermitePhase` applies the prepared principal-minor HNF to
the transpose and transports its multiplier back as a right transform. Every
`pass` therefore carries the existing `TwoSidedCertificate`, including both
explicit inverses.

The executable searches use `ComputableEuclideanOps.isZeroB` and `dvdB`.
When all below-pivot entries are divisible, `clearDivisibleFirstColumn` clears
them with one lower shear and stores the negated shear as an explicit inverse.
Otherwise, or after Step 7 injects an offending lower-right entry, the next
full pass produces a pivot dividing both the old pivot and that witness. The
formal theorems `pass_pivot_natAbs_lt_of_not_dvd_entry` and
`pass_pivot_natSize_lt_of_not_dvd_entry` make the resulting strict magnitude
and binary-length decrease explicit.

`stabilize` uses that decrease as its well-founded recursion measure and
returns a `Stabilization` for every nonsingular positive-dimensional square
matrix. The result proves a normalized nonzero pivot, both cleared borders,
divisibility of the lower block, the full transform equation, and inverse
recovery. `stabilize_passes_le_inputBitLength` bounds the number of passes by
one more than the input coefficient width.

`smith A hdet` structurally recurses through lower-right blocks and directly
returns the frozen `SNFResultFin A`. `smith_sound` exposes its equation,
inverse equation, and Smith predicate; `smith_eq_reference` proves equality
with the canonical core Smith matrix. The older `stabilize?` and `smith?`
entries remain available for bounded execution diagnostics, where fuel
exhaustion is visible as `none`. Neither path falls back to the generic Smith
kernel.

`SmithOperationCount` separately records scalar additions, multiplications,
XGCD calls, normalizations, and exact divisions. `smithOperationCount` mirrors
the total dimension recursion. Determinant magnitude is preserved by every
two-sided certificate and cannot increase in a stable lower-right block, so
`smithOperationCount_total_le_polynomial` bounds the complete count by an
explicit polynomial in dimension and the original coefficient width.

Step 4 now uses `boundedColumnTrace`, a dedicated bounded-XGCD one-column
reducer with exactly one pair step per lower row and one final normalization.
Its forward and inverse prefixes, transformed matrices, and arithmetic
operands have separate closed bit-length bounds. The full stabilization proof
then bounds every pass, divisible-column shear, Step-7 injection, and
certificate composition.

`smith_coefficientProfile_le_polynomial` lifts those bounds through the outer
lower-right recursion. It simultaneously bounds `S`, `U`, `U⁻¹`, `V`, and
`V⁻¹` in the original dimension and coefficient width.

`smithBitOperationCost` mirrors the same outer recursion, while
`stabilizeFromBitOperationCost` follows both pivot-descent branches. The model
charges the actual bounded-XGCD trace, exact reference division, row and
column scalar arithmetic, prepared principal HNF, and the four dense matrix
products that compose `U`, `U⁻¹`, `V`, and `V⁻¹`.
`matrixProductWithCost_value` proves the costed sign-magnitude dense product
equals standard `Matrix.mul` entrywise. The endpoint is:

```lean
smithBitOperationCost_le_polynomial
  (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
  smithBitOperationCost A hdet ≤
    smithPolynomialBitOperationBound n (matrixBitLength A)
```

This closes all four tiers for nonsingular square inputs. Rectangular and
rank-deficient wrappers remain subsequent work.

## Complexity boundary

The principal kernel has:

- at most `n ^ 3` primitive row steps;
- closed bit-length bounds for all matrices, arithmetic operands, forward
  multiplier prefixes, and inverse prefixes under `PrincipalReady`;
- exact reference charges for bounded XGCD and Euclidean division, plus
  schoolbook scalar row arithmetic.

`preparedPrincipalKernelBitOperationCost_le` applies that bound to every
nonsingular square input and states it using the original matrix bit width.
It charges only the principal run after preparation.

`DivisionFreeDeterminant.evaluateWithCost` is the certified determinant
program used by preparation. It implements the matrix recurrence in
[Bird (2011), p. 1072](https://doi.org/10.1016/j.ipl.2011.08.006), stores each
stage in nested `Vector`s,
executes all scalar arithmetic through the verified binary sign-magnitude
addition and multiplication primitives, and returns their exact modeled cost.
The following layers are already proved over the same implementation:

- dense-vector stages decode to the algebraic Bird matrix recurrence;
- recurrence heights and bit lengths have closed polynomial envelopes;
- every scalar entry, full stage, iteration prefix, and final result satisfies
  the public `determinantBitOperationBound`;
- a dimension-generic bordered-minor invariant proves
  `matrixBirdDet A = A.det`, and the cached and charged evaluators inherit that
  equality.

`evaluateWithCost_value_eq_det` is the trusted semantic endpoint.
`Principal.preparationDeterminantScanBitOperationCost` sums the actual scans
along the recursive permutation, and
`preparationDeterminantScanBitOperationCost_le` bounds it in the original
input width. `preparedPrincipalHNFBitOperationCost_le` then composes that
charge with the ready principal kernel under the closed public
`preparedPrincipalHNFBitOperationBound`.

The HNF model charges all specified binary scalar arithmetic plus one
structural zero test per inspected determinant. It is not a wall-clock or
allocation model. The SNF bit-operation model composes those charges with
Step 4, clearing, injection, and dense certificate multiplication. Search
comparisons, allocation, and wall time remain outside the arithmetic model.

The compile-time freeze contains 572 public checks. The axiom audit covers
263 theorem roots and permits only `propext`, `Quot.sound`, and
`Classical.choice`; project axioms, `sorryAx`, and native/compiler trust are
forbidden.

## Reproducibility profile

`scripts/verify.sh kannan-bachem` rebuilds the facade and tests, directly
re-elaborates the execution guards, runs the exact axiom audit, validates
three deterministic native cases, and checks the committed four-stage
baseline. Run `scripts/bench.py kannan-bachem` for fresh timing. The pinned
software profile is documented in `artifact/kannan-bachem`.

The committed JSON/CSV baseline records prepared 3-by-3 HNF, repeated-pass
2-by-2 SNF, and Step-7-injection 2-by-2 SNF. Deterministic fields include the
operation classes, pass/injection counts, all five certificate widths, exact
modeled bit cost, and the proved bound. Native wall time and RSS are
observational and never replace the formal theorems.
