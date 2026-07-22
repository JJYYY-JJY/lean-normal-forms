/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.Primitive

/-!
# Algebraic Operation Bound for Primitive-Traced Integer HNF

This layer expands every row update into scalar additions and
multiplications. Extended gcd and normalization remain separately counted
Euclidean primitives; their bit-level implementation cost belongs to the later
bit-complexity layer. Row swaps, comparisons, and data movement are not ring
operations in this model.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

/-- Algebraic work represented by a row trace on a matrix with fixed width. -/
public structure RingOperationCount where
  additions : Nat := 0
  multiplications : Nat := 0
  xgcdCalls : Nat := 0
  normalizations : Nat := 0
  deriving DecidableEq, Repr

namespace RingOperationCount

/-- Sum of scalar ring work and separately counted Euclidean primitives. -/
@[expose] public def total (count : RingOperationCount) : Nat :=
  count.additions + count.multiplications +
    count.xgcdCalls + count.normalizations

/--
Expand the exact row-step classes into scalar algebraic work for `columns`
matrix entries per affected row.
-/
@[expose] public def ofTrace {m : Nat}
    (columns : Nat) (trace : RowTrace Int m) : RingOperationCount :=
  let steps := trace.operationCount
  { additions := columns * (steps.additions + 2 * steps.bezoutPairs)
    multiplications :=
      columns * (steps.additions + steps.unitScales + 4 * steps.bezoutPairs)
    xgcdCalls := steps.bezoutPairs
    normalizations := steps.unitScales }

public theorem total_le_of_length {m columns limit : Nat}
    (trace : RowTrace Int m) (length_le : trace.length ≤ limit) :
    (ofTrace columns trace).total ≤
      columns * (3 * limit) + columns * (6 * limit) + 2 * limit := by
  rcases trace.operationCount_components_le_length with
    ⟨_swaps, additions, unitScales, bezoutPairs, _blocks⟩
  have additions_le := additions.trans length_le
  have unitScales_le := unitScales.trans length_le
  have bezoutPairs_le := bezoutPairs.trans length_le
  have additionTerms :
      trace.operationCount.additions +
          2 * trace.operationCount.bezoutPairs ≤
        3 * limit := by
    omega
  have multiplicationTerms :
      trace.operationCount.additions + trace.operationCount.unitScales +
          4 * trace.operationCount.bezoutPairs ≤
        6 * limit := by
    omega
  have euclideanTerms :
      trace.operationCount.bezoutPairs +
          trace.operationCount.unitScales ≤
        2 * limit := by
    omega
  have additionWork := Nat.mul_le_mul_left columns additionTerms
  have multiplicationWork := Nat.mul_le_mul_left columns multiplicationTerms
  simp only [total, ofTrace]
  omega

end RingOperationCount

/-- Closed polynomial budget for the primitive-traced HNF algebraic model. -/
@[expose] public def hermiteRingOperationBound (rows columns : Nat) : Nat :=
  let traceBound := 4 * rows * columns
  columns * (3 * traceBound) +
    columns * (6 * traceBound) + 2 * traceBound

public theorem hermiteRingOperationBound_eq (rows columns : Nat) :
    hermiteRingOperationBound rows columns =
      36 * rows * columns * columns + 8 * rows * columns := by
  simp [hermiteRingOperationBound]
  ring

/-- Exact algebraic cost extracted from the primitive HNF execution trace. -/
@[expose] public def primitiveHermiteRingOperations {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) : RingOperationCount :=
  RingOperationCount.ofTrace n (primitiveHermiteTrace A).steps

/-- Stage-two HNF ring-operation theorem. -/
public theorem primitiveHermiteRingOperations_total_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (primitiveHermiteRingOperations A).total ≤ hermiteRingOperationBound m n := by
  exact RingOperationCount.total_le_of_length
    (primitiveHermiteTrace A).steps
    (primitiveHermiteTrace_length_le A)

end NormalForms.Research.KannanBachem.Hermite
