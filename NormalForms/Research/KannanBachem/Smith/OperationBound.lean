/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.Totality
public import NormalForms.Research.KannanBachem.Hermite.PrincipalOperationBound
import all NormalForms.Research.KannanBachem.Smith.BoundedColumn

/-!
# Ring-operation Accounting for Kannan--Bachem SNF

This layer uses the same algebraic convention as the HNF operation theorem:
scalar additions and multiplications are counted, while extended gcd,
normalization, and exact division are recorded as separate Euclidean
primitives. Comparisons, searches, permutations, and data movement are not
ring operations. Determinant-selection arithmetic is charged later by the
bit-complexity layer, exactly as for prepared HNF.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms.Research.KannanBachem.Hermite

/-- Algebraic and Euclidean primitive counts for the Smith schedule. -/
public structure SmithOperationCount where
  additions : Nat := 0
  multiplications : Nat := 0
  xgcdCalls : Nat := 0
  normalizations : Nat := 0
  divModCalls : Nat := 0
  deriving DecidableEq, Repr

namespace SmithOperationCount

@[expose] public def total (count : SmithOperationCount) : Nat :=
  count.additions + count.multiplications + count.xgcdCalls +
    count.normalizations + count.divModCalls

@[expose] public def add (left right : SmithOperationCount) :
    SmithOperationCount :=
  { additions := left.additions + right.additions
    multiplications := left.multiplications + right.multiplications
    xgcdCalls := left.xgcdCalls + right.xgcdCalls
    normalizations := left.normalizations + right.normalizations
    divModCalls := left.divModCalls + right.divModCalls }

@[simp] public theorem total_add (left right : SmithOperationCount) :
    (left.add right).total = left.total + right.total := by
  cases left
  cases right
  simp [total, add]
  omega

/-- Embed the exact HNF trace accounting into the Smith accounting type. -/
@[expose] public def ofHermite (count : RingOperationCount) :
    SmithOperationCount :=
  { additions := count.additions
    multiplications := count.multiplications
    xgcdCalls := count.xgcdCalls
    normalizations := count.normalizations }

@[simp] public theorem total_ofHermite (count : RingOperationCount) :
    (ofHermite count).total = count.total := by
  cases count
  rfl

end SmithOperationCount

/-- Exact row arithmetic charged for the simultaneous divisible-column shear. -/
@[expose] public def clearColumnOperationCount (dimension : Nat) :
    SmithOperationCount :=
  let rows := dimension - 1
  { additions := rows * dimension
    multiplications := rows * dimension
    divModCalls := rows }

/-- Exact column-add arithmetic charged for one Step-7 injection. -/
@[expose] public def injectionOperationCount (dimension : Nat) :
    SmithOperationCount :=
  { additions := dimension
    multiplications := dimension }

@[simp] public theorem clearColumnOperationCount_total (dimension : Nat) :
    (clearColumnOperationCount dimension).total =
      2 * (dimension - 1) * dimension + (dimension - 1) := by
  simp [clearColumnOperationCount, SmithOperationCount.total]
  ring

@[simp] public theorem injectionOperationCount_total (dimension : Nat) :
    (injectionOperationCount dimension).total = 2 * dimension := by
  simp [injectionOperationCount, SmithOperationCount.total]
  omega

public theorem clearColumnOperationCount_total_mono {smaller larger : Nat}
    (hle : smaller ≤ larger) :
    (clearColumnOperationCount smaller).total ≤
      (clearColumnOperationCount larger).total := by
  rw [clearColumnOperationCount_total, clearColumnOperationCount_total]
  gcongr

public theorem injectionOperationCount_total_mono {smaller larger : Nat}
    (hle : smaller ≤ larger) :
    (injectionOperationCount smaller).total ≤
      (injectionOperationCount larger).total := by
  rw [injectionOperationCount_total, injectionOperationCount_total]
  omega

/-- Exact Step-4 trace cost when its row multiplier is applied to the full block. -/
@[expose] public def leftPhaseOperationCount {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    SmithOperationCount :=
  SmithOperationCount.ofHermite <|
    RingOperationCount.ofTrace (n + 1)
      (boundedColumnTrace A)

/-- Exact prepared principal-HNF trace cost used by Step 5. -/
@[expose] public def rightPhaseOperationCount {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) : SmithOperationCount :=
  let prepared := Principal.prepare A.transpose (by simpa using hdet)
  SmithOperationCount.ofHermite (principalRingOperations prepared.matrix)

/-- Exact algebraic charge of one full Step-4/Step-5 pass. -/
@[expose] public def passOperationCount {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) : SmithOperationCount :=
  (leftPhaseOperationCount A).add <|
    rightPhaseOperationCount (leftHermitePhase A).result
      (result_det_ne_zero (leftHermitePhase A) hdet)

/-- Closed full-width charge for the one-column LHNF phase. -/
@[expose] public def leftPhaseOperationBound (dimension : Nat) : Nat :=
  let traceBound := dimension
  dimension * (3 * traceBound) + dimension * (6 * traceBound) +
    2 * traceBound

/-- Closed charge for one complete Smith pass on a square block. -/
@[expose] public def passOperationBound (dimension : Nat) : Nat :=
  leftPhaseOperationBound dimension + principalRingOperationBound dimension

public theorem leftPhaseOperationBound_mono {smaller larger : Nat}
    (hle : smaller ≤ larger) :
    leftPhaseOperationBound smaller ≤ leftPhaseOperationBound larger := by
  simp only [leftPhaseOperationBound]
  gcongr

public theorem passOperationBound_mono {smaller larger : Nat}
    (hle : smaller ≤ larger) :
    passOperationBound smaller ≤ passOperationBound larger := by
  unfold passOperationBound
  apply Nat.add_le_add (leftPhaseOperationBound_mono hle)
  simp only [principalRingOperationBound]
  gcongr

public theorem leftPhaseOperationCount_total_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (leftPhaseOperationCount A).total ≤ leftPhaseOperationBound (n + 1) := by
  change
    (RingOperationCount.ofTrace (n + 1)
      (boundedColumnTrace A)).total ≤ _
  exact RingOperationCount.total_le_of_length
    (boundedColumnTrace A)
    (by rw [boundedColumnTrace_length])

public theorem rightPhaseOperationCount_total_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (rightPhaseOperationCount A hdet).total ≤
      principalRingOperationBound (n + 1) := by
  let prepared := Principal.prepare A.transpose (by simpa using hdet)
  change (principalRingOperations prepared.matrix).total ≤ _
  exact principalRingOperations_total_le prepared.matrix

public theorem passOperationCount_total_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (passOperationCount A hdet).total ≤ passOperationBound (n + 1) := by
  rw [passOperationCount, SmithOperationCount.total_add,
    passOperationBound]
  exact Nat.add_le_add (leftPhaseOperationCount_total_le A)
    (rightPhaseOperationCount_total_le (leftHermitePhase A).result
      (result_det_ne_zero (leftHermitePhase A) hdet))

/-- Uniform per-level budget, including a possible clear and Step-7 injection. -/
@[expose] public def stabilizationLevelOperationBound (dimension : Nat) : Nat :=
  passOperationBound dimension +
    (clearColumnOperationCount dimension).total +
    (injectionOperationCount dimension).total

public theorem stabilizationLevelOperationBound_mono {smaller larger : Nat}
    (hle : smaller ≤ larger) :
    stabilizationLevelOperationBound smaller ≤
      stabilizationLevelOperationBound larger := by
  unfold stabilizationLevelOperationBound
  exact Nat.add_le_add
    (Nat.add_le_add (passOperationBound_mono hle)
      (clearColumnOperationCount_total_mono hle))
    (injectionOperationCount_total_mono hle)

/-- Expanded dimension polynomial dominating every stabilization level. -/
@[expose] public def stabilizationLevelPolynomialBound
    (dimension : Nat) : Nat :=
  9 * dimension ^ 4 + 2 * dimension ^ 3 +
    11 * dimension ^ 2 + 5 * dimension

public theorem stabilizationLevelOperationBound_le_polynomial
    (dimension : Nat) :
    stabilizationLevelOperationBound dimension ≤
      stabilizationLevelPolynomialBound dimension := by
  rw [stabilizationLevelOperationBound, clearColumnOperationCount_total,
    injectionOperationCount_total]
  unfold passOperationBound leftPhaseOperationBound
    principalRingOperationBound stabilizationLevelPolynomialBound
  calc
    dimension * (3 * dimension) +
          dimension * (6 * dimension) + 2 * dimension +
          (dimension * (3 * dimension ^ 3) +
            dimension * (6 * dimension ^ 3) + 2 * dimension ^ 3) +
          (2 * (dimension - 1) * dimension + (dimension - 1)) +
          2 * dimension ≤
        dimension * (3 * dimension) +
          dimension * (6 * dimension) + 2 * dimension +
          (dimension * (3 * dimension ^ 3) +
            dimension * (6 * dimension ^ 3) + 2 * dimension ^ 3) +
          (2 * dimension * dimension + dimension) +
          2 * dimension := by
      gcongr <;> omega
    _ = 9 * dimension ^ 4 + 2 * dimension ^ 3 +
          11 * dimension ^ 2 + 5 * dimension := by ring

public theorem clearColumnOperationCount_total_le_level (dimension : Nat) :
    (clearColumnOperationCount dimension).total ≤
      stabilizationLevelOperationBound dimension := by
  unfold stabilizationLevelOperationBound
  omega

public theorem injectionOperationCount_total_le_level (dimension : Nat) :
    (injectionOperationCount dimension).total ≤
      stabilizationLevelOperationBound dimension := by
  unfold stabilizationLevelOperationBound
  omega

public theorem passOperationCount_total_le_level {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (passOperationCount A hdet).total ≤
      stabilizationLevelOperationBound (n + 1) :=
  (passOperationCount_total_le A hdet).trans (by
    unfold stabilizationLevelOperationBound
    omega)

public theorem levelOperationCount_total_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (clearColumnOperationCount (n + 1)).total +
        (injectionOperationCount (n + 1)).total +
        (passOperationCount A hdet).total ≤
      stabilizationLevelOperationBound (n + 1) := by
  unfold stabilizationLevelOperationBound
  have passLe := passOperationCount_total_le A hdet
  omega

/-- Exact recursive algebraic charge of the total inner stabilization loop. -/
@[expose] public def stabilizeFromOperationCount {n : Nat} :
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) →
      A.det ≠ 0 → A 0 0 ≠ 0 →
        A 0 0 = _root_.normalize (A 0 0) → FirstRowCleared A →
          SmithOperationCount
  | A, hdet, _hpivot, _hnormalized, hrow =>
      match hbadColumn : firstUndivisibleBelow? A with
      | some _row =>
          let current := pass A hdet
          let shape := pass_shape A hdet
          (passOperationCount A hdet).add <|
            stabilizeFromOperationCount current.result
              (pass_result_det_ne_zero A hdet) shape.1 shape.2.1 shape.2.2
      | none =>
          let hdiv := firstUndivisibleBelow?_eq_none A hbadColumn
          let cleared := clearDivisibleFirstColumn A
          let _hclearedColumn :=
            clearDivisibleFirstColumn_firstColumnCleared A hdiv
          let _hclearedRow :=
            clearDivisibleFirstColumn_firstRowCleared A hrow
          let clearCost := clearColumnOperationCount (n + 1)
          match hbadLower : firstUndivisibleLower? cleared.result with
          | none => clearCost
          | some position =>
              let injection := injectLowerWitness cleared.result position.2
              let accumulated := compose cleared injection
              let accumulatedDet := result_det_ne_zero accumulated hdet
              let current := pass accumulated.result accumulatedDet
              let shape := pass_shape accumulated.result accumulatedDet
              clearCost.add <| (injectionOperationCount (n + 1)).add <|
                (passOperationCount accumulated.result accumulatedDet).add <|
                  stabilizeFromOperationCount current.result
                    (pass_result_det_ne_zero accumulated.result accumulatedDet)
                    shape.1 shape.2.1 shape.2.2
termination_by A _ _ _ _ => (A 0 0).natAbs.size
decreasing_by
  · exact pass_pivot_natSize_lt_of_not_dvd_entry A hdet _hpivot _row.succ
      (firstUndivisibleBelow?_some_not_dvd A hbadColumn)
  · have accumulatedPivot : accumulated.result 0 0 = A 0 0 := by
      exact (injectLowerWitness_pivot cleared.result position.2
        _hclearedRow).trans (clearDivisibleFirstColumn_pivot A)
    have target : accumulated.result position.1.succ 0 =
        cleared.result position.1.succ position.2.succ :=
      injectLowerWitness_target cleared.result position.1 position.2
        _hclearedColumn
    have hnot : ¬ accumulated.result 0 0 ∣
        accumulated.result position.1.succ 0 := by
      rw [accumulatedPivot, target]
      have original := firstUndivisibleLower?_some_not_dvd
        cleared.result hbadLower
      rw [← show cleared.result 0 0 = A 0 0 by
        exact clearDivisibleFirstColumn_pivot A]
      exact original
    have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
      accumulated.result accumulatedDet
      (by simpa [accumulatedPivot] using _hpivot) position.1.succ hnot
    simpa [accumulatedPivot] using decrease

/-- Exact algebraic charge of total pivot stabilization. -/
@[expose] public def stabilizeOperationCount {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) : SmithOperationCount :=
  let initial := pass A hdet
  let shape := pass_shape A hdet
  (passOperationCount A hdet).add <|
    stabilizeFromOperationCount initial.result
      (pass_result_det_ne_zero A hdet) shape.1 shape.2.1 shape.2.2

/-- The exact inner charge is linear in pivot bit length and one-level cost. -/
public theorem stabilizeFromOperationCount_total_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = _root_.normalize (A 0 0))
    (hrow : FirstRowCleared A) :
    (stabilizeFromOperationCount A hdet hpivot hnormalized hrow).total ≤
      (A 0 0).natAbs.size * stabilizationLevelOperationBound (n + 1) := by
  generalize measureEq : (A 0 0).natAbs.size = measure
  induction measure using Nat.strong_induction_on generalizing A with
  | h measure ih =>
      rw [stabilizeFromOperationCount.eq_1]
      split
      next row hbadColumn =>
        dsimp only
        rw [SmithOperationCount.total_add]
        have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
          A hdet hpivot row.succ
            (firstUndivisibleBelow?_some_not_dvd A hbadColumn)
        have nextBound := ih _ (by omega) (pass A hdet).result
          (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
          (pass_shape A hdet).2.1 (pass_shape A hdet).2.2 rfl
        have passBound := passOperationCount_total_le_level A hdet
        calc
          (passOperationCount A hdet).total +
                (stabilizeFromOperationCount (pass A hdet).result
                  (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
                  (pass_shape A hdet).2.1 (pass_shape A hdet).2.2).total ≤
              stabilizationLevelOperationBound (n + 1) +
                ((pass A hdet).result 0 0).natAbs.size *
                  stabilizationLevelOperationBound (n + 1) :=
            Nat.add_le_add passBound nextBound
          _ = (((pass A hdet).result 0 0).natAbs.size + 1) *
                stabilizationLevelOperationBound (n + 1) := by ring
          _ ≤ measure * stabilizationLevelOperationBound (n + 1) := by
            apply Nat.mul_le_mul_right
            omega
      next hnoBadColumn =>
        dsimp only
        split
        next _hnoBadLower =>
          have clearBound := clearColumnOperationCount_total_le_level (n + 1)
          have measurePos : 0 < measure := by
            rw [← measureEq, Nat.size_pos]
            exact Int.natAbs_pos.mpr hpivot
          calc
            (clearColumnOperationCount (n + 1)).total ≤
                stabilizationLevelOperationBound (n + 1) := clearBound
            _ = 1 * stabilizationLevelOperationBound (n + 1) := by simp
            _ ≤ measure * stabilizationLevelOperationBound (n + 1) := by
              exact Nat.mul_le_mul_right _ measurePos
        next position hbadLower =>
          rw [SmithOperationCount.total_add, SmithOperationCount.total_add,
            SmithOperationCount.total_add]
          let cleared := clearDivisibleFirstColumn A
          let hdiv := firstUndivisibleBelow?_eq_none A hnoBadColumn
          let hclearedColumn :=
            clearDivisibleFirstColumn_firstColumnCleared A hdiv
          let hclearedRow :=
            clearDivisibleFirstColumn_firstRowCleared A hrow
          let injection := injectLowerWitness cleared.result position.2
          let accumulated := compose cleared injection
          let accumulatedDet := result_det_ne_zero accumulated hdet
          have accumulatedPivot : accumulated.result 0 0 = A 0 0 := by
            exact (injectLowerWitness_pivot cleared.result position.2
              hclearedRow).trans (clearDivisibleFirstColumn_pivot A)
          have target : accumulated.result position.1.succ 0 =
              cleared.result position.1.succ position.2.succ :=
            injectLowerWitness_target cleared.result position.1 position.2
              hclearedColumn
          have hnot : ¬ accumulated.result 0 0 ∣
              accumulated.result position.1.succ 0 := by
            rw [accumulatedPivot, target]
            have original := firstUndivisibleLower?_some_not_dvd
              cleared.result hbadLower
            rw [← show cleared.result 0 0 = A 0 0 by
              exact clearDivisibleFirstColumn_pivot A]
            exact original
          have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
            accumulated.result accumulatedDet
            (by simpa [accumulatedPivot] using hpivot) position.1.succ hnot
          have decreaseMeasure :
              ((pass accumulated.result accumulatedDet).result 0 0).natAbs.size <
                measure := by
            simpa [accumulatedPivot, measureEq] using decrease
          have nextBound := ih _ decreaseMeasure
            (pass accumulated.result accumulatedDet).result
            (pass_result_det_ne_zero accumulated.result accumulatedDet)
            (pass_shape accumulated.result accumulatedDet).1
            (pass_shape accumulated.result accumulatedDet).2.1
            (pass_shape accumulated.result accumulatedDet).2.2 rfl
          have levelBound := levelOperationCount_total_le
            accumulated.result accumulatedDet
          calc
            (clearColumnOperationCount (n + 1)).total +
                  ((injectionOperationCount (n + 1)).total +
                    ((passOperationCount accumulated.result accumulatedDet).total +
                      (stabilizeFromOperationCount
                        (pass accumulated.result accumulatedDet).result
                        (pass_result_det_ne_zero accumulated.result accumulatedDet)
                        (pass_shape accumulated.result accumulatedDet).1
                        (pass_shape accumulated.result accumulatedDet).2.1
                        (pass_shape accumulated.result accumulatedDet).2.2).total)) =
                ((clearColumnOperationCount (n + 1)).total +
                  (injectionOperationCount (n + 1)).total +
                  (passOperationCount accumulated.result accumulatedDet).total) +
                  (stabilizeFromOperationCount
                    (pass accumulated.result accumulatedDet).result
                    (pass_result_det_ne_zero accumulated.result accumulatedDet)
                    (pass_shape accumulated.result accumulatedDet).1
                    (pass_shape accumulated.result accumulatedDet).2.1
                    (pass_shape accumulated.result accumulatedDet).2.2).total := by
              omega
            _ ≤ stabilizationLevelOperationBound (n + 1) +
                  ((pass accumulated.result accumulatedDet).result 0 0).natAbs.size *
                    stabilizationLevelOperationBound (n + 1) :=
              Nat.add_le_add levelBound nextBound
            _ = (((pass accumulated.result accumulatedDet).result 0 0).natAbs.size + 1) *
                  stabilizationLevelOperationBound (n + 1) := by ring
            _ ≤ measure * stabilizationLevelOperationBound (n + 1) := by
              exact Nat.mul_le_mul_right _
                (Nat.succ_le_iff.mpr decreaseMeasure)

/-- Total stabilization has a determinant-width times per-level budget. -/
public theorem stabilizeOperationCount_total_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (stabilizeOperationCount A hdet).total ≤
      (integerBitLength A.det + 1) *
        stabilizationLevelOperationBound (n + 1) := by
  rw [stabilizeOperationCount, SmithOperationCount.total_add]
  have passBound := passOperationCount_total_le_level A hdet
  have innerBound := stabilizeFromOperationCount_total_le
    (pass A hdet).result (pass_result_det_ne_zero A hdet)
    (pass_shape A hdet).1 (pass_shape A hdet).2.1
    (pass_shape A hdet).2.2
  calc
    (passOperationCount A hdet).total +
          (stabilizeFromOperationCount (pass A hdet).result
            (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
            (pass_shape A hdet).2.1 (pass_shape A hdet).2.2).total ≤
        stabilizationLevelOperationBound (n + 1) +
          ((pass A hdet).result 0 0).natAbs.size *
            stabilizationLevelOperationBound (n + 1) :=
      Nat.add_le_add passBound innerBound
    _ = (((pass A hdet).result 0 0).natAbs.size + 1) *
          stabilizationLevelOperationBound (n + 1) := by ring
    _ ≤ (integerBitLength A.det + 1) *
          stabilizationLevelOperationBound (n + 1) := by
      exact Nat.mul_le_mul_right _ <|
        Nat.add_le_add_right (pass_pivotBitLength_le_determinant A hdet) 1

end NormalForms.Research.KannanBachem.Smith
