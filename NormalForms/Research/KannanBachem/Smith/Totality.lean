/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.Clear
public import NormalForms.Research.KannanBachem.Smith.Stabilize

/-!
# Total Kannan--Bachem Pivot Stabilization

The fuelled loop is useful for execution regressions, but its successful-run
theorems alone do not establish an algorithm.  This module closes that semantic
gap with a well-founded implementation.

After each full Step-4/Step-5 pass, the first row is cleared and the pivot is
normalized.  Entries in the first column that are already divisible by the
pivot are cleared by a certified shear.  Every remaining continuation then
contains an entry not divisible by the current pivot: either one was already in
the first column, or Step 7 injects one from the lower-right block.  The next
pass produces a proper common divisor, so the pivot's binary size strictly
decreases. This is the sole termination measure; no generic Smith computation
is used.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Research.KannanBachem.Hermite

/--
Total inner loop, entered with the invariant produced by a full pass.  Its
recursive calls are exactly the branches with a strictly smaller pivot.
-/
@[expose] public def stabilizeFrom {n : Nat} :
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) →
      A.det ≠ 0 → A 0 0 ≠ 0 →
        A 0 0 = _root_.normalize (A 0 0) → FirstRowCleared A →
          Stabilization A
  | A, hdet, hpivot, hnormalized, hrow =>
      match hbadColumn : firstUndivisibleBelow? A with
      | some row =>
          let current := pass A hdet
          let shape := pass_shape A hdet
          let next := stabilizeFrom current.result
            (pass_result_det_ne_zero A hdet) shape.1 shape.2.1 shape.2.2
          { certificate := compose current next.certificate
            stable := next.stable
            passes := next.passes + 1
            injections := next.injections }
      | none =>
          let hdiv := firstUndivisibleBelow?_eq_none A hbadColumn
          let cleared := clearDivisibleFirstColumn A
          let hclearedColumn :=
            clearDivisibleFirstColumn_firstColumnCleared A hdiv
          let hclearedRow :=
            clearDivisibleFirstColumn_firstRowCleared A hrow
          match hbadLower : firstUndivisibleLower? cleared.result with
          | none =>
              { certificate := cleared
                stable :=
                  { pivot_ne_zero := by
                      rw [show cleared.result 0 0 = A 0 0 by
                        exact clearDivisibleFirstColumn_pivot A]
                      exact hpivot
                    pivot_normalized := by
                      rw [show cleared.result 0 0 = A 0 0 by
                        exact clearDivisibleFirstColumn_pivot A]
                      exact hnormalized
                    firstRowCleared := hclearedRow
                    firstColumnCleared := hclearedColumn
                    pivotDividesLower :=
                      firstUndivisibleLower?_eq_none cleared.result hbadLower }
                passes := 0
                injections := 0 }
          | some position =>
              let injection := injectLowerWitness cleared.result position.2
              let accumulated := compose cleared injection
              let accumulatedDet := result_det_ne_zero accumulated hdet
              let current := pass accumulated.result accumulatedDet
              let shape := pass_shape accumulated.result accumulatedDet
              let next := stabilizeFrom current.result
                (pass_result_det_ne_zero accumulated.result accumulatedDet)
                shape.1 shape.2.1 shape.2.2
              { certificate := compose accumulated
                  (compose current next.certificate)
                stable := next.stable
                passes := next.passes + 1
                injections := next.injections + 1 }
termination_by A _ _ _ _ => (A 0 0).natAbs.size
decreasing_by
  · exact pass_pivot_natSize_lt_of_not_dvd_entry A hdet hpivot row.succ
      (firstUndivisibleBelow?_some_not_dvd A hbadColumn)
  · have accumulatedPivot : accumulated.result 0 0 = A 0 0 := by
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
    simpa [accumulatedPivot] using decrease

/-- Every recursive continuation consumes one strictly smaller positive pivot. -/
public theorem stabilizeFrom_passes_le_pivotBitLength {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = _root_.normalize (A 0 0))
    (hrow : FirstRowCleared A) :
    (stabilizeFrom A hdet hpivot hnormalized hrow).passes ≤
      (A 0 0).natAbs.size := by
  generalize measureEq : (A 0 0).natAbs.size = measure
  induction measure using Nat.strong_induction_on generalizing A with
  | h measure ih =>
      rw [stabilizeFrom.eq_1]
      split
      next row hbadColumn =>
        dsimp only
        have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
          A hdet hpivot row.succ
            (firstUndivisibleBelow?_some_not_dvd A hbadColumn)
        have nextBound := ih _ (by omega) (pass A hdet).result
          (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
          (pass_shape A hdet).2.1 (pass_shape A hdet).2.2 rfl
        omega
      next hnoBadColumn =>
        dsimp only
        split
        next _hnoBadLower =>
          simp
        next position hbadLower =>
          dsimp only
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
          have finalBound :
              (stabilizeFrom
                (pass accumulated.result accumulatedDet).result
                (pass_result_det_ne_zero accumulated.result accumulatedDet)
                (pass_shape accumulated.result accumulatedDet).1
                (pass_shape accumulated.result accumulatedDet).2.1
                (pass_shape accumulated.result accumulatedDet).2.2).passes + 1 ≤
                  measure :=
            Nat.succ_le_iff.mpr (lt_of_le_of_lt nextBound decreaseMeasure)
          simpa [cleared, injection, accumulated, accumulatedDet] using finalBound

/-- The binary-size pass bound also implies the coarser absolute-value bound. -/
public theorem stabilizeFrom_passes_le_natAbs {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = _root_.normalize (A 0 0))
    (hrow : FirstRowCleared A) :
    (stabilizeFrom A hdet hpivot hnormalized hrow).passes ≤
      (A 0 0).natAbs :=
  (stabilizeFrom_passes_le_pivotBitLength A hdet hpivot hnormalized hrow).trans
    (Nat.size_le.mpr (A 0 0).natAbs.lt_two_pow_self)

/--
Total pivot stabilization for every nonsingular positive-dimensional square
integer matrix.
-/
@[expose] public def stabilize {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) : Stabilization A :=
  let initial := pass A hdet
  let shape := pass_shape A hdet
  let rest := stabilizeFrom initial.result
    (pass_result_det_ne_zero A hdet) shape.1 shape.2.1 shape.2.2
  { certificate := compose initial rest.certificate
    stable := rest.stable
    passes := rest.passes + 1
    injections := rest.injections }

public theorem stabilize_passes_pos {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) : 0 < (stabilize A hdet).passes := by
  simp [stabilize]

/-- Closed pass bound for total stabilization after its mandatory first pass. -/
public theorem stabilize_passes_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (stabilize A hdet).passes ≤
      ((pass A hdet).result 0 0).natAbs.size + 1 := by
  change
    (stabilizeFrom (pass A hdet).result
      (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
      (pass_shape A hdet).2.1 (pass_shape A hdet).2.2).passes + 1 ≤
        ((pass A hdet).result 0 0).natAbs.size + 1
  exact Nat.add_le_add_right
    (stabilizeFrom_passes_le_pivotBitLength (pass A hdet).result
      (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
      (pass_shape A hdet).2.1 (pass_shape A hdet).2.2) 1

/-- Stabilization takes at most one more pass than the input coefficient width. -/
public theorem stabilize_passes_le_inputBitLength {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (stabilize A hdet).passes ≤ matrixBitLength A + 1 :=
  (stabilize_passes_le A hdet).trans
    (Nat.add_le_add_right (pass_pivotBitLength_le_input A hdet) 1)

end NormalForms.Research.KannanBachem.Smith
