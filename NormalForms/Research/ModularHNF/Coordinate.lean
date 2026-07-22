/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Run
import all NormalForms.Research.ModularHNF.Run

/-!
# Coordinate divisibility in a partially reduced lattice

Processed positive pivots force coefficients of earlier rows to vanish in
any row combination whose coordinate prefix is zero.  Consequently, once a
current column is zero below its pivot, the gcd of that pivot and the live
modulus divides the current coordinate of every prefix-zero vector in the
augmented lattice.  This is the local uniqueness fact used by the semantic
modular-HNF invariant.
-/

public section

namespace NormalForms.Research.ModularHNF

open scoped BigOperators Matrix

/-- A zero-prefix row combination has zero coefficients on all processed rows. -/
public theorem coefficients_zero_before_of_combination_zero {m n k : Nat}
    (columns_le_rows : n ≤ m)
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (processed_le : k ≤ n)
    (shape : ProcessedHermiteShape columns_le_rows A k)
    (coeff : Fin m → Int)
    (combinationZero : ∀ column, column.val < k →
      (∑ row : Fin m, coeff row * A row column) = 0) :
    ∀ row : Fin m, row.val < k → coeff row = 0 := by
  have byIndex : ∀ index, index < k →
      ∀ row : Fin m, row.val = index → coeff row = 0 := by
    intro index
    induction index using Nat.strong_induction_on with
    | h index ih =>
      intro indexBeforeK row rowValue
      have indexBeforeN : index < n :=
        lt_of_lt_of_le indexBeforeK processed_le
      let column : Fin n := ⟨index, indexBeforeN⟩
      let pivot : Fin m := Fin.castLE columns_le_rows column
      have pivotEq : pivot = row := by
        apply Fin.ext
        simpa [pivot, column] using rowValue.symm
      have columnShape := shape column (by
        simpa [column] using indexBeforeK)
      have sumEq :
          (∑ currentRow : Fin m, coeff currentRow * A currentRow column) =
            coeff pivot * A pivot column := by
        rw [Finset.sum_eq_single pivot]
        · intro currentRow _ currentNe
          by_cases currentBefore : currentRow.val < index
          · have coefficientZero : coeff currentRow = 0 :=
              ih currentRow.val currentBefore (by omega) currentRow rfl
            simp [coefficientZero]
          · have pivotBefore : pivot < currentRow := by
              change index < currentRow.val
              omega
            rw [columnShape.below_zero currentRow pivotBefore]
            simp
        · simp
      have productZero : coeff pivot * A pivot column = 0 := by
        rw [← sumEq]
        exact combinationZero column (by
          simpa [column] using indexBeforeK)
      have coefficientZero : coeff pivot = 0 :=
        (mul_eq_zero.mp productZero).resolve_right
          (ne_of_gt columnShape.pivot_positive)
      simpa [pivotEq] using coefficientZero
  intro row rowBefore
  exact byIndex row.val rowBefore row rfl

/-- The local pivot/modulus gcd divides every prefix-zero coordinate in the augmented lattice. -/
public theorem coordinate_dvd_of_mem_augmented {m n k : Nat}
    (columns_le_rows : n ≤ m)
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (processed_lt : k < n)
    (shape : ProcessedHermiteShape columns_le_rows A k)
    (pivot : Fin m) (column : Fin n)
    (pivotValue : pivot.val = k) (columnValue : column.val = k)
    (belowZero : ∀ row, pivot < row → A row column = 0)
    (modulus divisor : Int)
    (divisorDvdPivot : divisor ∣ A pivot column)
    (divisorDvdModulus : divisor ∣ modulus)
    {vector : Fin n → Int}
    (membership : vector ∈ augmentedRowSpan A modulus k)
    (vectorZero : ∀ currentColumn, currentColumn.val < k →
      vector currentColumn = 0) :
    divisor ∣ vector column := by
  rcases Submodule.mem_sup.mp membership with
    ⟨rowVector, rowMembership, suffixVector, suffixMembership, sumEquality⟩
  rcases (Submodule.mem_span_range_iff_exists_fun Int).mp rowMembership with
    ⟨coeff, rowEquality⟩
  have suffixCoordinates := suffixModule_coordinates suffixMembership
  have rowVectorZero : ∀ currentColumn, currentColumn.val < k →
      rowVector currentColumn = 0 := by
    intro currentColumn before
    have sumEntry := congrFun sumEquality currentColumn
    have sourceZero := vectorZero currentColumn before
    have suffixZero := suffixCoordinates.1 currentColumn before
    change rowVector currentColumn + suffixVector currentColumn =
      vector currentColumn at sumEntry
    rw [sourceZero, suffixZero] at sumEntry
    simpa using sumEntry
  have combinationZero : ∀ currentColumn, currentColumn.val < k →
      (∑ row : Fin m, coeff row * A row currentColumn) = 0 := by
    intro currentColumn before
    have entry := congrFun rowEquality currentColumn
    rw [rowVectorZero currentColumn before] at entry
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      _root_.Matrix.row] using entry
  have coeffZero := coefficients_zero_before_of_combination_zero
    columns_le_rows A (Nat.le_of_lt processed_lt) shape coeff combinationZero
  have rowDivides : divisor ∣ rowVector column := by
    have entry := congrFun rowEquality column
    rw [← entry]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.dvd_sum
    intro row _
    by_cases rowBefore : row.val < k
    · rw [coeffZero row rowBefore]
      simp
    · by_cases rowEq : row = pivot
      · subst row
        exact dvd_mul_of_dvd_right divisorDvdPivot (coeff pivot)
      · have pivotBefore : pivot < row := by
          change pivot.val < row.val
          omega
        change divisor ∣ coeff row * A row column
        rw [belowZero row pivotBefore]
        simp
  have suffixDivides : divisor ∣ suffixVector column :=
    dvd_trans divisorDvdModulus (suffixCoordinates.2 column)
  have entry := congrFun sumEquality column
  rw [← entry]
  exact dvd_add rowDivides suffixDivides

end NormalForms.Research.ModularHNF
