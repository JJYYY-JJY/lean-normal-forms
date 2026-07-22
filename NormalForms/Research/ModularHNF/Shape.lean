/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Run
public import NormalForms.Matrix.Hermite.Defs
import all NormalForms.Research.ModularHNF.Run
import all NormalForms.Matrix.Hermite.Defs

/-!
# From column shape to the recursive HNF predicate

The modular loop naturally establishes a global triangular column
specification.  The stable core API uses the recursive row-style
`IsHermiteNormalFormFin` predicate.  This module proves the exact bridge,
including rectangular full-column-rank matrices with a zero row tail.
-/

public section

namespace NormalForms.Research.ModularHNF

open NormalForms.Matrix.Hermite

theorem firstNonzero?_eq_some_of_prefix_zero {n : Nat}
    (row : Fin n → Int) (pivot : Fin n)
    (pivotNonzero : row pivot ≠ 0)
    (prefixZero : ∀ column, column < pivot → row column = 0) :
    firstNonzero? row = some pivot := by
  induction n with
  | zero => exact Fin.elim0 pivot
  | succ n ih =>
      cases pivot using Fin.cases with
      | zero => simp [firstNonzero?, pivotNonzero]
      | succ pivot =>
          have headZero : row 0 = 0 := prefixZero 0 (by simp)
          rw [firstNonzero?, headZero]
          have tailNonzero : (fun column : Fin n => row column.succ) pivot ≠ 0 :=
            pivotNonzero
          have tailPrefix : ∀ column, column < pivot → row column.succ = 0 := by
            intro column before
            exact prefixZero column.succ (Fin.succ_lt_succ_iff.mpr before)
          rw [ih (fun column : Fin n => row column.succ) pivot
            tailNonzero tailPrefix]
          rfl

/-- A full-column triangular shape is exactly a core row-style HNF. -/
theorem isHermiteNormalFormFin_of_fullColumnShape {m n : Nat}
    (columns_le_rows : n ≤ m)
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (zeroTail : PrefixRowsZero A n)
    (shape : ∀ column,
      ColumnHermiteShape A (Fin.castLE columns_le_rows column) column) :
    IsHermiteNormalFormFin A := by
  induction n generalizing m with
  | zero => exact .emptyCols A
  | succ n ih =>
      cases m with
      | zero => omega
      | succ m =>
          have tailColumnsLeRows : n ≤ m := by omega
          have topShape : ColumnHermiteShape A 0 0 := by
            simpa using shape 0
          have lowerZeroTail : PrefixRowsZero (lowerRight A) n := by
            intro row rowAfter column columnBefore
            exact zeroTail row.succ
              (by simpa using Nat.succ_le_succ rowAfter)
              column.succ
              (by simp [columnBefore])
          have lowerShape : ∀ column,
              ColumnHermiteShape (lowerRight A)
                (Fin.castLE tailColumnsLeRows column) column := by
            intro column
            have pivotEq :
                Fin.castLE columns_le_rows column.succ =
                  (Fin.castLE tailColumnsLeRows column).succ := by
              apply Fin.ext
              rfl
            have originalShape := shape column.succ
            rw [pivotEq] at originalShape
            exact
              { pivot_positive := by
                  simpa [lowerRight] using originalShape.pivot_positive
                pivot_normalized := by
                  simpa [lowerRight] using originalShape.pivot_normalized
                below_zero := by
                  intro row pivotBeforeRow
                  exact originalShape.below_zero row.succ
                    (Fin.succ_lt_succ_iff.mpr pivotBeforeRow)
                above_reduced := by
                  intro row rowBeforePivot
                  exact originalShape.above_reduced row.succ
                    (Fin.succ_lt_succ_iff.mpr rowBeforePivot) }
          refine .pivot A
            (ne_of_gt topShape.pivot_positive)
            topShape.pivot_normalized
            (fun row => topShape.below_zero row.succ (by simp))
            (ih tailColumnsLeRows (lowerRight A) lowerZeroTail lowerShape)
            ?_
          intro row
          by_cases rowInRank : row.val < n
          · let pivot : Fin n := ⟨row.val, rowInRank⟩
            have pivotRowEq :
                Fin.castLE columns_le_rows pivot.succ = row.succ := by
              apply Fin.ext
              rfl
            have pivotNonzero : A row.succ pivot.succ ≠ 0 := by
              have positive := (shape pivot.succ).pivot_positive
              rw [pivotRowEq] at positive
              exact ne_of_gt positive
            have rowPrefixZero : ∀ column, column < pivot →
                A row.succ column.succ = 0 := by
              intro column columnBefore
              have belowPivot :
                  Fin.castLE columns_le_rows column.succ < row.succ := by
                change column.val + 1 < row.val + 1
                exact Nat.succ_lt_succ columnBefore
              exact (shape column.succ).below_zero row.succ belowPivot
            have firstNonzero :
                firstNonzero? (fun column : Fin n => A row.succ column.succ) =
                  some pivot :=
              firstNonzero?_eq_some_of_prefix_zero _ pivot pivotNonzero
                rowPrefixZero
            rw [firstNonzero]
            have topBeforePivot :
                (0 : Fin (m + 1)) < Fin.castLE columns_le_rows pivot.succ := by
              change 0 < pivot.val + 1
              omega
            have reduced :=
              (shape pivot.succ).above_reduced 0 topBeforePivot
            rw [pivotRowEq] at reduced
            exact reduced
          · have tailRowZero :
                (fun column : Fin n => A row.succ column.succ) =
                  fun _ => 0 := by
              have rowAfter : n ≤ row.val := Nat.le_of_not_gt rowInRank
              funext column
              exact zeroTail row.succ
                (by simpa using Nat.succ_le_succ rowAfter)
                column.succ
                (by simp [column.isLt])
            rw [tailRowZero, firstNonzero?_zero]
            trivial

/-- The raw modular candidate is always syntactically an HNF for positive modulus. -/
theorem runRaw_isHermite {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int) (modulusPositive : 0 < modulus) :
    IsHermiteNormalFormFin (runRaw A columns_le_rows modulus).candidate := by
  have runShape := Internal.runRaw_shape A columns_le_rows modulus modulusPositive
  exact isHermiteNormalFormFin_of_fullColumnShape columns_le_rows
    (runRaw A columns_le_rows modulus).candidate runShape.1 runShape.2.1

end NormalForms.Research.ModularHNF
