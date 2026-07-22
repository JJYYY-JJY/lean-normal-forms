/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Below
import all NormalForms.Research.ModularHNF.Below

/-!
# The above-pivot loop of modular HNF

Once a stage has produced a nonzero pivot, the executable kernel visits every
earlier row and replaces its pivot-column entry by the canonical integer
remainder.  The lemmas below follow the list recursion exactly and also show
that the pivot row, all lower rows, and the processed prefix stay unchanged.
-/

public section

namespace NormalForms.Research.ModularHNF

namespace Internal

open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary

theorem reduceAboveRow_apply_of_other {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target row : Fin m) (rowNotTarget : row ≠ target)
    (column currentColumn : Fin n) :
    reduceAboveRow A pivot target column row currentColumn =
      A row currentColumn := by
  simp [reduceAboveRow, rowNotTarget]

theorem reduceAboveRow_apply_before {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target row : Fin m) (column currentColumn : Fin n)
    (before : currentColumn < column) :
    reduceAboveRow A pivot target column row currentColumn =
      A row currentColumn := by
  have notAfter : ¬ column ≤ currentColumn := not_le_of_gt before
  simp [reduceAboveRow, notAfter]

theorem reduceAboveRow_target_column {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n) :
    reduceAboveRow A pivot target column target column =
      A target column % A pivot column := by
  rw [EuclideanDomain.mod_eq_sub_mul_div]
  simp [reduceAboveRow]
  ring

/-- With a zero pivot prefix, the suffix-only update is exactly a unimodular row addition. -/
theorem reduceAboveRow_rowSpan_eq {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (pivotNotTarget : pivot ≠ target)
    (column : Fin n)
    (pivotPrefixZero : ∀ currentColumn, currentColumn < column →
      A pivot currentColumn = 0) :
    rowSpan (reduceAboveRow A pivot target column) = rowSpan A := by
  let quotient := A target column / A pivot column
  let transform := rowOperationMatrix
    (.add pivot target (-quotient) : RowOperation Int (Fin m))
  have matrixEq : reduceAboveRow A pivot target column = transform * A := by
    rw [rowOperationMatrix_mul]
    ext row currentColumn
    by_cases rowEq : row = target
    · subst row
      by_cases after : column ≤ currentColumn
      · simp [reduceAboveRow, applyRowOperation, quotient, after]
        ring
      · have before : currentColumn < column := lt_of_not_ge after
        have pivotZero := pivotPrefixZero currentColumn before
        simp [reduceAboveRow, applyRowOperation, quotient, after, pivotZero]
    · simp [reduceAboveRow, applyRowOperation, rowEq]
  rw [matrixEq]
  exact rowSpan_mul_eq
    (rowAddInverseCertificate pivot target (-quotient) pivotNotTarget) A

theorem reduceAboveRow_prefixRowsZero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n)
    (prefixZero : PrefixRowsZero A column.val) :
    PrefixRowsZero (reduceAboveRow A pivot target column) column.val := by
  intro row rowAfter currentColumn currentBefore
  rw [reduceAboveRow_apply_before A pivot target row column currentColumn]
  · exact prefixZero row rowAfter currentColumn currentBefore
  · exact currentBefore

theorem reduceAbove_apply_before {m n : Nat}
    (pivot row : Fin m) (column currentColumn : Fin n)
    (before : currentColumn < column) (rows : List (Fin m))
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    reduceAbove pivot column rows A row currentColumn =
      A row currentColumn := by
  induction rows generalizing A with
  | nil => rfl
  | cons target tail ih =>
      unfold reduceAbove
      split
      · calc
          reduceAbove pivot column tail
              (reduceAboveRow A pivot target column) row currentColumn =
            reduceAboveRow A pivot target column row currentColumn := ih _
          _ = A row currentColumn :=
            reduceAboveRow_apply_before A pivot target row column
              currentColumn before
      · exact ih A

theorem reduceAbove_prefixRowsZero {m n : Nat}
    (pivot : Fin m) (column : Fin n) (rows : List (Fin m))
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (prefixZero : PrefixRowsZero A column.val) :
    PrefixRowsZero (reduceAbove pivot column rows A) column.val := by
  intro row rowAfter currentColumn currentBefore
  rw [reduceAbove_apply_before pivot row column currentColumn currentBefore]
  exact prefixZero row rowAfter currentColumn currentBefore

/-- The complete above-pivot scan preserves the exact row lattice. -/
theorem reduceAbove_rowSpan_eq {m n : Nat}
    (pivot : Fin m) (column : Fin n) (rows : List (Fin m))
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivotAfter : column.val ≤ pivot.val)
    (prefixZero : PrefixRowsZero A column.val) :
    rowSpan (reduceAbove pivot column rows A) = rowSpan A := by
  induction rows generalizing A with
  | nil => rfl
  | cons target tail ih =>
      unfold reduceAbove
      split
      · rename_i targetBeforePivot
        have pivotNotTarget : pivot ≠ target := targetBeforePivot.ne'
        have pivotPrefixZero :
            ∀ currentColumn, currentColumn < column →
              A pivot currentColumn = 0 := by
          intro currentColumn before
          exact prefixZero pivot pivotAfter currentColumn before
        calc
          rowSpan
              (reduceAbove pivot column tail
                (reduceAboveRow A pivot target column)) =
              rowSpan (reduceAboveRow A pivot target column) :=
            ih (reduceAboveRow A pivot target column)
              (reduceAboveRow_prefixRowsZero A pivot target column prefixZero)
          _ = rowSpan A :=
            reduceAboveRow_rowSpan_eq A pivot target pivotNotTarget column
              pivotPrefixZero
      · exact ih A prefixZero

/-- Above-pivot reduction also preserves every augmented row lattice. -/
theorem reduceAbove_augmentedRowSpan_eq {m n : Nat}
    (pivot : Fin m) (column : Fin n) (rows : List (Fin m))
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (modulus : Int) (k : Nat)
    (pivotAfter : column.val ≤ pivot.val)
    (prefixZero : PrefixRowsZero A column.val) :
    augmentedRowSpan (reduceAbove pivot column rows A) modulus k =
      augmentedRowSpan A modulus k := by
  rw [augmentedRowSpan, augmentedRowSpan,
    reduceAbove_rowSpan_eq pivot column rows A pivotAfter prefixZero]

theorem reduceAbove_pivot_apply {m n : Nat}
    (pivot : Fin m) (column currentColumn : Fin n)
    (rows : List (Fin m)) (A : _root_.Matrix (Fin m) (Fin n) Int) :
    reduceAbove pivot column rows A pivot currentColumn =
      A pivot currentColumn := by
  induction rows generalizing A with
  | nil => rfl
  | cons target tail ih =>
      unfold reduceAbove
      split
      · rename_i targetBeforePivot
        calc
          reduceAbove pivot column tail
              (reduceAboveRow A pivot target column) pivot currentColumn =
            reduceAboveRow A pivot target column pivot currentColumn := ih _
          _ = A pivot currentColumn :=
            reduceAboveRow_apply_of_other A pivot target pivot
              targetBeforePivot.ne' column currentColumn
      · exact ih A

theorem reduceAbove_apply_of_below {m n : Nat}
    (pivot row : Fin m) (pivotBeforeRow : pivot < row)
    (column currentColumn : Fin n) (rows : List (Fin m))
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    reduceAbove pivot column rows A row currentColumn =
      A row currentColumn := by
  induction rows generalizing A with
  | nil => rfl
  | cons target tail ih =>
      unfold reduceAbove
      split
      · rename_i targetBeforePivot
        have rowNotTarget : row ≠ target :=
          ne_of_gt (targetBeforePivot.trans pivotBeforeRow)
        calc
          reduceAbove pivot column tail
              (reduceAboveRow A pivot target column) row currentColumn =
            reduceAboveRow A pivot target column row currentColumn := ih _
          _ = A row currentColumn :=
            reduceAboveRow_apply_of_other A pivot target row rowNotTarget
              column currentColumn
      · exact ih A

theorem reduceAbove_apply_of_not_mem {m n : Nat}
    (pivot row : Fin m)
    (column currentColumn : Fin n) (rows : List (Fin m))
    (rowNotMem : row ∉ rows)
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    reduceAbove pivot column rows A row currentColumn =
      A row currentColumn := by
  induction rows generalizing A with
  | nil => rfl
  | cons target tail ih =>
      have rowNotTarget : row ≠ target := by
        intro equality
        apply rowNotMem
        simp [equality]
      have rowNotTail : row ∉ tail := by
        intro membership
        exact rowNotMem (List.mem_cons_of_mem target membership)
      unfold reduceAbove
      split
      · calc
          reduceAbove pivot column tail
              (reduceAboveRow A pivot target column) row currentColumn =
            reduceAboveRow A pivot target column row currentColumn :=
              ih rowNotTail _
          _ = A row currentColumn :=
            reduceAboveRow_apply_of_other A pivot target row rowNotTarget
              column currentColumn
      · exact ih rowNotTail A

theorem reduceAbove_mem_column_eq_mod {m n : Nat}
    (pivot : Fin m) (column : Fin n) (rows : List (Fin m))
    (rowsNodup : rows.Nodup)
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (rowMem : row ∈ rows) (rowBeforePivot : row < pivot) :
    reduceAbove pivot column rows A row column =
      A row column % A pivot column := by
  induction rows generalizing A with
  | nil => simp at rowMem
  | cons target tail ih =>
      have targetNotTail : target ∉ tail :=
        (List.nodup_cons.mp rowsNodup).1
      have tailNodup := (List.nodup_cons.mp rowsNodup).2
      rcases List.mem_cons.mp rowMem with rowEq | rowInTail
      · subst row
        unfold reduceAbove
        rw [if_pos rowBeforePivot]
        calc
          reduceAbove pivot column tail
              (reduceAboveRow A pivot target column) target column =
            reduceAboveRow A pivot target column target column := by
              exact reduceAbove_apply_of_not_mem pivot target
                column column tail targetNotTail _
          _ = A target column % A pivot column :=
            reduceAboveRow_target_column A pivot target column
      · unfold reduceAbove
        split
        · rename_i targetBeforePivot
          have rowNotTarget : row ≠ target := by
            intro equality
            subst row
            exact targetNotTail rowInTail
          have rowEntry :
              reduceAboveRow A pivot target column row column =
                A row column :=
            reduceAboveRow_apply_of_other A pivot target row rowNotTarget
              column column
          have pivotEntry :
              reduceAboveRow A pivot target column pivot column =
                A pivot column :=
            reduceAboveRow_apply_of_other A pivot target pivot
              targetBeforePivot.ne' column column
          simpa [rowEntry, pivotEntry] using
            ih tailNodup (reduceAboveRow A pivot target column)
              rowInTail
        · exact ih tailNodup A rowInTail

/-- Every row above the pivot is reduced modulo that pivot after a full scan. -/
theorem reduceAbove_finRange_column_eq_mod {m n : Nat}
    (pivot : Fin m) (column : Fin n)
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    ∀ row, row < pivot →
      reduceAbove pivot column (List.finRange m).reverse A row column =
        A row column % A pivot column := by
  intro row rowBeforePivot
  exact reduceAbove_mem_column_eq_mod pivot column (List.finRange m).reverse
    (List.nodup_reverse.mpr (List.nodup_finRange m)) A row (by simp)
      rowBeforePivot

end Internal

end NormalForms.Research.ModularHNF
