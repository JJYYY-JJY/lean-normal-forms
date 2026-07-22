/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Transition
import all NormalForms.Research.ModularHNF.Transition

/-!
# The below-pivot loop of modular HNF

The raw kernel visits every row below the current pivot.  Each active visit is
the suffix-congruent Bézout transition proved in `Transition`; inactive visits
are identities.  This file lifts the local theorem through the executable
list recursion and records preservation of the processed zero prefix.
-/

public section

namespace NormalForms.Research.ModularHNF

open NormalForms
open NormalForms.Matrix.Elementary

namespace Internal

theorem replacePairSuffix_prefixRowsZero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n) (modulus : Int)
    (u v pivotDivGcd targetDivGcd : Int)
    (prefixZero : PrefixRowsZero A column.val) :
    PrefixRowsZero
      (replacePairSuffix A pivot target column modulus
        u v pivotDivGcd targetDivGcd)
      column.val := by
  intro row rowAfter currentColumn currentBefore
  have before : currentColumn < column := currentBefore
  simp [replacePairSuffix, before,
    prefixZero row rowAfter currentColumn currentBefore]

theorem reduceBelowRow_prefixRowsZero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n) (modulus : Int)
    (prefixZero : PrefixRowsZero A column.val) :
    PrefixRowsZero
      (reduceBelowRow A pivot target column modulus).1 column.val := by
  unfold reduceBelowRow
  split
  · exact prefixZero
  · exact replacePairSuffix_prefixRowsZero A pivot target column modulus
      _ _ _ _ prefixZero

theorem reduceBelowRow_augmentedRowSpan {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (hne : pivot ≠ target)
    (column : Fin n) (modulus : Int)
    (prefixZero :
      ∀ row, row = pivot ∨ row = target →
        ∀ currentColumn, currentColumn < column → A row currentColumn = 0) :
    augmentedRowSpan
        (reduceBelowRow A pivot target column modulus).1
        modulus column.val =
      augmentedRowSpan A modulus column.val := by
  unfold reduceBelowRow
  split
  · rfl
  · rename_i targetNonzero
    exact replacePairSuffix_augmentedRowSpan A pivot target hne column modulus
      targetNonzero prefixZero

theorem replacePairSuffix_target_column_zero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (hne : pivot ≠ target)
    (column : Fin n) (modulus : Int) (modulusPositive : 0 < modulus)
    (targetNonzero : A target column ≠ 0) :
    let gcdData := ComputableEuclideanOps.xgcd
      (A pivot column) (A target column)
    replacePairSuffix A pivot target column modulus
        gcdData.leftCoeff gcdData.rightCoeff
        (A pivot column / gcdData.gcd)
        (A target column / gcdData.gcd)
        target column = 0 := by
  let gcdData := ComputableEuclideanOps.xgcd
    (A pivot column) (A target column)
  have gcdNonzero : gcdData.gcd ≠ 0 := by
    intro gcdZero
    have bothZero :=
      (ComputableEuclideanOps.xgcd_gcd_eq_zero_iff
        (A pivot column) (A target column)).mp gcdZero
    exact targetNonzero bothZero.2
  have pivotExact :
      gcdData.gcd * (A pivot column / gcdData.gcd) = A pivot column := by
    simpa [ComputableEuclideanOps.quot_eq] using
      (ComputableEuclideanOps.mul_quot_cancel_of_dvd gcdNonzero
        (ComputableEuclideanOps.xgcd_gcd_dvd_left
          (A pivot column) (A target column)))
  have targetExact :
      gcdData.gcd * (A target column / gcdData.gcd) = A target column := by
    simpa [ComputableEuclideanOps.quot_eq] using
      (ComputableEuclideanOps.mul_quot_cancel_of_dvd gcdNonzero
        (ComputableEuclideanOps.xgcd_gcd_dvd_right
          (A pivot column) (A target column)))
  have baseZero :
      (A pivot column / gcdData.gcd) * A target column -
          (A target column / gcdData.gcd) * A pivot column = 0 := by
    have leftEquality :
        (A pivot column / gcdData.gcd) * A target column =
          (A pivot column / gcdData.gcd) *
            (gcdData.gcd * (A target column / gcdData.gcd)) :=
      congrArg (fun value => (A pivot column / gcdData.gcd) * value)
        targetExact.symm
    have rightEquality :
        (A target column / gcdData.gcd) * A pivot column =
          (A target column / gcdData.gcd) *
            (gcdData.gcd * (A pivot column / gcdData.gcd)) :=
      congrArg (fun value => (A target column / gcdData.gcd) * value)
        pivotExact.symm
    rw [leftEquality, rightEquality]
    ring
  have baseZero' :
      (A pivot column /
            (ComputableEuclideanOps.xgcd
              (A pivot column) (A target column)).gcd) * A target column -
          (A target column /
            (ComputableEuclideanOps.xgcd
              (A pivot column) (A target column)).gcd) * A pivot column = 0 := by
    simpa [gcdData] using baseZero
  have halfNonnegative : 0 ≤ modulus / 2 := by positivity
  simp [replacePairSuffix, hne.symm, baseZero', centeredMod,
    not_lt_of_ge halfNonnegative]

theorem reduceBelowRow_target_column_zero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (hne : pivot ≠ target)
    (column : Fin n) (modulus : Int) (modulusPositive : 0 < modulus) :
    (reduceBelowRow A pivot target column modulus).1 target column = 0 := by
  unfold reduceBelowRow
  split
  · assumption
  · rename_i targetNonzero
    exact replacePairSuffix_target_column_zero A pivot target hne column
      modulus modulusPositive targetNonzero

theorem reduceBelowRow_apply_of_other {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target row : Fin m) (rowNotPivot : row ≠ pivot)
    (rowNotTarget : row ≠ target) (column currentColumn : Fin n)
    (modulus : Int) :
    (reduceBelowRow A pivot target column modulus).1 row currentColumn =
      A row currentColumn := by
  unfold reduceBelowRow
  split
  · rfl
  · simp [replacePairSuffix, rowNotPivot, rowNotTarget]

theorem reduceBelowRow_apply_before {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target row : Fin m) (column currentColumn : Fin n)
    (modulus : Int) (before : currentColumn < column) :
    (reduceBelowRow A pivot target column modulus).1 row currentColumn =
      A row currentColumn := by
  unfold reduceBelowRow
  split
  · rfl
  · simp [replacePairSuffix, before]

theorem reduceBelow_prefixRowsZero {m n : Nat}
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (rows : List (Fin m)) (A : _root_.Matrix (Fin m) (Fin n) Int)
    (prefixZero : PrefixRowsZero A column.val) :
    PrefixRowsZero
      (reduceBelow pivot column modulus rows A).1 column.val := by
  induction rows generalizing A with
  | nil => exact prefixZero
  | cons target tail ih =>
      unfold reduceBelow
      split
      · exact ih _ (reduceBelowRow_prefixRowsZero A pivot target
          column modulus prefixZero)
      · exact ih A prefixZero

theorem reduceBelow_apply_of_not_mem {m n : Nat}
    (pivot row : Fin m) (rowNotPivot : row ≠ pivot)
    (column currentColumn : Fin n) (modulus : Int)
    (rows : List (Fin m)) (rowNotMem : row ∉ rows)
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (reduceBelow pivot column modulus rows A).1 row currentColumn =
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
      unfold reduceBelow
      split
      · calc
          (reduceBelow pivot column modulus tail
              (reduceBelowRow A pivot target column modulus).1).1
                row currentColumn =
              (reduceBelowRow A pivot target column modulus).1
                row currentColumn :=
            ih rowNotTail _
          _ = A row currentColumn :=
            reduceBelowRow_apply_of_other A pivot target row rowNotPivot
              rowNotTarget column currentColumn modulus
      · exact ih rowNotTail A

theorem reduceBelow_apply_before {m n : Nat}
    (pivot row : Fin m) (column currentColumn : Fin n)
    (modulus : Int) (before : currentColumn < column)
    (rows : List (Fin m)) (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (reduceBelow pivot column modulus rows A).1 row currentColumn =
      A row currentColumn := by
  induction rows generalizing A with
  | nil => rfl
  | cons target tail ih =>
      unfold reduceBelow
      split
      · calc
          (reduceBelow pivot column modulus tail
              (reduceBelowRow A pivot target column modulus).1).1
                row currentColumn =
              (reduceBelowRow A pivot target column modulus).1
                row currentColumn := ih _
          _ = A row currentColumn :=
            reduceBelowRow_apply_before A pivot target row column
              currentColumn modulus before
      · exact ih A

theorem reduceBelow_mem_column_zero {m n : Nat}
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (modulusPositive : 0 < modulus)
    (rows : List (Fin m)) (rowsNodup : rows.Nodup)
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (rowMem : row ∈ rows) (pivotBeforeRow : pivot < row) :
    (reduceBelow pivot column modulus rows A).1 row column = 0 := by
  induction rows generalizing A with
  | nil => simp at rowMem
  | cons target tail ih =>
      have targetNotTail : target ∉ tail :=
        (List.nodup_cons.mp rowsNodup).1
      have tailNodup := (List.nodup_cons.mp rowsNodup).2
      rcases List.mem_cons.mp rowMem with rowEq | rowInTail
      · subst row
        unfold reduceBelow
        rw [if_pos pivotBeforeRow]
        calc
          (reduceBelow pivot column modulus tail
              (reduceBelowRow A pivot target column modulus).1).1
                target column =
              (reduceBelowRow A pivot target column modulus).1
                target column :=
            reduceBelow_apply_of_not_mem pivot target pivotBeforeRow.ne'
              column column modulus tail targetNotTail _
          _ = 0 := reduceBelowRow_target_column_zero A pivot target
            pivotBeforeRow.ne column modulus modulusPositive
      · unfold reduceBelow
        split
        · exact ih tailNodup _ rowInTail
        · exact ih tailNodup A rowInTail

/-- After visiting every row, all entries strictly below the pivot are zero. -/
theorem reduceBelow_finRange_column_zero {m n : Nat}
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (modulusPositive : 0 < modulus)
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    ∀ row, pivot < row →
      (reduceBelow pivot column modulus (List.finRange m) A).1
        row column = 0 := by
  intro row pivotBeforeRow
  exact reduceBelow_mem_column_zero pivot column modulus modulusPositive
    (List.finRange m) (List.nodup_finRange m) A row
    (List.mem_finRange row) pivotBeforeRow

/-- The complete below-pivot loop preserves the live augmented row lattice. -/
theorem reduceBelow_augmentedRowSpan {m n : Nat}
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (rows : List (Fin m)) (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivotAtColumn : pivot.val = column.val)
    (prefixZero : PrefixRowsZero A column.val) :
    augmentedRowSpan
        (reduceBelow pivot column modulus rows A).1 modulus column.val =
      augmentedRowSpan A modulus column.val := by
  induction rows generalizing A with
  | nil => rfl
  | cons target tail ih =>
      unfold reduceBelow
      split
      · rename_i pivotBeforeTarget
        let current := reduceBelowRow A pivot target column modulus
        have pairPrefix :
            ∀ row, row = pivot ∨ row = target →
              ∀ currentColumn, currentColumn < column →
                A row currentColumn = 0 := by
          intro row rowCase currentColumn currentBefore
          apply prefixZero row
          · rcases rowCase with rfl | rfl
            · simp [pivotAtColumn]
            · exact (pivotAtColumn ▸ pivotBeforeTarget.le)
          · exact currentBefore
        have currentSpan :
            augmentedRowSpan current.1 modulus column.val =
              augmentedRowSpan A modulus column.val :=
          reduceBelowRow_augmentedRowSpan A pivot target
            pivotBeforeTarget.ne column modulus pairPrefix
        have currentPrefix : PrefixRowsZero current.1 column.val :=
          reduceBelowRow_prefixRowsZero A pivot target column modulus prefixZero
        exact (ih current.1 currentPrefix).trans currentSpan
      · exact ih A prefixZero

end Internal

end NormalForms.Research.ModularHNF
