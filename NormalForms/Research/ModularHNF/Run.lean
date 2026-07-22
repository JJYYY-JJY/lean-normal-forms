/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Stage
import all NormalForms.Research.ModularHNF.Stage

/-!
# Shape invariant for the complete modular-HNF run

`runColumns` consumes the canonical `Fin` enumeration from left to right.  A
run invariant records the zero prefix, the local HNF obligations of every
processed column, and positivity of the live modulus.  Later stages preserve
earlier columns literally, so the one-stage theorem lifts without any
determinant assumption.
-/

public section

namespace NormalForms.Research.ModularHNF

/-- Columns already put into local HNF shape. -/
@[expose] def ProcessedHermiteShape {m n : Nat}
    (columns_le_rows : n ≤ m)
    (A : _root_.Matrix (Fin m) (Fin n) Int) (processed : Nat) : Prop :=
  ∀ column, column.val < processed →
    ColumnHermiteShape A (Fin.castLE columns_le_rows column) column

/-- Inductive characterization of a consecutive list of canonical columns. -/
inductive ConsecutiveFrom {n : Nat} : Nat → List (Fin n) → Prop
  | nil (start : Nat) : ConsecutiveFrom start []
  | cons (start : Nat) (column : Fin n) (tail : List (Fin n))
      (head_value : column.val = start)
      (tail_consecutive : ConsecutiveFrom (start + 1) tail) :
      ConsecutiveFrom start (column :: tail)

namespace ConsecutiveFrom

theorem map_succ {n start : Nat} {columns : List (Fin n)}
    (consecutive : ConsecutiveFrom start columns) :
    ConsecutiveFrom (start + 1) (columns.map Fin.succ) := by
  induction consecutive with
  | nil start => exact ConsecutiveFrom.nil (start + 1)
  | cons start column tail headValue tailConsecutive ih =>
      apply ConsecutiveFrom.cons
      · simp [headValue]
      · simpa [Nat.add_assoc] using ih

theorem finRange (n : Nat) :
    ConsecutiveFrom 0 (List.finRange n) := by
  induction n with
  | zero => exact ConsecutiveFrom.nil 0
  | succ n ih =>
      rw [List.finRange_succ]
      apply ConsecutiveFrom.cons
      · rfl
      · simpa using map_succ ih

end ConsecutiveFrom

/-- State carried through the left-to-right column loop. -/
structure RunInvariant {m n : Nat} (columns_le_rows : n ≤ m)
    (state : RawModularRun m n) (processed : Nat) : Prop where
  prefix_zero : PrefixRowsZero state.candidate processed
  processed_shape :
    ProcessedHermiteShape columns_le_rows state.candidate processed
  modulus_positive : 0 < state.finalModulus

namespace Internal

theorem stage_runInvariant {m n : Nat}
    (columns_le_rows : n ≤ m) (state : RawModularRun m n)
    (processed : Nat) (column : Fin n) (columnValue : column.val = processed)
    (invariant : RunInvariant columns_le_rows state processed) :
    RunInvariant columns_le_rows
      (stage columns_le_rows state column) (processed + 1) := by
  have stageSpec := stage_shape columns_le_rows state column
    invariant.modulus_positive (by
      simpa [columnValue] using invariant.prefix_zero)
  refine
    { prefix_zero := by
        simpa [columnValue] using stageSpec.1
      processed_shape := ?_
      modulus_positive := stageSpec.2.2 }
  intro currentColumn currentBeforeNext
  by_cases previouslyProcessed : currentColumn.val < processed
  · have currentBeforeColumn : currentColumn < column := by
      change currentColumn.val < column.val
      omega
    exact ColumnHermiteShape.of_column_eq
      (invariant.processed_shape currentColumn previouslyProcessed)
      (fun row => stage_candidate_apply_before columns_le_rows state column
        currentColumn currentBeforeColumn row)
  · have currentEq : currentColumn = column := by
      apply Fin.ext
      omega
    subst currentColumn
    exact stageSpec.2.1

theorem runColumns_runInvariant {m n : Nat}
    (columns_le_rows : n ≤ m) (columns : List (Fin n))
    (state : RawModularRun m n) (processed : Nat)
    (consecutive : ConsecutiveFrom processed columns)
    (invariant : RunInvariant columns_le_rows state processed) :
    RunInvariant columns_le_rows
      (runColumns columns_le_rows columns state)
      (processed + columns.length) := by
  induction consecutive generalizing state with
  | nil start => simpa [runColumns] using invariant
  | cons start column tail columnValue tailConsecutive ih =>
      have nextInvariant := stage_runInvariant columns_le_rows state start
        column columnValue invariant
      have finalInvariant := ih (stage columns_le_rows state column) nextInvariant
      simpa [runColumns, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        finalInvariant

/-- Every positive-modulus raw run has HNF shape and retains a positive modulus. -/
theorem runRaw_shape {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int) (modulusPositive : 0 < modulus) :
    let result := runRaw A columns_le_rows modulus
    PrefixRowsZero result.candidate n ∧
      (∀ column,
        ColumnHermiteShape result.candidate
          (Fin.castLE columns_le_rows column) column) ∧
      0 < result.finalModulus := by
  let initial : RawModularRun m n :=
    { candidate := A
      finalModulus := modulus
      stages := []
      operations := {} }
  have initialInvariant : RunInvariant columns_le_rows initial 0 :=
    { prefix_zero := by
        intro _ _ column before
        omega
      processed_shape := by
        intro _ before
        omega
      modulus_positive := modulusPositive }
  have finalInvariant := runColumns_runInvariant columns_le_rows
    (List.finRange n) initial 0 (ConsecutiveFrom.finRange n) initialInvariant
  have lengthEq : (List.finRange n).length = n := List.length_finRange
  change PrefixRowsZero
      (runColumns columns_le_rows (List.finRange n) initial).candidate n ∧
    (∀ column,
      ColumnHermiteShape
        (runColumns columns_le_rows (List.finRange n) initial).candidate
        (Fin.castLE columns_le_rows column) column) ∧
    0 < (runColumns columns_le_rows (List.finRange n) initial).finalModulus
  constructor
  · simpa [lengthEq] using finalInvariant.prefix_zero
  · constructor
    · intro column
      exact finalInvariant.processed_shape column (by simp [lengthEq])
    · exact finalInvariant.modulus_positive

end Internal

end NormalForms.Research.ModularHNF
