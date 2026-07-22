/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Algorithm
import all NormalForms.Research.ModularHNF.Algorithm

/-!
# Algebraic operation bound for modular HNF

The exact counter stored by the executable DKT kernel counts scalar additions,
multiplications, extended-gcd calls, exact divisions, modular reductions, and
comparisons.  This module proves a closed dimension-only bound for every raw
run, independently of the input entries, modulus validity, or semantic
correctness theorem.
-/

public section

namespace NormalForms.Research.ModularHNF

namespace ModularOperationCount

@[simp] public theorem total_add (left right : ModularOperationCount) :
    (left + right).total = left.total + right.total := by
  simp [total, add]
  omega

@[simp] public theorem total_zero :
    ({} : ModularOperationCount).total = 0 := by
  rfl

end ModularOperationCount

/-- Uniform scalar-operation charge for one processed column. -/
@[expose] public def modularStageOperationBound
    (rows columns : Nat) : Nat :=
  12 * rows * columns + 5 * rows + 3 * columns + 4

/-- Closed scalar-operation budget for the full raw modular-HNF kernel. -/
@[expose] public def modularOperationBound (rows columns : Nat) : Nat :=
  columns * modularStageOperationBound rows columns

namespace Internal

theorem reduceBelowRow_operations_total_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n) (modulus : Int) :
    (reduceBelowRow A pivot target column modulus).2.total ≤
      10 * n + 4 := by
  rw [reduceBelowRow]
  split
  · simp [ModularOperationCount.total]
  · simp only [ModularOperationCount.total]
    omega

theorem reduceBelow_operations_total_le {m n : Nat}
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (targets : List (Fin m))
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (reduceBelow pivot column modulus targets A).2.total ≤
      targets.length * (10 * n + 4) := by
  induction targets generalizing A with
  | nil => simp [reduceBelow]
  | cons target tail ih =>
      rw [reduceBelow]
      split
      · rw [ModularOperationCount.total_add]
        have current := reduceBelowRow_operations_total_le
          A pivot target column modulus
        have rest := ih (reduceBelowRow A pivot target column modulus).1
        simp only [List.length_cons]
        calc
          (reduceBelowRow A pivot target column modulus).2.total +
                (reduceBelow pivot column modulus tail
                  (reduceBelowRow A pivot target column modulus).1).2.total ≤
              (10 * n + 4) + tail.length * (10 * n + 4) :=
            Nat.add_le_add current rest
          _ = (tail.length + 1) * (10 * n + 4) := by ring
      · have rest := ih A
        simp only [List.length_cons]
        exact rest.trans <| Nat.mul_le_mul_right (10 * n + 4)
          (Nat.le_succ tail.length)

theorem stage_operations_total_le {m n : Nat}
    (columns_le_rows : n ≤ m) (state : RawModularRun m n)
    (column : Fin n) :
    (stage columns_le_rows state column).operations.total ≤
      state.operations.total + modularStageOperationBound m n := by
  let pivot : Fin m := Fin.castLE columns_le_rows column
  let modulus := state.finalModulus
  let prepared :=
    if state.candidate pivot column = 0 then
      setEntry state.candidate pivot column modulus
    else
      state.candidate
  let below := reduceBelow pivot column modulus (List.finRange m) prepared
  let fixed : ModularOperationCount :=
    { additions := column.val * (n - column.val)
      multiplications := (n - column.val) + column.val * (n - column.val)
      xgcdCalls := 1
      exactDivisions := column.val + 1
      modularReductions := n - column.val
      comparisons := 2 + (n - column.val) }
  have belowBound : below.2.total ≤ m * (10 * n + 4) := by
    simpa only [below, List.length_finRange] using
      reduceBelow_operations_total_le pivot column modulus
        (List.finRange m) prepared
  have column_le : column.val ≤ n := Nat.le_of_lt column.isLt
  have column_le_m : column.val ≤ m := column_le.trans columns_le_rows
  have width_le : n - column.val ≤ n := Nat.sub_le n column.val
  have product_le : column.val * (n - column.val) ≤ m * n :=
    Nat.mul_le_mul column_le_m width_le
  have fixedEq : fixed.total =
      2 * (column.val * (n - column.val)) +
        3 * (n - column.val) + column.val + 4 := by
    simp [fixed, ModularOperationCount.total]
    ring
  have fixedBound : fixed.total ≤ 2 * m * n + 3 * n + m + 4 := by
    calc
      fixed.total = 2 * (column.val * (n - column.val)) +
          3 * (n - column.val) + column.val + 4 := fixedEq
      _ ≤ 2 * (m * n) + 3 * n + m + 4 := by gcongr
      _ = 2 * m * n + 3 * n + m + 4 := by ring
  rw [stage]
  simp only [ModularOperationCount.total_add]
  change state.operations.total +
      (below.2.total + fixed.total) ≤
      state.operations.total + modularStageOperationBound m n
  calc
    state.operations.total + (below.2.total + fixed.total) ≤
        state.operations.total +
          (m * (10 * n + 4) + (2 * m * n + 3 * n + m + 4)) :=
      Nat.add_le_add_left (Nat.add_le_add belowBound fixedBound) _
    _ = state.operations.total + modularStageOperationBound m n := by
      unfold modularStageOperationBound
      ring

theorem runColumns_operations_total_le {m n : Nat}
    (columns_le_rows : n ≤ m) (columns : List (Fin n))
    (state : RawModularRun m n) :
    (runColumns columns_le_rows columns state).operations.total ≤
      state.operations.total +
        columns.length * modularStageOperationBound m n := by
  induction columns generalizing state with
  | nil => simp [runColumns]
  | cons column tail ih =>
      rw [runColumns]
      have stageBound := stage_operations_total_le columns_le_rows state column
      have tailBound := ih (stage columns_le_rows state column)
      simp only [List.length_cons]
      calc
        (runColumns columns_le_rows tail
              (stage columns_le_rows state column)).operations.total ≤
            (stage columns_le_rows state column).operations.total +
              tail.length * modularStageOperationBound m n := tailBound
        _ ≤ (state.operations.total + modularStageOperationBound m n) +
              tail.length * modularStageOperationBound m n :=
            Nat.add_le_add_right stageBound _
        _ = state.operations.total +
              (tail.length + 1) * modularStageOperationBound m n := by ring

end Internal

/-- Every raw execution stays within the closed scalar-operation budget. -/
public theorem runRaw_operations_total_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int) :
    (runRaw A columns_le_rows modulus).operations.total ≤
      modularOperationBound m n := by
  unfold runRaw modularOperationBound
  have bound := Internal.runColumns_operations_total_le columns_le_rows
    (List.finRange n)
    ({ candidate := A
       finalModulus := modulus
       stages := []
       operations := {} } : RawModularRun m n)
  simpa using bound

/-- The checked determinant-modulus entry inherits the raw operation bound. -/
public theorem runWithDeterminantWitness_operations_total_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (modulus : DeterminantModulusWitness A fullRank) :
    (runWithDeterminantWitness A fullRank modulus).operations.total ≤
      modularOperationBound m n := by
  exact runRaw_operations_total_le A fullRank.columns_le_rows modulus.modulus

end NormalForms.Research.ModularHNF
