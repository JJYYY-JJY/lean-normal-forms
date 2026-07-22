/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.Search

/-!
# Certified Clearing of a Divisible Smith Pivot Column

When every entry below a nonzero pivot is divisible by that pivot, Step 4 does
not need an extended-gcd pass.  One simultaneous lower shear clears the whole
column.  This module stores the shear and its negation as explicit inverses and
proves the exact entries used by the total stabilization loop.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms
open NormalForms.Matrix.Certificates

/-- Lower shear that adds `coefficients row` times row zero to `row.succ`. -/
@[expose] public def firstColumnShear {n : Nat}
    (coefficients : Fin n → Int) :
    _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int :=
  fun row column =>
    Fin.cases
      (Fin.cases 1 (fun _ => 0) column)
      (fun row' => Fin.cases (coefficients row')
        (fun column' =>
          (1 : _root_.Matrix (Fin n) (Fin n) Int) row' column') column)
      row

@[simp] public theorem firstColumnShear_zero_zero {n : Nat}
    (coefficients : Fin n → Int) :
    firstColumnShear coefficients 0 0 = 1 :=
  rfl

@[simp] public theorem firstColumnShear_zero_succ {n : Nat}
    (coefficients : Fin n → Int) (column : Fin n) :
    firstColumnShear coefficients 0 column.succ = 0 :=
  rfl

@[simp] public theorem firstColumnShear_succ_zero {n : Nat}
    (coefficients : Fin n → Int) (row : Fin n) :
    firstColumnShear coefficients row.succ 0 = coefficients row :=
  rfl

@[simp] public theorem firstColumnShear_succ_succ {n : Nat}
    (coefficients : Fin n → Int) (row column : Fin n) :
    firstColumnShear coefficients row.succ column.succ =
      (1 : _root_.Matrix (Fin n) (Fin n) Int) row column :=
  rfl

public theorem firstColumnShear_mul_neg {n : Nat}
    (coefficients : Fin n → Int) :
    firstColumnShear coefficients * firstColumnShear (-coefficients) = 1 := by
  ext row column
  cases row using Fin.cases with
  | zero =>
      cases column using Fin.cases with
      | zero =>
          simp [_root_.Matrix.mul_apply, Fin.sum_univ_succ]
      | succ column =>
          have hne : (0 : Fin (n + 1)) ≠ column.succ :=
            fun h => Fin.succ_ne_zero column h.symm
          simp [_root_.Matrix.mul_apply, Fin.sum_univ_succ,
            _root_.Matrix.one_apply, hne]
  | succ row =>
      cases column using Fin.cases with
      | zero =>
          simp [_root_.Matrix.mul_apply, Fin.sum_univ_succ,
            _root_.Matrix.one_apply]
      | succ column =>
          simp [_root_.Matrix.mul_apply, Fin.sum_univ_succ,
            _root_.Matrix.one_apply]

public theorem firstColumnShear_neg_mul {n : Nat}
    (coefficients : Fin n → Int) :
    firstColumnShear (-coefficients) * firstColumnShear coefficients = 1 := by
  simpa only [neg_neg] using firstColumnShear_mul_neg (-coefficients)

/-- Explicit inverse certificate for the simultaneous row shear. -/
@[expose] public def firstColumnShearCertificate {n : Nat}
    (coefficients : Fin n → Int) :
    MatrixInverseCertificate (firstColumnShear coefficients) :=
  { inverse := firstColumnShear (-coefficients)
    left_inv := firstColumnShear_neg_mul coefficients
    right_inv := firstColumnShear_mul_neg coefficients }

public theorem firstColumnShear_mul_apply_zero {n : Nat}
    (coefficients : Fin n → Int)
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (column : Fin (n + 1)) :
    (firstColumnShear coefficients * A) 0 column = A 0 column := by
  simp [_root_.Matrix.mul_apply, Fin.sum_univ_succ]

public theorem firstColumnShear_mul_apply_succ {n : Nat}
    (coefficients : Fin n → Int)
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (row : Fin n) (column : Fin (n + 1)) :
    (firstColumnShear coefficients * A) row.succ column =
      coefficients row * A 0 column + A row.succ column := by
  simp [_root_.Matrix.mul_apply, Fin.sum_univ_succ,
    _root_.Matrix.one_apply]

/-- Executable quotient used to clear one divisible below-pivot entry. -/
@[expose] public def firstColumnClearCoefficient {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (row : Fin n) : Int :=
  -ComputableEuclideanOps.quot (A row.succ 0) (A 0 0)

/-- Clear all divisible first-column entries in one certified row shear. -/
@[expose] public def clearDivisibleFirstColumn {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    TwoSidedCertificate A :=
  let coefficients := firstColumnClearCoefficient A
  { U := firstColumnShear coefficients
    U_cert := firstColumnShearCertificate coefficients
    result := firstColumnShear coefficients * A
    V := 1
    V_cert := MatrixInverseCertificate.one
    equation := by rw [_root_.Matrix.mul_one] }

public theorem clearDivisibleFirstColumn_apply_zero {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (column : Fin (n + 1)) :
    (clearDivisibleFirstColumn A).result 0 column = A 0 column := by
  exact firstColumnShear_mul_apply_zero
    (firstColumnClearCoefficient A) A column

@[simp] public theorem clearDivisibleFirstColumn_pivot {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (clearDivisibleFirstColumn A).result 0 0 = A 0 0 :=
  clearDivisibleFirstColumn_apply_zero A 0

public theorem clearDivisibleFirstColumn_apply_succ {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (row : Fin n) (column : Fin (n + 1)) :
    (clearDivisibleFirstColumn A).result row.succ column =
      firstColumnClearCoefficient A row * A 0 column +
        A row.succ column := by
  exact firstColumnShear_mul_apply_succ
    (firstColumnClearCoefficient A) A row column

/-- Every divisible below-pivot entry is cleared exactly. -/
public theorem clearDivisibleFirstColumn_apply_succ_zero {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (row : Fin n) (hdiv : A 0 0 ∣ A row.succ 0) :
    (clearDivisibleFirstColumn A).result row.succ 0 = 0 := by
  rw [clearDivisibleFirstColumn_apply_succ]
  simp [firstColumnClearCoefficient, ComputableEuclideanOps.quot_eq,
    Int.ediv_mul_cancel hdiv]

public theorem clearDivisibleFirstColumn_firstColumnCleared {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0) :
    FirstColumnCleared (clearDivisibleFirstColumn A).result :=
  fun row => clearDivisibleFirstColumn_apply_succ_zero A row (hdiv row)

public theorem clearDivisibleFirstColumn_firstRowCleared {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hrow : FirstRowCleared A) :
    FirstRowCleared (clearDivisibleFirstColumn A).result := by
  intro column
  rw [clearDivisibleFirstColumn_apply_zero]
  exact hrow column

/-- With a cleared first row, the shear does not alter the lower-right block. -/
public theorem clearDivisibleFirstColumn_lowerRight {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hrow : FirstRowCleared A) (row column : Fin n) :
    (clearDivisibleFirstColumn A).result row.succ column.succ =
      A row.succ column.succ := by
  rw [clearDivisibleFirstColumn_apply_succ, hrow column]
  simp

/-- Step-7 injection preserves the pivot when the first row is cleared. -/
public theorem injectLowerWitness_pivot {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (column : Fin n) (hrow : FirstRowCleared A) :
    (injectLowerWitness A column).result 0 0 = A 0 0 := by
  simp [injectLowerWitness,
    NormalForms.Matrix.Elementary.applyColumnOperation, hrow column]

/-- Step-7 injection does not disturb a cleared first row. -/
public theorem injectLowerWitness_firstRowCleared {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (column : Fin n) (hrow : FirstRowCleared A) :
    FirstRowCleared (injectLowerWitness A column).result := by
  intro target
  simp [injectLowerWitness,
    NormalForms.Matrix.Elementary.applyColumnOperation, hrow target]

end NormalForms.Research.KannanBachem.Smith
