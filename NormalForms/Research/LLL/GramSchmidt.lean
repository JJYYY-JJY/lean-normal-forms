/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.Parameters
public import NormalForms.Matrix.Constructive

/-!
# Exact rational Gram--Schmidt data

Rows are integer lattice vectors.  This module casts them to `Rat` and
computes the unnormalised Gram--Schmidt vectors directly.  Keeping the
orthogonal vectors unnormalised avoids square roots and makes the complete
predicate executable.
-/

@[expose] public section

namespace NormalForms.Research.LLL

open scoped BigOperators

/-- The standard exact dot product on rational coordinate vectors. -/
public def dot {n : Nat} (left right : Fin n -> Rat) : Rat :=
  ∑ column, left column * right column

/-- Cast one integer matrix row to an exact rational vector. -/
public def rationalRow {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (row : Fin m) : Fin n -> Rat :=
  fun column => basis row column

/-- Squared length for the exact dot product. -/
public def normSq {n : Nat} (vector : Fin n -> Rat) : Rat :=
  dot vector vector

/-- One projection coefficient onto a nonnormalised orthogonal vector. -/
public def projectionCoefficient {n : Nat}
    (vector orthogonal : Fin n -> Rat) : Rat :=
  dot vector orthogonal / normSq orthogonal

/--
The unnormalised Gram--Schmidt vector at a natural row index.  Indices outside
the matrix are mapped to zero; recursive calls only use strictly earlier rows.
-/
public def gramSchmidtAux {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (row : Nat) : Fin n -> Rat :=
  if hrow : row < m then
    let current := rationalRow basis ⟨row, hrow⟩
    current -
      ∑ j : Fin row,
        projectionCoefficient current (gramSchmidtAux basis j.1) •
          gramSchmidtAux basis j.1
  else
    0
termination_by row
decreasing_by omega

/-- Exact unnormalised Gram--Schmidt row at a valid matrix index. -/
public def gramSchmidtRow {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (row : Fin m) : Fin n -> Rat :=
  gramSchmidtAux basis row

/-- Squared Gram--Schmidt length. -/
public def gramSchmidtNormSq {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (row : Fin m) : Rat :=
  normSq (gramSchmidtRow basis row)

/-- The exact Gram--Schmidt coefficient `mu_(row,column)`. -/
public def gramSchmidtCoefficient {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (row column : Fin m) : Rat :=
  projectionCoefficient (rationalRow basis row) (gramSchmidtRow basis column)

@[simp] public theorem gramSchmidtAux_of_ge {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (row : Nat) (hrow : m <= row) :
    gramSchmidtAux basis row = 0 := by
  rw [gramSchmidtAux.eq_1]
  simp only [Nat.not_lt_of_ge hrow, dite_false]

public theorem gramSchmidtAux_of_lt {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (row : Nat) (hrow : row < m) :
    gramSchmidtAux basis row =
      rationalRow basis ⟨row, hrow⟩ -
        ∑ j : Fin row,
          projectionCoefficient (rationalRow basis ⟨row, hrow⟩)
              (gramSchmidtAux basis j.1) •
            gramSchmidtAux basis j.1 := by
  rw [gramSchmidtAux.eq_1]
  simp only [hrow, dite_true]

@[simp] public theorem gramSchmidtAux_zero {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (hrows : 0 < m) :
    gramSchmidtAux basis 0 = rationalRow basis ⟨0, hrows⟩ := by
  rw [gramSchmidtAux_of_lt basis 0 hrows]
  simp

@[simp] public theorem dot_zero_left {n : Nat} (vector : Fin n -> Rat) :
    dot 0 vector = 0 := by
  simp [dot]

@[simp] public theorem dot_zero_right {n : Nat} (vector : Fin n -> Rat) :
    dot vector 0 = 0 := by
  simp [dot]

public theorem dot_add_left {n : Nat} (left right vector : Fin n -> Rat) :
    dot (left + right) vector = dot left vector + dot right vector := by
  simp [dot, add_mul, Finset.sum_add_distrib]

public theorem dot_add_right {n : Nat} (vector left right : Fin n -> Rat) :
    dot vector (left + right) = dot vector left + dot vector right := by
  simp [dot, mul_add, Finset.sum_add_distrib]

public theorem dot_smul_left {n : Nat} (coefficient : Rat)
    (left right : Fin n -> Rat) :
    dot (coefficient • left) right = coefficient * dot left right := by
  simp [dot, Finset.mul_sum, mul_assoc]

public theorem dot_smul_right {n : Nat} (coefficient : Rat)
    (left right : Fin n -> Rat) :
    dot left (coefficient • right) = coefficient * dot left right := by
  simp [dot, Finset.mul_sum, mul_left_comm]

public theorem dot_comm {n : Nat} (left right : Fin n -> Rat) :
    dot left right = dot right left := by
  apply Finset.sum_congr rfl
  intro column _
  exact mul_comm _ _

end NormalForms.Research.LLL
