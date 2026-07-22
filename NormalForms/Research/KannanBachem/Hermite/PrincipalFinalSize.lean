/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalCorrectness
public import NormalForms.Research.KannanBachem.Hermite.CoefficientSize
import all NormalForms.Research.KannanBachem.Hermite.PrincipalCorrectness
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Int.Order.Units

/-!
# Size of the principal HNF result and its multiplier

These are endpoint bounds, not yet bounds for every intermediate state.  They
form the reset estimate needed by the stagewise Kannan--Bachem argument.
-/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix BigOperators
open NormalForms.Matrix.Certificates

namespace Principal

theorem PrefixHermite.matrixHeight_le_det_natAbs {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (hprefix : PrefixHermite n A)
    (diagonal_ne : ∀ row, A row row ≠ 0) :
    matrixHeight A ≤ A.det.natAbs := by
  have upper : A.BlockTriangular id := by
    intro row column hcolumn
    exact hprefix.below row column row.isLt hcolumn
  have diagonal_one_le : ∀ row : Fin n, 1 ≤ (A row row).natAbs :=
    fun row => Int.natAbs_pos.mpr (diagonal_ne row)
  have diagonal_le_det : ∀ row : Fin n, (A row row).natAbs ≤ A.det.natAbs := by
    intro row
    have diagonal_le_product :
        (A row row).natAbs ≤ ∏ index : Fin n, (A index index).natAbs :=
      Finset.single_le_prod'
        (fun index _ => diagonal_one_le index) (Finset.mem_univ row)
    have det_abs_eq :
        A.det.natAbs = ∏ index : Fin n, (A index index).natAbs := by
      rw [_root_.Matrix.det_of_upperTriangular upper]
      change Int.natAbsHom (∏ index : Fin n, A index index) = _
      exact map_prod Int.natAbsHom
        (fun index : Fin n => A index index) Finset.univ
    exact diagonal_le_product.trans_eq det_abs_eq.symm
  apply matrixHeight_le
  intro row column
  rcases lt_trichotomy row column with hlt | heq | hgt
  · have remainder_le :
        (A row column % A column column).natAbs ≤
          (A column column).natAbs := by
      have nonnegative := Int.emod_nonneg (A row column) (diagonal_ne column)
      have strict := Int.emod_lt_abs (A row column) (diagonal_ne column)
      have remainder_abs_le :
          |A row column % A column column| ≤ |A column column| := by
        rw [abs_of_nonneg nonnegative]
        exact strict.le
      apply Int.ofNat_le.mp
      simpa only [Int.natCast_natAbs] using remainder_abs_le
    rw [hprefix.reduced row column column.isLt hlt]
    exact remainder_le.trans (diagonal_le_det column)
  · subst column
    exact diagonal_le_det row
  · rw [hprefix.below row column row.isLt hgt]
    exact Nat.zero_le _

end Principal

/-- The returned principal HNF is no taller than the input determinant. -/
public theorem principal_result_height_le_input_det {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (det_ne : A.det ≠ 0) :
    matrixHeight (principalRun A).matrix ≤ A.det.natAbs := by
  change matrixHeight (Principal.compute A).transform.B ≤ A.det.natAbs
  have final_le := (Principal.compute_prefix A).matrixHeight_le_det_natAbs
    (Principal.compute_diagonal_ne A det_ne)
  have unitDet : IsUnit (Principal.compute A).transform.U.det :=
    (Principal.compute A).transform.U_cert.unimodular
  have det_abs_eq :
      (Principal.compute A).transform.B.det.natAbs = A.det.natAbs := by
    rw [← (Principal.compute A).transform.equation,
      _root_.Matrix.det_mul, Int.natAbs_mul,
      Int.isUnit_iff_natAbs_eq.mp unitDet, one_mul]
  exact final_le.trans_eq det_abs_eq

/-- The returned HNF's coefficient length is bounded by the determinant length. -/
public theorem principal_result_bitLength_le_input_det {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (det_ne : A.det ≠ 0) :
    matrixBitLength (principalRun A).matrix ≤ integerBitLength A.det := by
  exact Nat.size_le_size (principal_result_height_le_input_det A det_ne)

/-- The returned HNF has an explicit polynomial coefficient-length bound. -/
public theorem principal_result_bitLength_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (det_ne : A.det ≠ 0) :
    matrixBitLength (principalRun A).matrix ≤
      determinantBitLengthBound n (matrixBitLength A) :=
  (principal_result_bitLength_le_input_det A det_ne).trans
    (determinant_bitLength_le A)

/-- Closed endpoint bound for the accumulated principal multiplier. -/
@[expose] public def principalMultiplierBitLengthBound
    (n inputBits determinantBits : Nat) : Nat :=
  match n with
  | 0 => 0
  | order + 1 =>
      Nat.size (order + 1) + determinantBits +
        determinantBitLengthBound order inputBits

/-- The final explicit multiplier satisfies the Cramer's-rule endpoint bound. -/
public theorem principal_multiplier_bitLength_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (det_ne : A.det ≠ 0) :
    matrixBitLength (principalRun A).steps.accumulator ≤
      principalMultiplierBitLengthBound n (matrixBitLength A)
        (integerBitLength A.det) := by
  cases n with
  | zero =>
      have hzero : (principalRun A).steps.accumulator =
          (0 : _root_.Matrix (Fin 0) (Fin 0) Int) :=
        Subsingleton.elim _ _
      rw [hzero, matrixBitLength_zero]
      rfl
  | succ order =>
      change matrixBitLength (Principal.compute A).transform.steps.accumulator ≤ _
      rw [(Principal.compute A).transform.accumulator_eq]
      have multiplier := leftMultiplier_bitLength_le_of_mul_eq
        A (Principal.compute A).transform.U
        (Principal.compute A).transform.B
        (Principal.compute A).transform.equation det_ne
      exact multiplier.trans <| by
        have resultBits := principal_result_bitLength_le_input_det A det_ne
        change matrixBitLength (Principal.compute A).transform.B ≤
          integerBitLength A.det at resultBits
        simp only [principalMultiplierBitLengthBound]
        omega

end NormalForms.Research.KannanBachem.Hermite
