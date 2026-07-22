/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Lattice
import all NormalForms.Research.ModularHNF.Lattice

/-!
# Determinant-modulus lattice containment

The determinant contract is strong enough to place every modular coordinate
generator in the original row lattice.  The proof is constructive: the
adjugate of the selected nonsingular square minor writes `det(B) e_j` as an
integer combination of selected rows, and the divisibility witness scales
that combination to the supplied modulus.
-/

public section

namespace NormalForms.Research.ModularHNF

open scoped BigOperators Matrix

/-- A selected square minor expresses `det(B) e_j` in the original row lattice. -/
public theorem selectedMinorDet_smul_single_mem_rowSpan {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A) (column : Fin n) :
    (selectedSquareMinor A fullRank.rows).det •
        Pi.single column (1 : Int) ∈ rowSpan A := by
  let B := selectedSquareMinor A fullRank.rows
  have equality :
      B.det • Pi.single column (1 : Int) =
        ∑ row : Fin n, B.adjugate column row • A.row (fullRank.rows row) := by
    ext currentColumn
    have entry := congrArg
      (fun M : _root_.Matrix (Fin n) (Fin n) Int => M column currentColumn)
      (_root_.Matrix.adjugate_mul B)
    simpa [B, selectedSquareMinor, _root_.Matrix.mul_apply,
      Pi.single_apply, _root_.Matrix.one_apply, smul_eq_mul, eq_comm] using entry.symm
  rw [equality]
  exact Submodule.sum_mem _ fun row _ =>
    Submodule.smul_mem _ _ (row_mem_rowSpan A (fullRank.rows row))

/-- Every supplied determinant-modulus coordinate generator lies in the input row lattice. -/
public theorem determinantModulus_smul_single_mem_rowSpan {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) (column : Fin n) :
    witness.modulus • Pi.single column (1 : Int) ∈ rowSpan A := by
  have determinantMem :=
    selectedMinorDet_smul_single_mem_rowSpan A fullRank column
  have divides : (selectedSquareMinor A fullRank.rows).det ∣ witness.modulus :=
    Int.natAbs_dvd_natAbs.mp witness.selectedMinor_dvd
  rcases divides with ⟨coefficient, equality⟩
  simpa [equality, mul_smul, mul_comm] using
    Submodule.smul_mem (rowSpan A) coefficient determinantMem

/-- The entire live modular suffix is already contained in the input row lattice. -/
public theorem determinantModulus_suffixModule_le_rowSpan {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) (k : Nat) :
    suffixModule witness.modulus k ≤ rowSpan A := by
  rw [suffixModule, Submodule.span_le]
  rintro _ ⟨column, rfl⟩
  exact determinantModulus_smul_single_mem_rowSpan A fullRank witness column.1

/-- Initially, adding any determinant-modulus suffix basis does not enlarge the row lattice. -/
public theorem determinantModulus_augmentedRowSpan_eq {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) (k : Nat) :
    augmentedRowSpan A witness.modulus k = rowSpan A := by
  exact sup_eq_left.mpr
    (determinantModulus_suffixModule_le_rowSpan A fullRank witness k)

end NormalForms.Research.ModularHNF
