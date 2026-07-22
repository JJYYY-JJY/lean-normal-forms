/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Lattice
import all NormalForms.Research.ModularHNF.Algorithm
import all NormalForms.Matrix.Hermite.Bezout
import all NormalForms.Matrix.Elementary.Basic

/-!
# Lattice semantics of the modular matrix transitions

The first transition family consists of a unimodular row operation followed
by replacing suffix entries with congruent centered representatives.  These
lemmas prove that such transitions preserve the augmented row lattice.
-/

public section

namespace NormalForms.Research.ModularHNF

open scoped Matrix
open NormalForms
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

/-- Rows at and below `k` vanish in every already processed column. -/
@[expose] public def PrefixRowsZero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (k : Nat) : Prop :=
  ∀ row, k ≤ row.val → ∀ column, column.val < k → A row column = 0

namespace Internal

/-- The full-size two-row Bézout transform used by one modular reduction. -/
def pairTransform {m : Nat} (pivot target : Fin m) (a b : Int) :
    _root_.Matrix (Fin m) (Fin m) Int :=
  twoRowLiftMatrix pivot target (bezoutReductionMatrix a b)

def pairTransformCertificate {m : Nat}
    (pivot target : Fin m) (hne : pivot ≠ target) (a b : Int) :
    MatrixInverseCertificate (pairTransform pivot target a b) :=
  { inverse := twoRowLiftMatrix pivot target (bezoutReductionInverseMatrix a b)
    left_inv := by
      rw [pairTransform, twoRowLiftMatrix_mul pivot target hne,
        bezoutReductionInverseMatrix_mul,
        twoRowLiftMatrix_one pivot target hne]
    right_inv := by
      rw [pairTransform, twoRowLiftMatrix_mul pivot target hne,
        bezoutReductionMatrix_mul_inverse,
        twoRowLiftMatrix_one pivot target hne] }

@[simp] theorem setEntry_apply_same {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (column : Fin n) (value : Int) :
    setEntry A row column value row column = value := by
  simp [setEntry]

@[simp] theorem setEntry_apply_of_row_ne {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row target : Fin m) (column current : Fin n) (value : Int)
    (hne : target ≠ row) :
    setEntry A row column value target current = A target current := by
  simp [setEntry, hne]

@[simp] theorem setEntry_apply_of_column_ne {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (column current : Fin n) (value : Int)
    (hne : current ≠ column) :
    setEntry A row column value row current = A row current := by
  simp [setEntry, hne]

theorem setEntry_congruent_of_zero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (column : Fin n) (modulus : Int)
    (zero : A row column = 0) :
    RowsCongruentOnSuffix (setEntry A row column modulus) A
      modulus column.val := by
  intro currentRow
  apply mem_suffixModule_of_coordinates
  · intro currentColumn before
    have columnNe : currentColumn ≠ column := by
      intro equality
      subst currentColumn
      exact Nat.lt_irrefl _ before
    by_cases rowEq : currentRow = row
    · subst currentRow
      simp [setEntry_apply_of_column_ne, columnNe]
    · simp [setEntry_apply_of_row_ne, rowEq]
  · intro currentColumn _after
    by_cases rowEq : currentRow = row
    · subst currentRow
      by_cases columnEq : currentColumn = column
      · subst currentColumn
        simp [zero]
      · simp [setEntry_apply_of_column_ne, columnEq]
    · simp [setEntry_apply_of_row_ne, rowEq]

theorem setEntry_augmentedRowSpan_of_zero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (column : Fin n) (modulus : Int)
    (zero : A row column = 0) :
    augmentedRowSpan (setEntry A row column modulus) modulus column.val =
      augmentedRowSpan A modulus column.val :=
  augmentedRowSpan_eq_of_congruent
    (setEntry_congruent_of_zero A row column modulus zero)

theorem replacePairSuffix_congruent {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (hne : pivot ≠ target)
    (column : Fin n) (modulus : Int)
    (targetNonzero : A target column ≠ 0)
    (prefixZero :
      ∀ row, row = pivot ∨ row = target →
        ∀ currentColumn, currentColumn < column → A row currentColumn = 0) :
    let gcdData := ComputableEuclideanOps.xgcd
      (A pivot column) (A target column)
    RowsCongruentOnSuffix
      (replacePairSuffix A pivot target column modulus
        gcdData.leftCoeff gcdData.rightCoeff
        (A pivot column / gcdData.gcd)
        (A target column / gcdData.gcd))
      (pairTransform pivot target (A pivot column) (A target column) * A)
      modulus column.val := by
  let gcdData := ComputableEuclideanOps.xgcd
    (A pivot column) (A target column)
  let result := replacePairSuffix A pivot target column modulus
    gcdData.leftCoeff gcdData.rightCoeff
    (A pivot column / gcdData.gcd) (A target column / gcdData.gcd)
  let transform := pairTransform pivot target (A pivot column) (A target column)
  change RowsCongruentOnSuffix result (transform * A) modulus column.val
  have gcdNonzero : gcdData.gcd ≠ 0 := by
    intro gcdZero
    have bothZero :=
      (ComputableEuclideanOps.xgcd_gcd_eq_zero_iff
        (A pivot column) (A target column)).mp gcdZero
    exact targetNonzero bothZero.2
  have gcdBool : ComputableEuclideanOps.isZeroB gcdData.gcd ≠ true :=
    fun equality => gcdNonzero
      ((ComputableEuclideanOps.isZeroB_eq_true_iff _).mp equality)
  have gcdBool' :
      ComputableEuclideanOps.isZeroB
          (ComputableEuclideanOps.xgcd
            (A pivot column) (A target column)).gcd ≠ true := by
    simpa [gcdData] using gcdBool
  intro row
  apply mem_suffixModule_of_coordinates
  · intro currentColumn before
    have currentBefore : currentColumn < column := by
      exact before
    change result row currentColumn - (transform * A) row currentColumn = 0
    by_cases rowPivot : row = pivot
    · subst row
      have pivotZero := prefixZero pivot (Or.inl rfl) currentColumn currentBefore
      have targetZero := prefixZero target (Or.inr rfl) currentColumn currentBefore
      simp [result, transform, pairTransform, replacePairSuffix, currentBefore,
        twoRowLiftMatrix_mul_apply_pivot, hne, bezoutReductionMatrix,
        pivotZero, targetZero]
    · by_cases rowTarget : row = target
      · subst row
        have pivotZero := prefixZero pivot (Or.inl rfl) currentColumn currentBefore
        have targetZero := prefixZero target (Or.inr rfl) currentColumn currentBefore
        simp [result, transform, pairTransform, replacePairSuffix, currentBefore,
          twoRowLiftMatrix_mul_apply_target, bezoutReductionMatrix,
          pivotZero, targetZero]
      · simp [result, transform, pairTransform, replacePairSuffix, currentBefore,
          twoRowLiftMatrix_mul_apply_other, rowPivot, rowTarget]
  · intro currentColumn after
    have currentNotBefore : ¬ currentColumn < column := not_lt_of_ge after
    change modulus ∣ result row currentColumn - (transform * A) row currentColumn
    by_cases rowPivot : row = pivot
    · subst row
      let base := gcdData.leftCoeff * A pivot currentColumn +
        gcdData.rightCoeff * A target currentColumn
      rcases centeredMod_eq_add_mul base modulus with ⟨coefficient, equality⟩
      refine ⟨coefficient, ?_⟩
      simp only [result, transform, pairTransform, replacePairSuffix,
        currentNotBefore, if_false,
        twoRowLiftMatrix_mul_apply_pivot pivot target hne,
        bezoutReductionMatrix, gcdBool', bezoutCoreMatrix,
        ComputableEuclideanOps.quot_eq]
      dsimp [base, gcdData] at equality ⊢
      rw [equality]
      ring
    · by_cases rowTarget : row = target
      · subst row
        let base :=
          (A pivot column / gcdData.gcd) * A target currentColumn -
            (A target column / gcdData.gcd) * A pivot currentColumn
        rcases centeredMod_eq_add_mul base modulus with ⟨coefficient, equality⟩
        refine ⟨coefficient, ?_⟩
        simp only [result, transform, pairTransform, replacePairSuffix,
          currentNotBefore, if_false, if_neg hne.symm,
          twoRowLiftMatrix_mul_apply_target, bezoutReductionMatrix, gcdBool',
          bezoutCoreMatrix, ComputableEuclideanOps.quot_eq]
        dsimp [base, gcdData] at equality ⊢
        rw [equality]
        ring
      · simp only [transform, pairTransform,
          twoRowLiftMatrix_mul_apply_other pivot target row rowPivot rowTarget]
        refine ⟨0, ?_⟩
        simp [result, replacePairSuffix, currentNotBefore, rowPivot, rowTarget]

theorem replacePairSuffix_augmentedRowSpan {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (hne : pivot ≠ target)
    (column : Fin n) (modulus : Int)
    (targetNonzero : A target column ≠ 0)
    (prefixZero :
      ∀ row, row = pivot ∨ row = target →
        ∀ currentColumn, currentColumn < column → A row currentColumn = 0) :
    let gcdData := ComputableEuclideanOps.xgcd
      (A pivot column) (A target column)
    augmentedRowSpan
        (replacePairSuffix A pivot target column modulus
          gcdData.leftCoeff gcdData.rightCoeff
          (A pivot column / gcdData.gcd)
          (A target column / gcdData.gcd))
        modulus column.val =
      augmentedRowSpan A modulus column.val := by
  dsimp
  apply augmentedRowSpan_eq_of_transform_congruent
    (pairTransformCertificate pivot target hne
      (A pivot column) (A target column))
  exact replacePairSuffix_congruent A pivot target hne column modulus
    targetNonzero prefixZero

end Internal

end NormalForms.Research.ModularHNF
