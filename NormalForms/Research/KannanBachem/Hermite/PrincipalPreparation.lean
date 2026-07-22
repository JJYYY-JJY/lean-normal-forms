/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalPrefix
public import NormalForms.Research.KannanBachem.Hermite.PrincipalChecker
public import NormalForms.Research.KannanBachem.Hermite.DeterminantScan
public import Mathlib.GroupTheory.Perm.Fin
import all NormalForms.Matrix.Hermite.Uniqueness

/-!
# Deterministic Preparation for the Principal HNF Kernel

The principal-minor coefficient bounds require every leading principal minor
to be nonsingular.  Following the transposed Step 2 of Kannan--Bachem, this
module deterministically permutes rows before running the principal kernel.

The selector is executable and chooses the first row whose complementary
last-column minor is nonsingular. It is the value projection of the certified
charged Bird scan, rather than mathlib's permutation-sum determinant. This
module proves semantic correctness, the `PrincipalReady` invariant, an
explicit inverse certificate for the permutation transform, and a uniform
cost bound for every individual scan.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix BigOperators
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Research.BitCost
open DivisionFreeDeterminant

namespace Principal

/-- Extend a permutation by putting `pivot` last and permuting its complement. -/
@[expose] public def appendRowPermutation {n : Nat} (pivot : Fin (n + 1))
    (tail : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans
    ((Equiv.optionCongr tail).trans (finSuccEquiv' pivot).symm)

@[simp] public theorem appendRowPermutation_last {n : Nat}
    (pivot : Fin (n + 1)) (tail : Equiv.Perm (Fin n)) :
    appendRowPermutation pivot tail (Fin.last n) = pivot := by
  simp [appendRowPermutation]

@[simp] public theorem appendRowPermutation_castSucc {n : Nat}
    (pivot : Fin (n + 1)) (tail : Equiv.Perm (Fin n)) (i : Fin n) :
    appendRowPermutation pivot tail i.castSucc =
      pivot.succAbove (tail i) := by
  simp [appendRowPermutation]

/-- Delete one row and the last column. -/
@[expose] public def lastColumnMinor {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (pivot : Fin (n + 1)) : _root_.Matrix (Fin n) (Fin n) Int :=
  A.submatrix pivot.succAbove (Fin.last n).succAbove

/-- A nonsingular matrix has a nonsingular complementary last-column minor. -/
public theorem exists_lastColumnMinor_det_ne_zero {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    ∃ pivot, (lastColumnMinor A pivot).det ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hdet
  rw [_root_.Matrix.det_succ_column A (Fin.last n)]
  apply Finset.sum_eq_zero
  intro pivot _
  have hminor :
      (A.submatrix pivot.succAbove Fin.castSucc).det = 0 := by
    simpa [lastColumnMinor] using hall pivot
  simp [hminor]

/-- Charged left-to-right scan of all complementary last-column minors. -/
@[expose] public def lastColumnScan {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    WithCost (Option (Fin (n + 1))) :=
  scanFirstNonzeroWithCost (lastColumnMinor A)
    (List.finRange (n + 1))

/-- Nonsingularity guarantees that the charged scan finds a row. -/
public theorem lastColumnScan_isSome {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (lastColumnScan A).value.isSome := by
  rw [Option.isSome_iff_ne_none]
  intro none
  rw [lastColumnScan, scanFirstNonzeroWithCost_none_iff] at none
  obtain ⟨pivot, pivotNonzero⟩ :=
    exists_lastColumnMinor_det_ne_zero A hdet
  have encodedNonzero :
      (evaluateWithCost (lastColumnMinor A pivot)).value ≠ 0 :=
    (evaluateWithCost_value_ne_zero_iff _).2 pivotNonzero
  exact encodedNonzero (none pivot (by simp))

/-- One scan has at most one determinant evaluation and zero test per row. -/
public theorem lastColumnScan_cost_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (lastColumnScan A).cost ≤
      (n + 1) *
        (determinantBitOperationBound n (matrixBitLength A) + 1) := by
  rw [lastColumnScan]
  simpa using scanFirstNonzeroWithCost_cost_le
    (lastColumnMinor A) (List.finRange (n + 1)) (matrixBitLength A)
    (by
      intro pivot _member
      exact submatrix_bitLength_le A pivot.succAbove
        (Fin.last n).succAbove)

/-- The first row accepted by the certified charged scan. -/
@[expose] public def lastColumnPivot {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) : Fin (n + 1) :=
  (lastColumnScan A).value.get (lastColumnScan_isSome A hdet)

public theorem lastColumnPivot_spec {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (lastColumnMinor A (lastColumnPivot A hdet)).det ≠ 0 := by
  have result :
      (lastColumnScan A).value = some (lastColumnPivot A hdet) := by
    exact (Option.some_get _).symm
  have nonzero := (scanFirstNonzeroWithCost_some_spec
    (lastColumnMinor A) (List.finRange (n + 1))
    (by simpa [lastColumnScan] using result)).2
  exact (evaluateWithCost_value_ne_zero_iff _).1 nonzero

/-- Recursively order rows so that every leading principal minor is nonzero. -/
@[expose] public def readyRowPermutation : {_n : Nat} →
    (A : _root_.Matrix (Fin _n) (Fin _n) Int) → A.det ≠ 0 →
      Equiv.Perm (Fin _n)
  | 0, _, _ => 1
  | _n + 1, A, hdet =>
      let pivot := lastColumnPivot A hdet
      appendRowPermutation pivot
        (readyRowPermutation (lastColumnMinor A pivot)
          (lastColumnPivot_spec A hdet))

public theorem leadingSubmatrix_appendRowPermutation {n k : Nat}
    (hk : k ≤ n)
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (pivot : Fin (n + 1)) (tail : Equiv.Perm (Fin n)) :
    leadingSubmatrix (hk.trans (Nat.le_succ n))
        (A.submatrix (appendRowPermutation pivot tail) id) =
      leadingSubmatrix hk
        ((lastColumnMinor A pivot).submatrix tail id) := by
  ext row column
  have hrow :
      Fin.castLE (hk.trans (Nat.le_succ n)) row =
        Fin.castSucc (Fin.castLE hk row) := Fin.ext rfl
  have hcolumn :
      Fin.castLE (hk.trans (Nat.le_succ n)) column =
        Fin.castSucc (Fin.castLE hk column) := Fin.ext rfl
  have hpermutation :
      appendRowPermutation pivot tail
          (Fin.castLE (hk.trans (Nat.le_succ n)) row) =
        pivot.succAbove (tail (Fin.castLE hk row)) := by
    rw [hrow]
    exact appendRowPermutation_castSucc pivot tail _
  simp only [leadingSubmatrix, _root_.Matrix.submatrix_apply, id_eq]
  rw [hpermutation, hcolumn]
  simp [lastColumnMinor]

/-- The recursive row permutation establishes the principal-kernel precondition. -/
public theorem readyRowPermutation_ready : {n : Nat} →
    (A : _root_.Matrix (Fin n) (Fin n) Int) → (hdet : A.det ≠ 0) →
      PrincipalReady (A.submatrix (readyRowPermutation A hdet) id)
  | 0, _, _ => by
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp [leadingSubmatrix]
  | n + 1, A, hdet => by
      let pivot := lastColumnPivot A hdet
      let minor := lastColumnMinor A pivot
      let minorNonzero : minor.det ≠ 0 := lastColumnPivot_spec A hdet
      have tailReady := readyRowPermutation_ready minor minorNonzero
      intro k hk
      by_cases hfull : k = n + 1
      · subst k
        have hleading :
            leadingSubmatrix hk
                (A.submatrix (readyRowPermutation A hdet) id) =
              A.submatrix (readyRowPermutation A hdet) id := by
          ext row column
          simp only [leadingSubmatrix, _root_.Matrix.submatrix_apply, id_eq]
          have hrow : Fin.castLE hk row = row := Fin.ext rfl
          have hcolumn : Fin.castLE hk column = column := Fin.ext rfl
          rw [hrow, hcolumn]
        rw [hleading, _root_.Matrix.det_permute]
        exact mul_ne_zero (by simp) hdet
      · have hk' : k ≤ n := by omega
        rw [show readyRowPermutation A hdet =
            appendRowPermutation pivot
              (readyRowPermutation minor minorNonzero) by
          simp [readyRowPermutation, pivot, minor]]
        rw [leadingSubmatrix_appendRowPermutation hk']
        exact tailReady k hk'

/-- Left multiplication by a permutation matrix implements the same row reindexing. -/
public theorem permMatrix_mul_eq_submatrix {n : Nat}
    (permutation : Equiv.Perm (Fin n))
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    permutation.permMatrix Int * A = A.submatrix permutation id := by
  ext row column
  have entry := congrFun
    (_root_.Matrix.permMatrix_mulVec (R := Int)
      (v := fun source => A source column) permutation) row
  change
    _root_.Matrix.mulVec (permutation.permMatrix Int)
        (fun source => A source column) row =
      A (permutation row) column
  exact entry

/-- Constructive inverse of an arbitrary integer permutation matrix. -/
@[expose] public def permMatrixCertificate {n : Nat}
    (permutation : Equiv.Perm (Fin n)) :
    MatrixInverseCertificate (permutation.permMatrix Int) :=
  { inverse := (permutation⁻¹).permMatrix Int
    left_inv := by
      rw [← _root_.Matrix.permMatrix_mul]
      simp
    right_inv := by
      rw [← _root_.Matrix.permMatrix_mul]
      simp }

/-- Minimal preparation data; matrices and certificates are derived projections. -/
public structure Preparation {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) where
  rowPermutation : Equiv.Perm (Fin n)
  ready : PrincipalReady (A.submatrix rowPermutation id)

namespace Preparation

@[expose] public def matrix {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (preparation : Preparation A) : _root_.Matrix (Fin n) (Fin n) Int :=
  A.submatrix preparation.rowPermutation id

@[expose] public def transform {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (preparation : Preparation A) : _root_.Matrix (Fin n) (Fin n) Int :=
  preparation.rowPermutation.permMatrix Int

@[expose] public def transformCertificate {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (preparation : Preparation A) :
    MatrixInverseCertificate preparation.transform :=
  permMatrixCertificate preparation.rowPermutation

public theorem equation {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (preparation : Preparation A) :
    preparation.transform * A = preparation.matrix :=
  permMatrix_mul_eq_submatrix preparation.rowPermutation A

public theorem det_ne {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (preparation : Preparation A) (hdet : A.det ≠ 0) :
    preparation.matrix.det ≠ 0 := by
  rw [matrix, _root_.Matrix.det_permute]
  exact mul_ne_zero (by simp) hdet

end Preparation

/-- Deterministic certified preparation of a nonsingular square input. -/
@[expose] public def prepare {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    Preparation A :=
  { rowPermutation := readyRowPermutation A hdet
    ready := readyRowPermutation_ready A hdet }

/-- Run the ready principal kernel and compose its certificate back to the input. -/
@[expose] public def preparedPrincipalHermiteNormalForm {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    HNFResultFin A := by
  let preparation := prepare A hdet
  let core := principalHermiteNormalForm preparation.matrix
    (preparation.det_ne hdet)
  exact
    { U := core.U * preparation.transform
      U_cert := core.U_cert.mul preparation.transformCertificate
      H := core.H
      equation := by
        rw [_root_.Matrix.mul_assoc, preparation.equation, core.equation]
      isHermite := core.isHermite }

public theorem preparedPrincipalHermiteNormalForm_equation {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (preparedPrincipalHermiteNormalForm A hdet).U * A =
      (preparedPrincipalHermiteNormalForm A hdet).H :=
  (preparedPrincipalHermiteNormalForm A hdet).equation

public theorem preparedPrincipalHermiteNormalForm_inverse_equation {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (preparedPrincipalHermiteNormalForm A hdet).U_cert.inverse *
        (preparedPrincipalHermiteNormalForm A hdet).H = A := by
  rw [← (preparedPrincipalHermiteNormalForm A hdet).equation,
    ← _root_.Matrix.mul_assoc,
    (preparedPrincipalHermiteNormalForm A hdet).U_cert.left_inv]
  simp

public theorem preparedPrincipalHermiteNormalForm_isHermite {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    IsHermiteNormalFormFin (preparedPrincipalHermiteNormalForm A hdet).H :=
  (preparedPrincipalHermiteNormalForm A hdet).isHermite

/-- Certified preparation preserves the canonical HNF, not only left equivalence. -/
public theorem preparedPrincipalHermiteNormalForm_eq_reference {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (preparedPrincipalHermiteNormalForm A hdet).H =
      (semanticReference A).H := by
  let prepared := preparedPrincipalHermiteNormalForm A hdet
  let reference := semanticReference A
  let change := reference.U * prepared.U_cert.inverse
  have changeCert : MatrixInverseCertificate change :=
    reference.U_cert.mul prepared.U_cert.symm
  apply isHermiteNormalFormFin_unique_of_left_equiv
    prepared.isHermite reference.isHermite changeCert.unimodular
  calc
    change * prepared.H =
        reference.U * (prepared.U_cert.inverse * prepared.H) := by
      rw [_root_.Matrix.mul_assoc]
    _ = reference.U * A := by
      rw [show prepared.U_cert.inverse * prepared.H = A by
        simpa [prepared] using
          preparedPrincipalHermiteNormalForm_inverse_equation A hdet]
    _ = reference.H := reference.equation

end Principal

end NormalForms.Research.KannanBachem.Hermite
