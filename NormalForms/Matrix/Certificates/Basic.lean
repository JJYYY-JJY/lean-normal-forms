/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Basic
public import NormalForms.Matrix.Indexing
import all NormalForms.Matrix.Elementary

/-!
# Certificates

Strong matrix-inverse certificates and the left/two-sided normal-form
certificate interfaces. The determinant-based `Unimodular` predicate is a
derived compatibility view, never the source of an algorithmic inverse.
-/

namespace NormalForms.Matrix.Certificates

open scoped Matrix

abbrev ERowOperation := NormalForms.Matrix.Elementary.RowOperation
abbrev EColumnOperation := NormalForms.Matrix.Elementary.ColumnOperation
abbrev EMatrixStep := NormalForms.Matrix.Elementary.MatrixStep
abbrev EOperationLog := NormalForms.Matrix.Elementary.OperationLog

@[expose] public section

/-- Square matrices with unit determinant. This is derived from an explicit inverse certificate. -/
def Unimodular {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (U : _root_.Matrix m m R) : Prop :=
  IsUnit U.det

/-- The equation-only shape retained for statements that do not claim invertibility. -/
structure LeftTransformEquation {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  result : _root_.Matrix m n R
  equation : U * A = result

/-- The equation-only shape retained for statements that do not claim invertibility. -/
structure TwoSidedTransformEquation {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  result : _root_.Matrix m n R
  V : _root_.Matrix n n R
  equation : U * A * V = result

/-- Constructive evidence that `U` is invertible, carrying the inverse itself. -/
structure MatrixInverseCertificate {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    (U : _root_.Matrix n n R) where
  inverse : _root_.Matrix n n R
  left_inv : inverse * U = 1
  right_inv : U * inverse = 1

/-- A left transform together with a constructive inverse for the transform matrix. -/
structure LeftCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  U_cert : MatrixInverseCertificate U
  result : _root_.Matrix m n R
  equation : U * A = result

/-- A two-sided transform with constructive inverses for both transform matrices. -/
structure TwoSidedCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  U_cert : MatrixInverseCertificate U
  result : _root_.Matrix m n R
  V : _root_.Matrix n n R
  V_cert : MatrixInverseCertificate V
  equation : U * A * V = result

def MatrixInverseCertificate.one {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R] :
    MatrixInverseCertificate (1 : _root_.Matrix n n R) := by
  have sumIteEq (s : Finset n) (a : n) (b : n → R) :
      (∑ x ∈ s, if a = x then b x else 0) =
        if a ∈ s then b a else 0 := by
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty]
        rfl
    | @insert x s hx ih =>
        rw [Finset.sum_insert hx, ih]
        by_cases h : a = x
        · subst x
          simp only [if_pos, Finset.mem_insert, true_or, hx, if_false, add_zero]
        · simp only [h, if_false, Finset.mem_insert, false_or, zero_add]
  have hOne : (1 : _root_.Matrix n n R) * 1 = 1 := by
    ext i j
    simp only [_root_.Matrix.mul_apply, _root_.Matrix.one_apply, ite_mul,
      _root_.one_mul, zero_mul]
    rw [sumIteEq]
    simp only [Finset.mem_univ, if_true]
  exact
    { inverse := 1
      left_inv := hOne
      right_inv := hOne }

/-- Compose inverse certificates without determinant or choice. -/
def MatrixInverseCertificate.mul {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    {U V : _root_.Matrix n n R}
    (U_cert : MatrixInverseCertificate U) (V_cert : MatrixInverseCertificate V) :
    MatrixInverseCertificate (U * V) := by
  have sumComm (s t : Finset n) (f : n → n → R) :
      (∑ x ∈ s, ∑ y ∈ t, f x y) =
        ∑ y ∈ t, ∑ x ∈ s, f x y := by
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty]
        exact (Finset.sum_const_zero).symm
    | @insert x s hx ih =>
        rw [Finset.sum_insert hx, ih]
        simp only [Finset.sum_insert hx]
        exact Finset.sum_add_distrib.symm
  have matrixMulAssoc (L M N : _root_.Matrix n n R) :
      L * M * N = L * (M * N) := by
    ext i j
    simp only [_root_.Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
      _root_.mul_assoc]
    exact sumComm Finset.univ Finset.univ
      (fun x y => L i y * (M y x * N x j))
  have matrixMulOne (M : _root_.Matrix n n R) :
      M * (1 : _root_.Matrix n n R) = M := by
    have sumIteEqRight (s : Finset n) (a : n) (b : n → R) :
        (∑ x ∈ s, if x = a then b x else 0) =
          if a ∈ s then b a else 0 := by
      induction s using Finset.induction_on with
      | empty =>
          rw [Finset.sum_empty]
          rfl
      | @insert x s hx ih =>
          rw [Finset.sum_insert hx, ih]
          by_cases h : x = a
          · subst x
            simp only [if_pos, Finset.mem_insert, true_or, hx, if_false, add_zero]
          · have h' : a ≠ x := by simpa [eq_comm] using h
            simp only [h, if_false, Finset.mem_insert, h', false_or, zero_add]
    ext i j
    simp only [_root_.Matrix.mul_apply, _root_.Matrix.one_apply, mul_ite,
      _root_.mul_one, mul_zero]
    rw [sumIteEqRight]
    simp only [Finset.mem_univ, if_true]
  exact
  { inverse := V_cert.inverse * U_cert.inverse
    left_inv := by
      calc
        (V_cert.inverse * U_cert.inverse) * (U * V) =
            V_cert.inverse * (U_cert.inverse * (U * V)) :=
              matrixMulAssoc _ _ _
        _ = V_cert.inverse * ((U_cert.inverse * U) * V) := by
              rw [matrixMulAssoc U_cert.inverse U V]
        _ = (V_cert.inverse * (U_cert.inverse * U)) * V :=
              (matrixMulAssoc _ _ _).symm
        _ = (V_cert.inverse * 1) * V := by rw [U_cert.left_inv]
        _ = V_cert.inverse * V := by
              rw [matrixMulOne]
        _ = 1 := V_cert.left_inv
    right_inv := by
      calc
        (U * V) * (V_cert.inverse * U_cert.inverse) =
            U * (V * (V_cert.inverse * U_cert.inverse)) :=
              matrixMulAssoc _ _ _
        _ = U * ((V * V_cert.inverse) * U_cert.inverse) := by
              rw [matrixMulAssoc V V_cert.inverse U_cert.inverse]
        _ = (U * (V * V_cert.inverse)) * U_cert.inverse :=
              (matrixMulAssoc _ _ _).symm
        _ = (U * 1) * U_cert.inverse := by rw [V_cert.right_inv]
        _ = U * U_cert.inverse := by
              rw [matrixMulOne]
        _ = 1 := U_cert.right_inv }

/-- Regard the certified inverse as a certified matrix in its own right. -/
def MatrixInverseCertificate.symm {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    {U : _root_.Matrix n n R} (U_cert : MatrixInverseCertificate U) :
    MatrixInverseCertificate U_cert.inverse :=
  { inverse := U
    left_inv := U_cert.right_inv
    right_inv := U_cert.left_inv }

/-- Reindex a square inverse certificate along an explicit equivalence. -/
def MatrixInverseCertificate.reindex {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (e : m ≃ n) {U : _root_.Matrix m m R} (U_cert : MatrixInverseCertificate U) :
    MatrixInverseCertificate (_root_.Matrix.reindex e e U) :=
  { inverse := _root_.Matrix.reindex e e U_cert.inverse
    left_inv := by
      calc
        _root_.Matrix.reindex e e U_cert.inverse * _root_.Matrix.reindex e e U =
            _root_.Matrix.reindex e e (U_cert.inverse * U) := by
              simpa only [Matrix.coe_reindexLinearEquiv] using
                Matrix.reindexLinearEquiv_mul R R e e e U_cert.inverse U
        _ = 1 := by simp [U_cert.left_inv]
    right_inv := by
      calc
        _root_.Matrix.reindex e e U * _root_.Matrix.reindex e e U_cert.inverse =
            _root_.Matrix.reindex e e (U * U_cert.inverse) := by
              simpa only [Matrix.coe_reindexLinearEquiv] using
                Matrix.reindexLinearEquiv_mul R R e e e U U_cert.inverse
        _ = 1 := by simp [U_cert.right_inv] }

/-- Transposition swaps the two inverse equations. -/
def MatrixInverseCertificate.transpose {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    {U : _root_.Matrix n n R} (U_cert : MatrixInverseCertificate U) :
    MatrixInverseCertificate U.transpose :=
  { inverse := U_cert.inverse.transpose
    left_inv := by
      simpa [Matrix.transpose_mul] using congrArg _root_.Matrix.transpose U_cert.right_inv
    right_inv := by
      simpa [Matrix.transpose_mul] using congrArg _root_.Matrix.transpose U_cert.left_inv }

/-- Constructive inverse for the row permutation between two explicit indexings. -/
def MatrixInverseCertificate.rowPermutation {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [CommRing R]
    (source target : NormalForms.Matrix.MatrixIndexing m n) :
    MatrixInverseCertificate
      (source.rowPermutation (R := R) target) :=
  { inverse := target.rowPermutation (R := R) source
    left_inv :=
      NormalForms.Matrix.MatrixIndexing.rowPermutation_reverse_mul
        (R := R) source target
    right_inv :=
      NormalForms.Matrix.MatrixIndexing.rowPermutation_mul_reverse
        (R := R) source target }

/-- Constructive inverse for the column permutation between two explicit indexings. -/
def MatrixInverseCertificate.columnPermutation {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq n] [CommRing R]
    (source target : NormalForms.Matrix.MatrixIndexing m n) :
    MatrixInverseCertificate
      (source.columnPermutation (R := R) target) :=
  { inverse := target.columnPermutation (R := R) source
    left_inv :=
      NormalForms.Matrix.MatrixIndexing.columnPermutation_reverse_mul
        (R := R) source target
    right_inv :=
      NormalForms.Matrix.MatrixIndexing.columnPermutation_mul_reverse
        (R := R) source target }

/-- An explicit two-sided inverse makes the matrix a unit in the matrix monoid. -/
theorem MatrixInverseCertificate.isUnit {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    {U : _root_.Matrix n n R} (U_cert : MatrixInverseCertificate U) :
    IsUnit U :=
  isUnit_iff_exists.mpr ⟨U_cert.inverse, U_cert.right_inv, U_cert.left_inv⟩

/-- Determinant-based unimodularity derived from the explicit inverse. -/
theorem MatrixInverseCertificate.unimodular {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    {U : _root_.Matrix n n R} (U_cert : MatrixInverseCertificate U) :
    Unimodular U :=
  _root_.Matrix.isUnit_det_of_left_inverse U_cert.left_inv

/-- Forget inverse evidence and retain only the left transformation equation. -/
def LeftCertificate.toTransformEquation {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (cert : LeftCertificate A) :
    LeftTransformEquation A :=
  { U := cert.U, result := cert.result, equation := cert.equation }

/-- Forget inverse evidence and retain only the two-sided transformation equation. -/
def TwoSidedCertificate.toTransformEquation {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (cert : TwoSidedCertificate A) :
    TwoSidedTransformEquation A :=
  { U := cert.U, result := cert.result, V := cert.V, equation := cert.equation }

@[simp] theorem unimodular_one {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R] :
    Unimodular (1 : _root_.Matrix m m R) := by
  simp [Unimodular]

@[simp] theorem unimodular_mul {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    {U V : _root_.Matrix m m R} (hU : Unimodular U) (hV : Unimodular V) :
    Unimodular (U * V) := by
  simpa [Unimodular, _root_.Matrix.det_mul] using IsUnit.mul hU hV

end

theorem rowSwapMatrix_mul_self {m R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R] (i j : m) :
    NormalForms.Matrix.Elementary.rowOperationMatrix
          (.swap i j : ERowOperation R m) *
        NormalForms.Matrix.Elementary.rowOperationMatrix
          (.swap i j : ERowOperation R m) =
      1 := by
  rw [NormalForms.Matrix.Elementary.rowOperationMatrix_mul]
  ext r c
  by_cases hij : i = j
  · subst j
    by_cases hri : r = i
    · subst r
      simp [NormalForms.Matrix.Elementary.rowOperationMatrix,
        NormalForms.Matrix.Elementary.applyRowOperation]
    · simp [NormalForms.Matrix.Elementary.rowOperationMatrix,
        NormalForms.Matrix.Elementary.applyRowOperation, hri]
  · by_cases hri : r = i
    · subst r
      have hji : j ≠ i := fun h => hij h.symm
      simp [NormalForms.Matrix.Elementary.rowOperationMatrix,
        NormalForms.Matrix.Elementary.applyRowOperation, hji]
    · by_cases hrj : r = j
      · subst r
        simp [NormalForms.Matrix.Elementary.rowOperationMatrix,
          NormalForms.Matrix.Elementary.applyRowOperation, hri]
      · simp [NormalForms.Matrix.Elementary.rowOperationMatrix,
          NormalForms.Matrix.Elementary.applyRowOperation, hri, hrj]

theorem columnSwapMatrix_mul_self {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R] (i j : n) :
    NormalForms.Matrix.Elementary.columnOperationMatrix
          (.swap i j : EColumnOperation R n) *
        NormalForms.Matrix.Elementary.columnOperationMatrix
          (.swap i j : EColumnOperation R n) =
      1 := by
  rw [NormalForms.Matrix.Elementary.mul_columnOperationMatrix]
  ext r c
  by_cases hij : i = j
  · subst j
    by_cases hci : c = i
    · subst c
      simp [NormalForms.Matrix.Elementary.columnOperationMatrix,
        NormalForms.Matrix.Elementary.applyColumnOperation]
    · simp [NormalForms.Matrix.Elementary.columnOperationMatrix,
        NormalForms.Matrix.Elementary.applyColumnOperation, hci]
  · by_cases hci : c = i
    · subst c
      have hji : j ≠ i := fun h => hij h.symm
      simp [NormalForms.Matrix.Elementary.columnOperationMatrix,
        NormalForms.Matrix.Elementary.applyColumnOperation, hji]
    · by_cases hcj : c = j
      · subst c
        simp [NormalForms.Matrix.Elementary.columnOperationMatrix,
          NormalForms.Matrix.Elementary.applyColumnOperation, hci]
      · simp [NormalForms.Matrix.Elementary.columnOperationMatrix,
          NormalForms.Matrix.Elementary.applyColumnOperation, hci, hcj]

theorem unimodular_rowOperationMatrix {m R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    (op : ERowOperation R m)
    (hop : NormalForms.Matrix.Elementary.UnimodularRowOperation op) :
    Unimodular (NormalForms.Matrix.Elementary.rowOperationMatrix op) := by
  cases op with
  | swap i j =>
      change
        IsUnit
          (NormalForms.Matrix.Elementary.rowOperationMatrix
            (.swap i j : ERowOperation R m)).det
      exact _root_.Matrix.isUnit_det_of_left_inverse
        (rowSwapMatrix_mul_self (R := R) i j)
  | add src dst c =>
      simp [Unimodular, NormalForms.Matrix.Elementary.det_rowAddMatrix_of_ne src dst c hop]
  | smul i c =>
      change IsUnit c at hop
      rw [Unimodular, NormalForms.Matrix.Elementary.rowOperationMatrix,
        NormalForms.Matrix.Elementary.det_rowScaleMatrix i c]
      exact hop

theorem unimodular_columnOperationMatrix {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    (op : EColumnOperation R n)
    (hop : NormalForms.Matrix.Elementary.UnimodularColumnOperation op) :
    Unimodular (NormalForms.Matrix.Elementary.columnOperationMatrix op) := by
  cases op with
  | swap i j =>
      change
        IsUnit
          (NormalForms.Matrix.Elementary.columnOperationMatrix
            (.swap i j : EColumnOperation R n)).det
      exact _root_.Matrix.isUnit_det_of_left_inverse
        (columnSwapMatrix_mul_self (R := R) i j)
  | add src dst c =>
      simp [Unimodular, NormalForms.Matrix.Elementary.det_columnAddMatrix_of_ne src dst c hop]
  | smul i c =>
      change IsUnit c at hop
      rw [Unimodular, NormalForms.Matrix.Elementary.columnOperationMatrix,
        NormalForms.Matrix.Elementary.det_columnScaleMatrix i c]
      exact hop

/-- Explicit inverse certificate for a row swap. -/
def rowSwapInverseCertificate {m R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R] (i j : m) :
    MatrixInverseCertificate
      (NormalForms.Matrix.Elementary.rowOperationMatrix
        (.swap i j : ERowOperation R m)) :=
  { inverse :=
      NormalForms.Matrix.Elementary.rowOperationMatrix
        (.swap i j : ERowOperation R m)
    left_inv := rowSwapMatrix_mul_self i j
    right_inv := rowSwapMatrix_mul_self i j }

/-- Explicit inverse certificate for a column swap. -/
def columnSwapInverseCertificate {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R] (i j : n) :
    MatrixInverseCertificate
      (NormalForms.Matrix.Elementary.columnOperationMatrix
        (.swap i j : EColumnOperation R n)) :=
  { inverse :=
      NormalForms.Matrix.Elementary.columnOperationMatrix
        (.swap i j : EColumnOperation R n)
    left_inv := columnSwapMatrix_mul_self i j
    right_inv := columnSwapMatrix_mul_self i j }

/-- Explicit inverse certificate for adding a multiple of one row to another. -/
def rowAddInverseCertificate {m R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    (src dst : m) (c : R) (hne : src ≠ dst) :
    MatrixInverseCertificate
      (NormalForms.Matrix.Elementary.rowOperationMatrix
        (.add src dst c : ERowOperation R m)) :=
  { inverse :=
      NormalForms.Matrix.Elementary.rowOperationMatrix
        (.add src dst (-c) : ERowOperation R m)
    left_inv := by
      rw [NormalForms.Matrix.Elementary.rowOperationMatrix_mul]
      ext i j
      by_cases hi : i = dst
      · subst i
        simp [NormalForms.Matrix.Elementary.applyRowOperation,
          NormalForms.Matrix.Elementary.rowOperationMatrix, hne]
      · simp [NormalForms.Matrix.Elementary.applyRowOperation,
          NormalForms.Matrix.Elementary.rowOperationMatrix, hi]
    right_inv := by
      rw [NormalForms.Matrix.Elementary.rowOperationMatrix_mul]
      ext i j
      by_cases hi : i = dst
      · subst i
        simp [NormalForms.Matrix.Elementary.applyRowOperation,
          NormalForms.Matrix.Elementary.rowOperationMatrix, hne]
      · simp [NormalForms.Matrix.Elementary.applyRowOperation,
          NormalForms.Matrix.Elementary.rowOperationMatrix, hi] }

/-- Explicit inverse certificate for adding a multiple of one column to another. -/
def columnAddInverseCertificate {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    (src dst : n) (c : R) (hne : src ≠ dst) :
    MatrixInverseCertificate
      (NormalForms.Matrix.Elementary.columnOperationMatrix
        (.add src dst c : EColumnOperation R n)) :=
  { inverse :=
      NormalForms.Matrix.Elementary.columnOperationMatrix
        (.add src dst (-c) : EColumnOperation R n)
    left_inv := by
      rw [NormalForms.Matrix.Elementary.mul_columnOperationMatrix]
      ext i j
      by_cases hj : j = dst
      · subst j
        simp [NormalForms.Matrix.Elementary.applyColumnOperation,
          NormalForms.Matrix.Elementary.columnOperationMatrix, hne]
      · simp [NormalForms.Matrix.Elementary.applyColumnOperation,
          NormalForms.Matrix.Elementary.columnOperationMatrix, hj]
    right_inv := by
      rw [NormalForms.Matrix.Elementary.mul_columnOperationMatrix]
      ext i j
      by_cases hj : j = dst
      · subst j
        simp [NormalForms.Matrix.Elementary.applyColumnOperation,
          NormalForms.Matrix.Elementary.columnOperationMatrix, hne]
      · simp [NormalForms.Matrix.Elementary.applyColumnOperation,
          NormalForms.Matrix.Elementary.columnOperationMatrix, hj] }

/-- Explicit inverse certificate for scaling a row by a supplied unit. -/
def rowUnitScaleInverseCertificate {m R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R] (i : m) (u : Rˣ) :
    MatrixInverseCertificate
      (NormalForms.Matrix.Elementary.rowOperationMatrix
        (.smul i (u : R) : ERowOperation R m)) :=
  { inverse :=
      NormalForms.Matrix.Elementary.rowOperationMatrix
        (.smul i (↑u⁻¹ : R) : ERowOperation R m)
    left_inv := by
      rw [NormalForms.Matrix.Elementary.rowOperationMatrix_mul]
      ext r c
      by_cases hr : r = i
      · subst r
        simp [NormalForms.Matrix.Elementary.applyRowOperation,
          NormalForms.Matrix.Elementary.rowOperationMatrix,
          NormalForms.Matrix.Elementary.rowScaleMatrix]
      · simp [NormalForms.Matrix.Elementary.applyRowOperation,
          NormalForms.Matrix.Elementary.rowOperationMatrix,
          NormalForms.Matrix.Elementary.rowScaleMatrix, hr]
    right_inv := by
      rw [NormalForms.Matrix.Elementary.rowOperationMatrix_mul]
      ext r c
      by_cases hr : r = i
      · subst r
        simp [NormalForms.Matrix.Elementary.applyRowOperation,
          NormalForms.Matrix.Elementary.rowOperationMatrix,
          NormalForms.Matrix.Elementary.rowScaleMatrix]
      · simp [NormalForms.Matrix.Elementary.applyRowOperation,
          NormalForms.Matrix.Elementary.rowOperationMatrix,
          NormalForms.Matrix.Elementary.rowScaleMatrix, hr] }

/-- Explicit inverse certificate for scaling a column by a supplied unit. -/
def columnUnitScaleInverseCertificate {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R] (i : n) (u : Rˣ) :
    MatrixInverseCertificate
      (NormalForms.Matrix.Elementary.columnOperationMatrix
        (.smul i (u : R) : EColumnOperation R n)) :=
  { inverse :=
      NormalForms.Matrix.Elementary.columnOperationMatrix
        (.smul i (↑u⁻¹ : R) : EColumnOperation R n)
    left_inv := by
      rw [NormalForms.Matrix.Elementary.mul_columnOperationMatrix]
      ext r c
      by_cases hc : c = i
      · subst c
        simp [NormalForms.Matrix.Elementary.applyColumnOperation,
          NormalForms.Matrix.Elementary.columnOperationMatrix,
          NormalForms.Matrix.Elementary.columnScaleMatrix]
      · simp [NormalForms.Matrix.Elementary.applyColumnOperation,
          NormalForms.Matrix.Elementary.columnOperationMatrix,
          NormalForms.Matrix.Elementary.columnScaleMatrix, hc]
    right_inv := by
      rw [NormalForms.Matrix.Elementary.mul_columnOperationMatrix]
      ext r c
      by_cases hc : c = i
      · subst c
        simp [NormalForms.Matrix.Elementary.applyColumnOperation,
          NormalForms.Matrix.Elementary.columnOperationMatrix,
          NormalForms.Matrix.Elementary.columnScaleMatrix]
      · simp [NormalForms.Matrix.Elementary.applyColumnOperation,
          NormalForms.Matrix.Elementary.columnOperationMatrix,
          NormalForms.Matrix.Elementary.columnScaleMatrix, hc] }

theorem leftAccumulator_unimodular_of_forall {m n R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    (log : EOperationLog R m n)
    (hlog : log.Forall NormalForms.Matrix.Elementary.UnimodularStep) :
    Unimodular (NormalForms.Matrix.Elementary.leftAccumulator log) := by
  induction log with
  | nil =>
      simp [NormalForms.Matrix.Elementary.leftAccumulator]
  | cons step log ih =>
      cases step with
      | row op =>
          have hpair :
              NormalForms.Matrix.Elementary.UnimodularStep (.row op : EMatrixStep R m n) ∧
                log.Forall NormalForms.Matrix.Elementary.UnimodularStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.leftAccumulator,
              NormalForms.Matrix.Elementary.UnimodularStep] using
            unimodular_mul (ih hpair.2) (unimodular_rowOperationMatrix op hpair.1)
      | col op =>
          have hpair :
              NormalForms.Matrix.Elementary.UnimodularStep (.col op : EMatrixStep R m n) ∧
                log.Forall NormalForms.Matrix.Elementary.UnimodularStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.leftAccumulator,
              NormalForms.Matrix.Elementary.UnimodularStep] using ih hpair.2

theorem rightAccumulator_unimodular_of_forall {m n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    (log : EOperationLog R m n)
    (hlog : log.Forall NormalForms.Matrix.Elementary.UnimodularStep) :
    Unimodular (NormalForms.Matrix.Elementary.rightAccumulator log) := by
  induction log with
  | nil =>
      simp [NormalForms.Matrix.Elementary.rightAccumulator]
  | cons step log ih =>
      cases step with
      | row op =>
          have hpair :
              NormalForms.Matrix.Elementary.UnimodularStep (.row op : EMatrixStep R m n) ∧
                log.Forall NormalForms.Matrix.Elementary.UnimodularStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.rightAccumulator,
              NormalForms.Matrix.Elementary.UnimodularStep] using ih hpair.2
      | col op =>
          have hpair :
              NormalForms.Matrix.Elementary.UnimodularStep (.col op : EMatrixStep R m n) ∧
                log.Forall NormalForms.Matrix.Elementary.UnimodularStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.rightAccumulator,
              NormalForms.Matrix.Elementary.UnimodularStep] using
            unimodular_mul (unimodular_columnOperationMatrix op hpair.1) (ih hpair.2)

/-- Predicate selecting row-only logs, used to collapse the right accumulator to `1`. -/
def IsRowStep {m n R : Type _} : EMatrixStep R m n -> Prop
  | .row _ => True
  | .col _ => False

/-- Predicate selecting column-only logs, used to collapse the left accumulator to `1`. -/
def IsColStep {m n R : Type _} : EMatrixStep R m n -> Prop
  | .row _ => False
  | .col _ => True

theorem rightAccumulator_eq_one_of_forall_isRow {m n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    (log : EOperationLog R m n) (hlog : log.Forall IsRowStep) :
    NormalForms.Matrix.Elementary.rightAccumulator log = (1 : _root_.Matrix n n R) := by
  induction log with
  | nil =>
      simp [NormalForms.Matrix.Elementary.rightAccumulator]
  | cons step log ih =>
      cases step with
      | row op =>
          have hpair : IsRowStep (.row op : EMatrixStep R m n) ∧ log.Forall IsRowStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.rightAccumulator, IsRowStep] using ih hpair.2
      | col op =>
          have hpair : IsRowStep (.col op : EMatrixStep R m n) ∧ log.Forall IsRowStep := by
            simpa [List.Forall]
              using hlog
          cases hpair.1

theorem leftAccumulator_eq_one_of_forall_isCol {m n R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    (log : EOperationLog R m n) (hlog : log.Forall IsColStep) :
    NormalForms.Matrix.Elementary.leftAccumulator log = (1 : _root_.Matrix m m R) := by
  induction log with
  | nil =>
      simp [NormalForms.Matrix.Elementary.leftAccumulator]
  | cons step log ih =>
      cases step with
      | row op =>
          have hpair : IsColStep (.row op : EMatrixStep R m n) ∧ log.Forall IsColStep := by
            simpa [List.Forall]
              using hlog
          cases hpair.1
      | col op =>
          have hpair : IsColStep (.col op : EMatrixStep R m n) ∧ log.Forall IsColStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.leftAccumulator, IsColStep] using ih hpair.2

def TwoSidedTransformEquation.ofLog {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (log : EOperationLog R m n) :
    TwoSidedTransformEquation A :=
  { U := NormalForms.Matrix.Elementary.leftAccumulator log
    result := NormalForms.Matrix.Elementary.replayLog A log
    V := NormalForms.Matrix.Elementary.rightAccumulator log
    equation := NormalForms.Matrix.Elementary.replayLog_eq_left_right A log }

def LeftTransformEquation.ofRowLog {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (log : EOperationLog R m n)
    (hrow : log.Forall IsRowStep) :
    LeftTransformEquation A :=
  { U := NormalForms.Matrix.Elementary.leftAccumulator log
    result := NormalForms.Matrix.Elementary.replayLog A log
    equation := by
      simpa [rightAccumulator_eq_one_of_forall_isRow log hrow] using
        NormalForms.Matrix.Elementary.replayLog_eq_left_right A log }

end NormalForms.Matrix.Certificates
