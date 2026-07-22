/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.Totality
public import NormalForms.Matrix.Smith.Algorithm
import all NormalForms.Matrix.Smith.Uniqueness

/-!
# Outer Kannan--Bachem Smith Recursion

Once Steps 4--7 produce a stable pivot, the outer recursion transforms only
the strict lower-right block.  This module lifts both explicit inverse
certificates through that block boundary and returns the existing
`SNFResultFin` directly.  The primary `smith` entry is total on every
nonsingular square integer matrix; `smith?` remains as a fuelled diagnostic
entry for bounded execution experiments.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix BigOperators
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith
open NormalForms.Research.KannanBachem.Hermite

/-- Adjoin one diagonal pivot above a square lower-right block. -/
@[expose] public def adjoinPivot {n : Nat} (pivot : Int)
    (lower : _root_.Matrix (Fin n) (Fin n) Int) :
    _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int :=
  fun row column =>
    Fin.cases
      (Fin.cases pivot (fun _ => 0) column)
      (fun row => Fin.cases 0 (fun column => lower row column) column)
      row

@[simp] public theorem adjoinPivot_zero_zero {n : Nat} (pivot : Int)
    (lower : _root_.Matrix (Fin n) (Fin n) Int) :
    adjoinPivot pivot lower 0 0 = pivot := by
  simp [adjoinPivot]

@[simp] public theorem adjoinPivot_zero_succ {n : Nat} (pivot : Int)
    (lower : _root_.Matrix (Fin n) (Fin n) Int) (column : Fin n) :
    adjoinPivot pivot lower 0 column.succ = 0 := by
  simp [adjoinPivot]

@[simp] public theorem adjoinPivot_succ_zero {n : Nat} (pivot : Int)
    (lower : _root_.Matrix (Fin n) (Fin n) Int) (row : Fin n) :
    adjoinPivot pivot lower row.succ 0 = 0 := by
  simp [adjoinPivot]

@[simp] public theorem adjoinPivot_succ_succ {n : Nat} (pivot : Int)
    (lower : _root_.Matrix (Fin n) (Fin n) Int) (row column : Fin n) :
    adjoinPivot pivot lower row.succ column.succ = lower row column := by
  simp [adjoinPivot]

@[simp] public theorem lowerRight_adjoinPivot {n : Nat} (pivot : Int)
    (lower : _root_.Matrix (Fin n) (Fin n) Int) :
    lowerRight (adjoinPivot pivot lower) = lower := by
  ext row column
  simp [lowerRight]

/-- Lift an explicit inverse below one fixed leading coordinate. -/
@[expose] public def leadingLiftCertificate {n : Nat}
    {U : _root_.Matrix (Fin n) (Fin n) Int}
    (certificate : MatrixInverseCertificate U) :
    MatrixInverseCertificate (leadingLiftMatrix U) :=
  { inverse := leadingLiftMatrix certificate.inverse
    left_inv := by
      rw [leadingLiftMatrix_mul, certificate.left_inv,
        leadingLiftMatrix_one]
    right_inv := by
      rw [leadingLiftMatrix_mul, certificate.right_inv,
        leadingLiftMatrix_one] }

/-- Block multiplication acts only on the lower-right block. -/
public theorem leadingLift_mul_mul_leadingLift {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (U V : _root_.Matrix (Fin n) (Fin n) Int)
    (hrow : FirstRowCleared A) (hcolumn : FirstColumnCleared A) :
    leadingLiftMatrix U * A * leadingLiftMatrix V =
      adjoinPivot (A 0 0) (U * lowerRight A * V) := by
  ext row column
  cases row using Fin.cases with
  | zero =>
      cases column using Fin.cases with
      | zero =>
          simp [leadingLiftMatrix, adjoinPivot, _root_.Matrix.mul_apply,
            NormalForms.Matrix.Constructive.sum_univ_succ]
      | succ column =>
          have sumZero :
              (∑ index : Fin n, A 0 index.succ * V index column) = 0 := by
            apply Finset.sum_eq_zero
            intro index _member
            rw [hrow index, zero_mul]
          simpa [leadingLiftMatrix, adjoinPivot, _root_.Matrix.mul_apply,
            NormalForms.Matrix.Constructive.sum_univ_succ] using sumZero
  | succ row =>
      cases column using Fin.cases with
      | zero =>
          have sumZero :
              (∑ index : Fin n, U row index * A index.succ 0) = 0 := by
            apply Finset.sum_eq_zero
            intro index _member
            rw [hcolumn index, mul_zero]
          simpa [leadingLiftMatrix, adjoinPivot, _root_.Matrix.mul_apply,
            NormalForms.Matrix.Constructive.sum_univ_succ] using sumZero
      | succ column =>
          simp [leadingLiftMatrix, adjoinPivot, lowerRight,
            _root_.Matrix.mul_apply,
            NormalForms.Matrix.Constructive.sum_univ_succ]

/-- Lift a lower-right strong certificate through a stable pivot. -/
@[expose] public def liftLowerCertificate {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (stable : StablePivot A)
    (lower : TwoSidedCertificate (lowerRight A)) :
    TwoSidedCertificate A :=
  { U := leadingLiftMatrix lower.U
    U_cert := leadingLiftCertificate lower.U_cert
    result := adjoinPivot (A 0 0) lower.result
    V := leadingLiftMatrix lower.V
    V_cert := leadingLiftCertificate lower.V_cert
    equation := by
      rw [leadingLift_mul_mul_leadingLift A lower.U lower.V
        stable.firstRowCleared stable.firstColumnCleared,
        lower.equation] }

set_option linter.unusedDecidableInType false in
public theorem dvd_matrix_mul_of_right {l m n : Type _} {R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    {d : R} {A : _root_.Matrix l m R} {B : _root_.Matrix m n R}
    (hB : ∀ row column, d ∣ B row column) :
    ∀ row column, d ∣ (A * B) row column := by
  intro row column
  rw [_root_.Matrix.mul_apply]
  refine Finset.dvd_sum ?_
  intro index _member
  rcases hB index column with ⟨coefficient, equality⟩
  refine ⟨A row index * coefficient, ?_⟩
  calc
    A row index * B index column =
        A row index * (d * coefficient) := by rw [equality]
    _ = d * (A row index * coefficient) := by ring

set_option linter.unusedDecidableInType false in
public theorem dvd_matrix_mul_of_left {l m n : Type _} {R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    {d : R} {A : _root_.Matrix l m R} {B : _root_.Matrix m n R}
    (hA : ∀ row column, d ∣ A row column) :
    ∀ row column, d ∣ (A * B) row column := by
  intro row column
  rw [_root_.Matrix.mul_apply]
  refine Finset.dvd_sum ?_
  intro index _member
  rcases hA row index with ⟨coefficient, equality⟩
  refine ⟨coefficient * B index column, ?_⟩
  calc
    A row index * B index column =
        (d * coefficient) * B index column := by rw [equality]
    _ = d * (coefficient * B index column) := by ring

/-- A cleared first row factors the determinant through the lower-right block. -/
public theorem det_eq_pivot_mul_lowerRight {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hrow : FirstRowCleared A) :
    A.det = A 0 0 * (lowerRight A).det := by
  rw [_root_.Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have tailZero :
      (∑ column : Fin n,
        (-1 : Int) ^ (column.succ : Nat) * A 0 column.succ *
          (A.submatrix Fin.succ column.succ.succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro column _member
    rw [hrow column]
    ring
  have lowerRightEq :
      A.submatrix Fin.succ Fin.succ = lowerRight A := rfl
  rw [tailZero]
  simp only [Fin.val_zero, pow_zero, one_mul, add_zero,
    Fin.succAbove_zero]
  rw [lowerRightEq]

/-- The lower-right block below a stable nonsingular pivot is nonsingular. -/
public theorem stable_lowerRight_det_ne_zero {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (stable : StablePivot A) (hdet : A.det ≠ 0) :
    (lowerRight A).det ≠ 0 := by
  intro hlower
  apply hdet
  rw [det_eq_pivot_mul_lowerRight A stable.firstRowCleared, hlower,
    mul_zero]

/-- Assemble one stable pivot and a recursive lower-right Smith result. -/
@[expose] public def assemble {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (stabilized : Stabilization A)
    (lower : SNFResultFin
      (lowerRight stabilized.certificate.result)) :
    SNFResultFin A := by
  let lowerCertificate : TwoSidedCertificate
      (lowerRight stabilized.certificate.result) :=
    { U := lower.U
      U_cert := lower.U_cert
      result := lower.S
      V := lower.V
      V_cert := lower.V_cert
      equation := lower.equation }
  let lifted := liftLowerCertificate stabilized.certificate.result
    stabilized.stable lowerCertificate
  let final := compose stabilized.certificate lifted
  refine
    { U := final.U
      U_cert := final.U_cert
      S := final.result
      V := final.V
      V_cert := final.V_cert
      equation := final.equation
      isSmith := ?_ }
  change IsSmithNormalFormFin
    (adjoinPivot (stabilized.certificate.result 0 0) lower.S)
  refine IsSmithNormalFormFin.pivot _ ?_ ?_ ?_ ?_ ?_ ?_
  · exact stabilized.stable.pivot_ne_zero
  · exact stabilized.stable.pivot_normalized
  · intro column
    simp
  · intro row
    simp
  · simpa using lower.isSmith
  · intro row column
    rw [adjoinPivot_succ_succ, ← lower.equation]
    exact dvd_matrix_mul_of_left
      (dvd_matrix_mul_of_right stabilized.stable.pivotDividesLower)
      row column

/--
Total nonsingular square Kannan--Bachem SNF.  Dimension recursion is structural;
each active pivot is stabilized by the well-founded binary-size loop.
-/
@[expose] public def smith : {n : Nat} →
    (A : _root_.Matrix (Fin n) (Fin n) Int) → A.det ≠ 0 → SNFResultFin A
  | 0, A, _hdet =>
      { U := 1
        U_cert := MatrixInverseCertificate.one
        S := A
        V := 1
        V_cert := MatrixInverseCertificate.one
        equation := NormalForms.Matrix.Constructive.one_mul_mul_one A
        isSmith := IsSmithNormalFormFin.emptyRows A }
  | _n + 1, A, hdet =>
      let stabilized := stabilize A hdet
      let transformed := stabilized.certificate.result
      let transformedDet : transformed.det ≠ 0 :=
        stabilized.result_det_ne_zero hdet
      let lowerDet : (lowerRight transformed).det ≠ 0 :=
        stable_lowerRight_det_ne_zero transformed stabilized.stable
          transformedDet
      assemble stabilized (smith (lowerRight transformed) lowerDet)

public theorem smith_sound {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smith A hdet).U * A * (smith A hdet).V = (smith A hdet).S ∧
      (smith A hdet).U_cert.inverse * (smith A hdet).S *
          (smith A hdet).V_cert.inverse = A ∧
      IsSmithNormalFormFin (smith A hdet).S := by
  exact ⟨(smith A hdet).equation,
    NormalForms.Research.KannanBachem.Smith.inverse_equation
      { U := (smith A hdet).U
        U_cert := (smith A hdet).U_cert
        result := (smith A hdet).S
        V := (smith A hdet).V
        V_cert := (smith A hdet).V_cert
        equation := (smith A hdet).equation },
    (smith A hdet).isSmith⟩

/-- The total research algorithm computes the canonical core Smith matrix. -/
public theorem smith_eq_reference {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smith A hdet).S = (smithNormalFormFin A).S := by
  let result := smith A hdet
  let reference := smithNormalFormFin A
  let left := reference.U * result.U_cert.inverse
  let right := result.V_cert.inverse * reference.V
  have leftCertificate : MatrixInverseCertificate left :=
    reference.U_cert.mul result.U_cert.symm
  have rightCertificate : MatrixInverseCertificate right :=
    result.V_cert.symm.mul reference.V_cert
  apply Internal.isSmithNormalFormFin_unique_of_two_sided_equiv
    result.isSmith reference.isSmith leftCertificate.unimodular
      rightCertificate.unimodular
  calc
    left * result.S * right =
        reference.U *
          (result.U_cert.inverse * result.S *
            result.V_cert.inverse) * reference.V := by
      simp only [left, right, _root_.Matrix.mul_assoc]
    _ = reference.U * A * reference.V := by
      rw [(smith_sound A hdet).2.1]
    _ = reference.S := reference.equation

/--
Fuelled nonsingular square Kannan--Bachem SNF.  Success returns the frozen
strong result; `none` means that some active stabilization exhausted its fuel.
-/
@[expose] public def smith? : {n : Nat} →
    (fuel : Nat) → (A : _root_.Matrix (Fin n) (Fin n) Int) →
      A.det ≠ 0 → Option (SNFResultFin A)
  | 0, _fuel, A, _hdet =>
      some
        { U := 1
          U_cert := MatrixInverseCertificate.one
          S := A
          V := 1
          V_cert := MatrixInverseCertificate.one
          equation := NormalForms.Matrix.Constructive.one_mul_mul_one A
          isSmith := IsSmithNormalFormFin.emptyRows A }
  | _n + 1, fuel, A, hdet =>
      match stabilize? fuel A hdet with
      | none => none
      | some stabilized =>
          let transformed := stabilized.certificate.result
          let transformedDet : transformed.det ≠ 0 :=
            stabilized.result_det_ne_zero hdet
          let lowerDet : (lowerRight transformed).det ≠ 0 :=
            stable_lowerRight_det_ne_zero transformed stabilized.stable
              transformedDet
          match smith? fuel (lowerRight transformed) lowerDet with
          | none => none
          | some lower => some (assemble stabilized lower)

public theorem smith?_sound {n fuel : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0)
    {result : SNFResultFin A} (_success : smith? fuel A hdet = some result) :
    result.U * A * result.V = result.S ∧
      result.U_cert.inverse * result.S * result.V_cert.inverse = A ∧
      IsSmithNormalFormFin result.S := by
  exact ⟨result.equation,
    NormalForms.Research.KannanBachem.Smith.inverse_equation
      { U := result.U
        U_cert := result.U_cert
        result := result.S
        V := result.V
        V_cert := result.V_cert
        equation := result.equation },
    result.isSmith⟩

/-- Every successful research run computes the canonical core Smith matrix. -/
public theorem smith?_eq_reference {n fuel : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0)
    {result : SNFResultFin A} (success : smith? fuel A hdet = some result) :
    result.S = (smithNormalFormFin A).S := by
  let reference := smithNormalFormFin A
  let left := reference.U * result.U_cert.inverse
  let right := result.V_cert.inverse * reference.V
  have leftCertificate : MatrixInverseCertificate left :=
    reference.U_cert.mul result.U_cert.symm
  have rightCertificate : MatrixInverseCertificate right :=
    result.V_cert.symm.mul reference.V_cert
  apply Internal.isSmithNormalFormFin_unique_of_two_sided_equiv
    result.isSmith reference.isSmith leftCertificate.unimodular
      rightCertificate.unimodular
  calc
    left * result.S * right =
        reference.U *
          (result.U_cert.inverse * result.S *
            result.V_cert.inverse) * reference.V := by
      simp only [left, right, _root_.Matrix.mul_assoc]
    _ = reference.U * A * reference.V := by
      rw [(smith?_sound A hdet success).2.1]
    _ = reference.S := reference.equation

end NormalForms.Research.KannanBachem.Smith
