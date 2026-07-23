/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.CoefficientSize
public import NormalForms.Research.KannanBachem.Smith.RecursiveOperationBound
import all NormalForms.Research.KannanBachem.Smith.Recursive

/-!
# Polynomial coefficient bounds for total Kannan--Bachem SNF

The bounds in this module include the Smith matrix, both accumulated
transformations, and both explicitly accumulated inverses across every
lower-right recursive level.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith
open NormalForms.Research.KannanBachem.Hermite

theorem lowerRight_height_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    matrixHeight (lowerRight A) ≤ matrixHeight A := by
  apply matrixHeight_le
  intro row column
  exact entry_natAbs_le_matrixHeight A row.succ column.succ

theorem lowerRight_bitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    matrixBitLength (lowerRight A) ≤ matrixBitLength A :=
  Nat.size_le_size (lowerRight_height_le A)

theorem leadingLiftMatrix_height_le {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    matrixHeight (leadingLiftMatrix A) ≤ max 1 (matrixHeight A) := by
  apply matrixHeight_le
  intro row column
  cases row using Fin.cases with
  | zero =>
      cases column using Fin.cases <;> simp [leadingLiftMatrix]
  | succ row =>
      cases column using Fin.cases with
      | zero => simp [leadingLiftMatrix]
      | succ column =>
          exact (entry_natAbs_le_matrixHeight A row column).trans
            (le_max_right _ _)

theorem natSize_max (left right : Nat) :
    Nat.size (max left right) = max (Nat.size left) (Nat.size right) := by
  rcases le_total left right with hle | hle
  · rw [max_eq_right hle, max_eq_right (Nat.size_le_size hle)]
  · rw [max_eq_left hle, max_eq_left (Nat.size_le_size hle)]

theorem natSize_max_one (height : Nat) :
    Nat.size (max 1 height) = max 1 (Nat.size height) := by
  simpa using natSize_max 1 height

theorem leadingLiftMatrix_bitLength_le {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    matrixBitLength (leadingLiftMatrix A) ≤ max 1 (matrixBitLength A) := by
  unfold matrixBitLength
  refine (Nat.size_le_size (leadingLiftMatrix_height_le A)).trans ?_
  exact (natSize_max_one _).le

theorem liftLowerCertificate_transformBitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (stable : StablePivot A)
    (lower : TwoSidedCertificate (lowerRight A)) :
    certificateTransformBitLength (liftLowerCertificate A stable lower) ≤
      max 1 (certificateTransformBitLength lower) := by
  have lowerU : matrixBitLength lower.U ≤
      certificateTransformBitLength lower := le_max_left _ _
  have lowerUInv : matrixBitLength lower.U_cert.inverse ≤
      certificateTransformBitLength lower :=
    (le_max_left _ _).trans (le_max_right _ _)
  have lowerV : matrixBitLength lower.V ≤
      certificateTransformBitLength lower :=
    (le_max_left _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
  have lowerVInv : matrixBitLength lower.V_cert.inverse ≤
      certificateTransformBitLength lower :=
    (le_max_right _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
  have liftBound (B : Matrix (Fin n) (Fin n) Int)
      (hB : matrixBitLength B ≤ certificateTransformBitLength lower) :
      matrixBitLength (leadingLiftMatrix B) ≤
        max 1 (certificateTransformBitLength lower) :=
    (leadingLiftMatrix_bitLength_le B).trans <|
      max_le (le_max_left _ _) (hB.trans (le_max_right _ _))
  unfold certificateTransformBitLength liftLowerCertificate
    leadingLiftCertificate
  apply max_le
  · exact liftBound lower.U lowerU
  · apply max_le
    · exact liftBound lower.U_cert.inverse lowerUInv
    · apply max_le
      · exact liftBound lower.V lowerV
      · exact liftBound lower.V_cert.inverse lowerVInv

@[expose] def snfCertificate {n : Nat} {A : Matrix (Fin n) (Fin n) Int}
    (result : SNFResultFin A) : TwoSidedCertificate A :=
  { U := result.U
    U_cert := result.U_cert
    result := result.S
    V := result.V
    V_cert := result.V_cert
    equation := result.equation }

@[expose] def smithTransformBitLength {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) : Nat :=
  certificateTransformBitLength (snfCertificate result)

@[expose] def stabilizationTransformWorkBound (dimension workBits : Nat) : Nat :=
  (3 * workBits + 2) *
    stabilizationCompositionBitLength (dimension - 1) workBits

theorem stabilize_transformBitLength_le_work {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0)
    (matrixBound : matrixBitLength A ≤ workBits)
    (detBound : integerBitLength A.det ≤ workBits) :
    certificateTransformBitLength (stabilize A hdet).certificate ≤
      stabilizationTransformWorkBound (n + 1) workBits := by
  let initial := pass A hdet
  have initialMatrixBound : matrixBitLength initial.result ≤ workBits :=
    (pass_result_bitLength_le_determinant A hdet).trans detBound
  have initialDetBits :
      integerBitLength initial.result.det = integerBitLength A.det :=
    congrArg Nat.size (certificate_result_det_natAbs initial)
  have initialBound : certificateTransformBitLength initial ≤
      stabilizationFactorBitLengthBound n workBits :=
    pass_transformBitLength_le_uniform A hdet
      (matrixBound.trans (by omega)) detBound
  have restBound := stabilizeFrom_transformBitLength_le initial.result
    (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
    (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
    initialMatrixBound (initialDetBits ▸ detBound)
  have compositionBound := compose_transformBitLength_le initial
    (stabilizeFrom initial.result (pass_result_det_ne_zero A hdet)
      (pass_shape A hdet).1 (pass_shape A hdet).2.1
      (pass_shape A hdet).2.2).certificate
  have pivotBound : (initial.result 0 0).natAbs.size ≤ workBits :=
    (pass_pivotBitLength_le_determinant A hdet).trans detBound
  change certificateTransformBitLength
      (compose initial
        (stabilizeFrom initial.result (pass_result_det_ne_zero A hdet)
          (pass_shape A hdet).1 (pass_shape A hdet).2.1
          (pass_shape A hdet).2.2).certificate) ≤ _
  unfold stabilizationTransformWorkBound
  simp only [Nat.add_sub_cancel]
  calc
    certificateTransformBitLength
        (compose initial
          (stabilizeFrom initial.result (pass_result_det_ne_zero A hdet)
            (pass_shape A hdet).1 (pass_shape A hdet).2.1
            (pass_shape A hdet).2.2).certificate) ≤
        Nat.size (n + 1) + certificateTransformBitLength initial +
          certificateTransformBitLength
            (stabilizeFrom initial.result (pass_result_det_ne_zero A hdet)
              (pass_shape A hdet).1 (pass_shape A hdet).2.1
              (pass_shape A hdet).2.2).certificate := compositionBound
    _ ≤ stabilizationCompositionBitLength n workBits +
          (3 * (initial.result 0 0).natAbs.size + 1) *
            stabilizationCompositionBitLength n workBits := by
      unfold stabilizationCompositionBitLength
      exact Nat.add_le_add
        (Nat.add_le_add_left initialBound _)
        restBound
    _ = (3 * (initial.result 0 0).natAbs.size + 2) *
          stabilizationCompositionBitLength n workBits := by ring
    _ ≤ (3 * workBits + 2) *
          stabilizationCompositionBitLength n workBits := by
      apply Nat.mul_le_mul_right
      omega

@[expose] def smithTransformWorkBound : Nat → Nat → Nat
  | 0, _workBits => 0
  | dimension + 1, workBits =>
      Nat.size (dimension + 1) +
        stabilizationTransformWorkBound (dimension + 1) workBits +
        max 1 (smithTransformWorkBound dimension workBits)

@[expose] def smithMatrixWorkBound (_dimension workBits : Nat) : Nat := workBits

theorem smith_transformBitLength_le_work {n workBits : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0)
    (matrixBound : matrixBitLength A ≤ workBits)
    (detBound : integerBitLength A.det ≤ workBits) :
    smithTransformBitLength (smith A hdet) ≤
      smithTransformWorkBound n workBits := by
  induction n with
  | zero =>
      simp [smith, smithTransformBitLength, snfCertificate,
        certificateTransformBitLength, smithTransformWorkBound,
        matrixBitLength, matrixHeight]
  | succ n ih =>
      let stabilized := stabilize A hdet
      let transformed := stabilized.certificate.result
      let transformedDet : transformed.det ≠ 0 :=
        stabilized.result_det_ne_zero hdet
      let lowerDet : (lowerRight transformed).det ≠ 0 :=
        stable_lowerRight_det_ne_zero transformed stabilized.stable
          transformedDet
      let lower := smith (lowerRight transformed) lowerDet
      let lowerCertificate := snfCertificate lower
      let lifted := liftLowerCertificate transformed stabilized.stable
        lowerCertificate
      have stabilizedBound :
          certificateTransformBitLength stabilized.certificate ≤
            stabilizationTransformWorkBound (n + 1) workBits := by
        exact stabilize_transformBitLength_le_work A hdet matrixBound detBound
      have transformedMatrixBound : matrixBitLength transformed ≤ workBits :=
        (stabilize_result_bitLength_le_determinant A hdet).trans detBound
      have lowerMatrixBound :
          matrixBitLength (lowerRight transformed) ≤ workBits :=
        (lowerRight_bitLength_le transformed).trans transformedMatrixBound
      have lowerDetBound :
          integerBitLength (lowerRight transformed).det ≤ workBits :=
        (Nat.size_le_size (stabilization_lowerRight_det_natAbs_le A hdet)).trans
          detBound
      have recursiveBound : smithTransformBitLength lower ≤
          smithTransformWorkBound n workBits :=
        ih (lowerRight transformed) lowerDet lowerMatrixBound lowerDetBound
      have liftedBound : certificateTransformBitLength lifted ≤
          max 1 (smithTransformWorkBound n workBits) := by
        exact (liftLowerCertificate_transformBitLength_le transformed
          stabilized.stable lowerCertificate).trans <| by
            exact max_le (le_max_left _ _) <|
              recursiveBound.trans (le_max_right _ _)
      have compositionBound := compose_transformBitLength_le
        stabilized.certificate lifted
      change certificateTransformBitLength
          (compose stabilized.certificate lifted) ≤ _
      rw [smithTransformWorkBound]
      exact compositionBound.trans <|
        Nat.add_le_add
          (Nat.add_le_add_left stabilizedBound _)
          liftedBound

@[expose] def smithCoefficientWorkBitLength (dimension inputBits : Nat) : Nat :=
  max inputBits (determinantBitLengthBound dimension inputBits)

@[expose] def smithCertificatePolynomialBitLengthBound
    (dimension inputBits : Nat) : Nat :=
  smithTransformWorkBound dimension
    (smithCoefficientWorkBitLength dimension inputBits)

theorem smith_transformBitLength_le_polynomial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    smithTransformBitLength (smith A hdet) ≤
      smithCertificatePolynomialBitLengthBound n (matrixBitLength A) := by
  apply smith_transformBitLength_le_work A hdet
  · exact le_max_left _ _
  · exact (determinant_bitLength_le A).trans (le_max_right _ _)

theorem adjoinPivot_height_le {n : Nat} (pivot : Int)
    (lower : Matrix (Fin n) (Fin n) Int) :
    matrixHeight (adjoinPivot pivot lower) ≤
      max pivot.natAbs (matrixHeight lower) := by
  apply matrixHeight_le
  intro row column
  cases row using Fin.cases with
  | zero =>
      cases column using Fin.cases <;> simp [adjoinPivot]
  | succ row =>
      cases column using Fin.cases with
      | zero => simp [adjoinPivot]
      | succ column =>
          exact (entry_natAbs_le_matrixHeight lower row column).trans
            (le_max_right _ _)

theorem adjoinPivot_bitLength_le {n : Nat} (pivot : Int)
    (lower : Matrix (Fin n) (Fin n) Int) :
    matrixBitLength (adjoinPivot pivot lower) ≤
      max (integerBitLength pivot) (matrixBitLength lower) := by
  unfold matrixBitLength integerBitLength
  refine (Nat.size_le_size (adjoinPivot_height_le pivot lower)).trans ?_
  exact (natSize_max _ _).le

theorem smith_result_bitLength_le_work {n workBits : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0)
    (detBound : integerBitLength A.det ≤ workBits) :
    matrixBitLength (smith A hdet).S ≤ workBits := by
  induction n with
  | zero =>
      simp [smith, matrixBitLength, matrixHeight]
  | succ n ih =>
      let stabilized := stabilize A hdet
      let transformed := stabilized.certificate.result
      let transformedDet : transformed.det ≠ 0 :=
        stabilized.result_det_ne_zero hdet
      let lowerDet : (lowerRight transformed).det ≠ 0 :=
        stable_lowerRight_det_ne_zero transformed stabilized.stable
          transformedDet
      let lower := smith (lowerRight transformed) lowerDet
      have pivotBound : integerBitLength (transformed 0 0) ≤ workBits :=
        (entry_bitLength_le_matrixBitLength transformed 0 0).trans <|
          (stabilize_result_bitLength_le_determinant A hdet).trans detBound
      have lowerDetBound :
          integerBitLength (lowerRight transformed).det ≤ workBits :=
        (Nat.size_le_size (stabilization_lowerRight_det_natAbs_le A hdet)).trans
          detBound
      have lowerBound : matrixBitLength lower.S ≤ workBits :=
        ih (lowerRight transformed) lowerDet lowerDetBound
      change matrixBitLength
        (adjoinPivot (transformed 0 0) lower.S) ≤ workBits
      exact (adjoinPivot_bitLength_le (transformed 0 0) lower.S).trans <|
        max_le pivotBound lowerBound

theorem smith_result_bitLength_le_polynomial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    matrixBitLength (smith A hdet).S ≤
      determinantBitLengthBound n (matrixBitLength A) :=
  smith_result_bitLength_le_work A hdet (determinant_bitLength_le A)

structure SmithCoefficientProfile {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) where
  resultBitLength : Nat
  leftBitLength : Nat
  leftInverseBitLength : Nat
  rightBitLength : Nat
  rightInverseBitLength : Nat

@[expose] def smithCoefficientProfile {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) :
    SmithCoefficientProfile result :=
  { resultBitLength := matrixBitLength result.S
    leftBitLength := matrixBitLength result.U
    leftInverseBitLength := matrixBitLength result.U_cert.inverse
    rightBitLength := matrixBitLength result.V
    rightInverseBitLength := matrixBitLength result.V_cert.inverse }

theorem smith_coefficientProfile_le_polynomial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    let profile := smithCoefficientProfile (smith A hdet)
    profile.resultBitLength ≤
        determinantBitLengthBound n (matrixBitLength A) ∧
      profile.leftBitLength ≤
        smithCertificatePolynomialBitLengthBound n (matrixBitLength A) ∧
      profile.leftInverseBitLength ≤
        smithCertificatePolynomialBitLengthBound n (matrixBitLength A) ∧
      profile.rightBitLength ≤
        smithCertificatePolynomialBitLengthBound n (matrixBitLength A) ∧
      profile.rightInverseBitLength ≤
        smithCertificatePolynomialBitLengthBound n (matrixBitLength A) := by
  dsimp only [smithCoefficientProfile]
  have transformBound := smith_transformBitLength_le_polynomial A hdet
  exact ⟨smith_result_bitLength_le_polynomial A hdet,
    (le_max_left _ _).trans transformBound,
    ((le_max_left _ _).trans (le_max_right _ _)).trans transformBound,
    ((le_max_left _ _).trans <| (le_max_right _ _).trans
      (le_max_right _ _)).trans transformBound,
    ((le_max_right _ _).trans <| (le_max_right _ _).trans
      (le_max_right _ _)).trans transformBound⟩

end NormalForms.Research.KannanBachem.Smith
