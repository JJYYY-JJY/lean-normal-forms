/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Hermite
public import NormalForms.Research.KannanBachem.Smith.Pass

/-! # Instrumented Kannan--Bachem Pass -/

public section

namespace NormalForms.Research.KannanBachem

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

/-- Execute the bounded left-Hermite phase once. -/
@[expose] public def leftHermitePhaseExecution {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    CertificateExecution A := by
  let hnf := boundedColumnExecution A
  let value : TwoSidedCertificate A :=
    { U := hnf.value.U
      U_cert := hnf.value.U_cert
      result := hnf.matrix
      V := 1
      V_cert := MatrixInverseCertificate.one
      equation := by
        rw [Matrix.mul_one]
        exact hnf.fullEquation }
  exact
    { value
      charges := hnf.charges
      trace_wellFormed := hnf.trace_wellFormed
      chargeOwnership := hnf.chargeOwnership }

public theorem leftHermitePhaseExecution_value {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (leftHermitePhaseExecution A).value = leftHermitePhase A := by
  apply twoSidedCertificate_ext_data
  · exact congrArg (fun result ↦ result.U) (boundedColumnExecution_value A)
  · exact congrArg (fun result ↦ result.U_cert.inverse)
      (boundedColumnExecution_value A)
  · change (boundedColumnExecution A).matrix =
      (boundedColumnHermiteNormalForm A).U * A
    exact (boundedColumnExecution A).fullEquation.symm.trans <|
      congrArg (fun U ↦ U * A) <|
        congrArg (fun result ↦ result.U) (boundedColumnExecution_value A)
  · rfl
  · rfl

/-- Execute the transposed prepared-principal phase once. -/
@[expose] public def rightHermitePhaseExecution {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    CertificateExecution A := by
  let hnf := preparedPrincipalExecution A.transpose (by simpa using hdet)
  let value : TwoSidedCertificate A :=
    { U := 1
      U_cert := MatrixInverseCertificate.one
      result := hnf.value.H.transpose
      V := hnf.value.U.transpose
      V_cert := hnf.value.U_cert.transpose
      equation := by
        rw [Matrix.one_mul]
        have equation := congrArg Matrix.transpose hnf.value.equation
        simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using equation }
  exact
    { value
      charges := hnf.charges
      trace_wellFormed := hnf.trace_wellFormed
      chargeOwnership := hnf.chargeOwnership }

public theorem rightHermitePhaseExecution_value {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (rightHermitePhaseExecution A hdet).value =
      rightHermitePhase A hdet := by
  apply twoSidedCertificate_ext_data
  · rfl
  · rfl
  · exact congrArg (fun result ↦ result.H.transpose)
      (preparedPrincipalExecution_value A.transpose (by simpa using hdet))
  · exact congrArg (fun result ↦ result.U.transpose)
      (preparedPrincipalExecution_value A.transpose (by simpa using hdet))
  · exact congrArg (fun result ↦ result.U_cert.transpose.inverse)
      (preparedPrincipalExecution_value A.transpose (by simpa using hdet))

/-- One value-producing Step-4/Step-5 pass. -/
@[expose] public def passExecution {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    CertificateExecution A :=
  let left := leftHermitePhaseExecution A
  let right := rightHermitePhaseExecution left.value.result
    (result_det_ne_zero left.value hdet)
  composeExecution left right

public theorem passExecution_value {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (passExecution A hdet).value = pass A hdet := by
  rw [passExecution, composeExecution_value]
  let left := leftHermitePhaseExecution A
  let leftDet := result_det_ne_zero left.value hdet
  let right := rightHermitePhaseExecution left.value.result leftDet
  have rightValue :
      right.value = rightHermitePhase left.value.result leftDet :=
    rightHermitePhaseExecution_value left.value.result leftDet
  calc
    compose left.value right.value =
        compose left.value
          (rightHermitePhase left.value.result leftDet) :=
      congrArg (compose left.value) rightValue
    _ = compose (leftHermitePhase A)
          (rightHermitePhase (leftHermitePhase A).result
            (result_det_ne_zero (leftHermitePhase A) hdet)) :=
      congrArg
        (fun first ↦ compose first
          (rightHermitePhase first.result
            (result_det_ne_zero first hdet)))
        (leftHermitePhaseExecution_value A)
    _ = pass A hdet := rfl

/-- Actual pass budget, including both HNF executions and four products. -/
@[expose] public def passExecutionBitOperationBound
    (order inputBits determinantBits : Nat) : Nat :=
  let dimension := order + 1
  let leftBits :=
    boundedColumnIntermediatePolynomialBitLengthBound dimension inputBits
  let transformBits :=
    passPhaseTransformBitLengthBound order inputBits determinantBits
  boundedColumnExecutionBitOperationBound dimension inputBits +
    preparedPrincipalExecutionBitOperationBound dimension leftBits +
    certificateCompositionBitOperationBound dimension
      transformBits transformBits

set_option maxHeartbeats 800000 in
-- The certificate-component bounds require normalizing several nested maxima.
public theorem passExecution_cost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    traceBitCost (passExecution A hdet).charges ≤
      passExecutionBitOperationBound n (matrixBitLength A)
        (integerBitLength A.det) := by
  let left := leftHermitePhaseExecution A
  let leftDet := result_det_ne_zero left.value hdet
  let right := rightHermitePhaseExecution left.value.result leftDet
  let leftBits :=
    boundedColumnIntermediatePolynomialBitLengthBound
      (n + 1) (matrixBitLength A)
  let transformBits :=
    passPhaseTransformBitLengthBound n (matrixBitLength A)
      (integerBitLength A.det)
  have leftCost :
      traceBitCost left.charges ≤
        boundedColumnExecutionBitOperationBound
          (n + 1) (matrixBitLength A) := by
    exact boundedColumnExecution_cost_le A hdet
  have leftResultBits :
      matrixBitLength left.value.result ≤ leftBits := by
    rw [leftHermitePhaseExecution_value]
    exact leftHermitePhase_result_bitLength_le A
  have rightCost :
      traceBitCost right.charges ≤
        preparedPrincipalExecutionBitOperationBound (n + 1) leftBits := by
    exact (preparedPrincipalExecution_cost_le
      left.value.result.transpose (by simpa using leftDet)).trans <| by
        apply preparedPrincipalExecutionBitOperationBound_mono_right
        rw [matrixBitLength_transpose]
        exact leftResultBits
  have phaseBounds := pass_phase_transformBitLength_le A hdet
  have leftTransform :
      certificateTransformBitLength left.value ≤ transformBits := by
    rw [leftHermitePhaseExecution_value]
    exact phaseBounds.1
  have rightTransform :
      certificateTransformBitLength right.value ≤ transformBits := by
    let hnf := preparedPrincipalExecution
      left.value.result.transpose (by simpa using leftDet)
    have detBitsEq :
        integerBitLength left.value.result.det =
          integerBitLength A.det :=
      congrArg Nat.size (certificate_result_det_natAbs left.value)
    have rightForwardRaw :=
      preparedPrincipal_multiplier_bitLength_le
        left.value.result.transpose (by simpa using leftDet)
    have rightInverseRaw :=
      preparedPrincipal_inverse_bitLength_le
        left.value.result.transpose (by simpa using leftDet)
    have rightForward :
        matrixBitLength hnf.value.U ≤
          preparedMultiplierBits n leftBits (integerBitLength A.det) := by
      rw [preparedPrincipalExecution_value]
      exact rightForwardRaw.trans <| by
        unfold preparedMultiplierBits
        rw [matrixBitLength_transpose, Matrix.det_transpose, detBitsEq]
        unfold determinantBitLengthBound
        gcongr
    have rightInverse :
        matrixBitLength hnf.value.U_cert.inverse ≤
          preparedInverseBits n leftBits (integerBitLength A.det) := by
      rw [preparedPrincipalExecution_value]
      exact rightInverseRaw.trans <| by
        unfold preparedInverseBits
        rw [matrixBitLength_transpose, Matrix.det_transpose, detBitsEq]
        unfold determinantBitLengthBound
        gcongr
    have oneBits :
        matrixBitLength
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) ≤
          transformBits :=
      matrixBitLength_one_le.trans <| by
        unfold transformBits passPhaseTransformBitLengthBound
        exact le_max_left _ _
    have passFits :
        passTransformBitLengthBound n (matrixBitLength A)
            (integerBitLength A.det) ≤ transformBits := by
      unfold transformBits passPhaseTransformBitLengthBound
      exact le_max_right _ _
    have rightForwardFits :
        preparedMultiplierBits n leftBits (integerBitLength A.det) ≤
          transformBits := by
      apply LE.le.trans (b :=
        passTransformBitLengthBound n (matrixBitLength A)
          (integerBitLength A.det))
      · unfold passTransformBitLengthBound
        exact (le_max_left _ _).trans <|
          (le_max_right _ _).trans (le_max_right _ _)
      · exact passFits
    have rightInverseFits :
        preparedInverseBits n leftBits (integerBitLength A.det) ≤
          transformBits := by
      apply LE.le.trans (b :=
        passTransformBitLengthBound n (matrixBitLength A)
          (integerBitLength A.det))
      · unfold passTransformBitLengthBound
        exact (le_max_right _ _).trans <|
          (le_max_right _ _).trans (le_max_right _ _)
      · exact passFits
    change
      max (matrixBitLength
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int))
        (max (matrixBitLength
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int))
          (max (matrixBitLength hnf.value.U.transpose)
            (matrixBitLength hnf.value.U_cert.inverse.transpose))) ≤
        transformBits
    simp only [matrixBitLength_transpose]
    apply max_le oneBits
    apply max_le oneBits
    exact max_le (rightForward.trans rightForwardFits)
      (rightInverse.trans rightInverseFits)
  have compositionCost :
      certificateCompositionBitOperationCost left.value right.value ≤
        certificateCompositionBitOperationBound
          (n + 1) transformBits transformBits :=
    certificateCompositionBitOperationCost_le left.value right.value
      leftTransform rightTransform
  rw [passExecution, composeExecution_cost_eq]
  unfold passExecutionBitOperationBound
  dsimp only
  exact Nat.add_le_add (Nat.add_le_add leftCost rightCost) compositionCost

public theorem passExecutionBitOperationBound_mono
    (order : Nat) {inputSmall inputLarge detSmall detLarge : Nat}
    (inputLe : inputSmall ≤ inputLarge) (detLe : detSmall ≤ detLarge) :
    passExecutionBitOperationBound order inputSmall detSmall ≤
      passExecutionBitOperationBound order inputLarge detLarge := by
  let dimension := order + 1
  have leftBitsLe :=
    boundedColumnIntermediateBound_mono_right dimension inputLe
  have transformLe :
      passPhaseTransformBitLengthBound order inputSmall detSmall ≤
        passPhaseTransformBitLengthBound order inputLarge detLarge := by
    unfold passPhaseTransformBitLengthBound
    exact max_le (le_max_left _ _) <|
      (passTransformBitLengthBound_mono
        (order := order) inputLe detLe).trans (le_max_right _ _)
  unfold passExecutionBitOperationBound
  exact Nat.add_le_add
    (Nat.add_le_add
      (boundedColumnExecutionBitOperationBound_mono_right
        dimension inputLe)
      (preparedPrincipalExecutionBitOperationBound_mono_right
        dimension leftBitsLe))
    (certificateCompositionBitOperationBound_mono
      dimension transformLe transformLe)

end NormalForms.Research.KannanBachem
