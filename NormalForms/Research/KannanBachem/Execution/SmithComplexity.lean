/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Smith
public import NormalForms.Research.KannanBachem.Execution.StabilizationComplexity
import all NormalForms.Research.KannanBachem.Smith.RecursiveCoefficientSize

/-! # Actual Arithmetic Bound for Instrumented Smith Recursion -/

public section

namespace NormalForms.Research.KannanBachem

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith
open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

/-- Closed dimension-recursive bound for the actual Smith leaf trace. -/
@[expose] public def smithExecutionBitOperationWorkBound : Nat → Nat → Nat
  | 0, _workBits => 0
  | dimension + 1, workBits =>
      stabilizationExecutionBitOperationBound (dimension + 1) workBits +
        smithExecutionBitOperationWorkBound dimension workBits +
        certificateCompositionBitOperationBound (dimension + 1)
          (stabilizationTransformWorkBound (dimension + 1) workBits)
          (max 1 (smithTransformWorkBound dimension workBits))

public theorem smithExecution_cost_le_work {n workBits : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0)
    (matrixBound : matrixBitLength A ≤ workBits)
    (detBound : integerBitLength A.det ≤ workBits) :
    traceBitCost (smithExecution A hdet).charges ≤
      smithExecutionBitOperationWorkBound n workBits := by
  induction n with
  | zero =>
      simp [smithExecution, emptySmithExecution,
        smithExecutionBitOperationWorkBound,
        traceBitCost]
  | succ n ih =>
      let stabilized := stabilizeExecution A hdet
      let transformed := stabilized.certificate.value.result
      let transformedDet : transformed.det ≠ 0 :=
        result_det_ne_zero stabilized.certificate.value hdet
      let lowerDet : (lowerRight transformed).det ≠ 0 :=
        stable_lowerRight_det_ne_zero transformed stabilized.stable
          transformedDet
      let lower := smithExecution (lowerRight transformed) lowerDet
      let lowerCertificateValue : TwoSidedCertificate
          (lowerRight transformed) :=
        { U := lower.value.U
          U_cert := lower.value.U_cert
          result := lower.value.S
          V := lower.value.V
          V_cert := lower.value.V_cert
          equation := lower.value.equation }
      let liftedValue := liftLowerCertificate
        transformed stabilized.stable lowerCertificateValue
      let lifted : CertificateExecution transformed :=
        { value := liftedValue
          charges := lower.charges
          trace_wellFormed := lower.trace_wellFormed }
      have stabilizationCost :
          traceBitCost stabilized.charges ≤
            stabilizationExecutionBitOperationBound (n + 1) workBits :=
        stabilizeExecution_cost_le A hdet matrixBound detBound
      have stabilizedValue :
          stabilized.certificate.value =
            (stabilize A hdet).certificate :=
        stabilizeExecution_replay A hdet
      have transformedMatrixBound : matrixBitLength transformed ≤ workBits := by
        simpa [transformed, stabilizedValue] using
          (stabilize_result_bitLength_le_determinant A hdet).trans detBound
      have lowerMatrixBound :
          matrixBitLength (lowerRight transformed) ≤ workBits :=
        (lowerRight_bitLength_le transformed).trans transformedMatrixBound
      have lowerDetBound :
          integerBitLength (lowerRight transformed).det ≤ workBits := by
        have detLe := stabilization_lowerRight_det_natAbs_le A hdet
        rw [show (stabilize A hdet).certificate.result = transformed by
          simpa [transformed] using
            (congrArg (fun certificate ↦ certificate.result)
              stabilizedValue).symm]
          at detLe
        exact (Nat.size_le_size detLe).trans detBound
      have recursiveCost :
          traceBitCost lower.charges ≤
            smithExecutionBitOperationWorkBound n workBits :=
        ih (lowerRight transformed) lowerDet
          lowerMatrixBound lowerDetBound
      have stabilizedTransform :
          certificateTransformBitLength stabilized.certificate.value ≤
            stabilizationTransformWorkBound (n + 1) workBits := by
        rw [stabilizedValue]
        exact stabilize_transformBitLength_le_work
          A hdet matrixBound detBound
      have recursiveTransform :
          smithTransformBitLength lower.value ≤
            smithTransformWorkBound n workBits := by
        rw [smithExecution_value]
        exact smith_transformBitLength_le_work
          (lowerRight transformed) lowerDet
          lowerMatrixBound lowerDetBound
      have liftedTransform :
          certificateTransformBitLength lifted.value ≤
            max 1 (smithTransformWorkBound n workBits) := by
        apply (liftLowerCertificate_transformBitLength_le
          transformed stabilized.stable lowerCertificateValue).trans
        exact max_le (le_max_left _ _) <| by
          simpa [lifted, liftedValue, lowerCertificateValue,
            smithTransformBitLength, snfCertificate] using
              recursiveTransform.trans (le_max_right _ _)
      have compositionCost :
          certificateCompositionBitOperationCost
              stabilized.certificate.value lifted.value ≤
            certificateCompositionBitOperationBound (n + 1)
              (stabilizationTransformWorkBound (n + 1) workBits)
              (max 1 (smithTransformWorkBound n workBits)) :=
        certificateCompositionBitOperationCost_le
          stabilized.certificate.value lifted.value
          stabilizedTransform liftedTransform
      rw [smithExecution, smithExecutionBitOperationWorkBound]
      change
        traceBitCost
            (composeExecution stabilized.certificate lifted).charges ≤ _
      rw [composeExecution_cost_eq]
      exact Nat.add_le_add
        (Nat.add_le_add stabilizationCost recursiveCost)
        compositionCost

/-- Original-input-width instance of the actual execution bound. -/
@[expose] public def smithExecutionPolynomialBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  smithExecutionBitOperationWorkBound dimension
    (smithCoefficientWorkBitLength dimension inputBits)

public theorem smithExecution_cost_le_polynomial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    traceBitCost (smithExecution A hdet).charges ≤
      smithExecutionPolynomialBitOperationBound
        n (matrixBitLength A) := by
  apply smithExecution_cost_le_work A hdet
  · exact le_max_left _ _
  · exact (determinant_bitLength_le A).trans (le_max_right _ _)

end NormalForms.Research.KannanBachem
