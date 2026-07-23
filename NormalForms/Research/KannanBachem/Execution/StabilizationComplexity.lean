/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Stabilization

/-! # Actual Arithmetic Bound for Instrumented Pivot Stabilization -/

public section

namespace NormalForms.Research.KannanBachem

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

/-- Width covering a composition of any two stabilization certificates. -/
@[expose] public def stabilizationExecutionTransformBitLengthBound
    (dimension workBits : Nat) : Nat :=
  Nat.size dimension +
    2 * stabilizationTransformWorkBound dimension workBits

/-- Dense-product budget at the execution composition width. -/
@[expose] public def stabilizationExecutionCompositionBitOperationBound
    (dimension workBits : Nat) : Nat :=
  let bits :=
    stabilizationExecutionTransformBitLengthBound dimension workBits
  certificateCompositionBitOperationBound dimension bits bits

private theorem stabilizationTransformWorkBound_le_execution
    (dimension workBits : Nat) :
    stabilizationTransformWorkBound dimension workBits ≤
      stabilizationExecutionTransformBitLengthBound dimension workBits := by
  unfold stabilizationExecutionTransformBitLengthBound
  omega

private theorem certificateCompositionBitOperationCost_le_execution
    {dimension workBits : Nat}
    {A : Matrix (Fin dimension) (Fin dimension) Int}
    (first : TwoSidedCertificate A)
    (second : TwoSidedCertificate first.result)
    (firstBound : certificateTransformBitLength first ≤
      stabilizationExecutionTransformBitLengthBound dimension workBits)
    (secondBound : certificateTransformBitLength second ≤
      stabilizationExecutionTransformBitLengthBound dimension workBits) :
    certificateCompositionBitOperationCost first second ≤
      stabilizationExecutionCompositionBitOperationBound
        dimension workBits := by
  unfold stabilizationExecutionCompositionBitOperationBound
  exact certificateCompositionBitOperationCost_le first second
    firstBound secondBound

/-- Uniform actual-trace charge for one pivot-size descent level. -/
@[expose] public def stabilizationExecutionLevelBitOperationBound
    (dimension workBits : Nat) : Nat :=
  (dimension - 1) * smithSearchDecisionBitOperationBound workBits +
    (dimension - 1) * (dimension - 1) *
      smithSearchDecisionBitOperationBound workBits +
    passExecutionBitOperationBound (dimension - 1) (workBits + 1) workBits +
    clearExecutionBitOperationBound dimension workBits +
    injectExecutionBitOperationBound dimension workBits +
    3 * stabilizationExecutionCompositionBitOperationBound
      dimension workBits

/-- Closed actual-trace charge over all possible pivot-size descents. -/
@[expose] public def stabilizationExecutionBitOperationBound
    (dimension workBits : Nat) : Nat :=
  (workBits + 1) *
    stabilizationExecutionLevelBitOperationBound dimension workBits

set_option maxHeartbeats 1600000 in
-- Strong induction follows the pivot-size descent used by the executable.
public theorem stabilizeFromExecution_cost_le {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = _root_.normalize (A 0 0))
    (hrow : FirstRowCleared A)
    (matrixBound : matrixBitLength A ≤ workBits)
    (detBound : integerBitLength A.det ≤ workBits) :
    traceBitCost
        (stabilizeFromExecution A hdet hpivot hnormalized hrow).charges ≤
      (A 0 0).natAbs.size *
        stabilizationExecutionLevelBitOperationBound (n + 1) workBits := by
  generalize measureEq : (A 0 0).natAbs.size = measure
  induction measure using Nat.strong_induction_on generalizing A with
  | h measure ih =>
      rw [stabilizeFromExecution.eq_1]
      split
      next row hbadColumn =>
        let below := firstUndivisibleBelowWithCost A
        let current := passExecution A hdet
        have shape :
            current.value.result 0 0 ≠ 0 ∧
              current.value.result 0 0 =
                _root_.normalize (current.value.result 0 0) ∧
              FirstRowCleared current.value.result := by
          rw [passExecution_value]
          exact pass_shape A hdet
        let next := stabilizeFromExecution current.value.result
          (result_det_ne_zero current.value hdet)
          shape.1 shape.2.1 shape.2.2
        let prefixed := current.prependCharges below.charges
          below.trace_wellFormed
        have pureBadColumn :
            firstUndivisibleBelow? A = some row :=
          (firstUndivisibleBelowWithCost_value A).symm.trans hbadColumn
        have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
          A hdet hpivot row.succ
            (firstUndivisibleBelow?_some_not_dvd A pureBadColumn)
        have decreaseMeasure :
            (current.value.result 0 0).natAbs.size < measure := by
          simpa [current, measureEq, passExecution_value] using decrease
        have currentMatrixBound :
            matrixBitLength current.value.result ≤ workBits := by
          simp only [current, passExecution_value]
          exact (pass_result_bitLength_le_determinant A hdet).trans detBound
        have currentDetBits :
            integerBitLength current.value.result.det =
              integerBitLength A.det := by
          simp only [current, passExecution_value]
          exact congrArg Nat.size
            (certificate_result_det_natAbs (pass A hdet))
        have nextCost := ih _ decreaseMeasure current.value.result
          (result_det_ne_zero current.value hdet)
          shape.1 shape.2.1 shape.2.2 currentMatrixBound
          (currentDetBits ▸ detBound) rfl
        have belowCost :
            traceBitCost below.charges ≤
              n * smithSearchDecisionBitOperationBound workBits :=
          firstUndivisibleBelowWithCost_cost_le_uniform
            A workBits matrixBound
        have currentCost :
            traceBitCost current.charges ≤
              passExecutionBitOperationBound n (workBits + 1) workBits :=
          (passExecution_cost_le A hdet).trans <|
            passExecutionBitOperationBound_mono n
              (matrixBound.trans <| by omega) detBound
        have currentTransform :
            certificateTransformBitLength current.value ≤
              stabilizationTransformWorkBound (n + 1) workBits := by
          simp only [current, passExecution_value]
          exact (pass_transformBitLength_le_uniform A hdet
            (matrixBound.trans <| by omega) detBound).trans
              (stabilizationFactor_le_transformWorkBound n workBits)
        have currentPivotBound :
            (current.value.result 0 0).natAbs.size ≤ workBits :=
          (entry_bitLength_le_matrixBitLength current.value.result 0 0).trans
            currentMatrixBound
        have nextTransform :
            certificateTransformBitLength next.certificate.value ≤
              stabilizationTransformWorkBound (n + 1) workBits := by
          simp only [next, stabilizeFromExecution_replay]
          exact (stabilizeFrom_transformBitLength_le current.value.result
            (result_det_ne_zero current.value hdet)
            shape.1 shape.2.1 shape.2.2 currentMatrixBound
            (currentDetBits ▸ detBound)).trans <|
              stabilizationContinuation_le_transformWorkBound
                n workBits _ currentPivotBound
        have compositionCost :
            certificateCompositionBitOperationCost
                prefixed.value next.certificate.value ≤
              stabilizationExecutionCompositionBitOperationBound
                (n + 1) workBits := by
          have prefixedTransform :
              certificateTransformBitLength prefixed.value ≤
                stabilizationTransformWorkBound (n + 1) workBits := by
            simpa [prefixed] using currentTransform
          apply certificateCompositionBitOperationCost_le_execution
          · exact prefixedTransform.trans
              (stabilizationTransformWorkBound_le_execution _ _)
          · exact nextTransform.trans
              (stabilizationTransformWorkBound_le_execution _ _)
        simp only [StabilizationExecution.charges, composeExecution_cost_eq,
          CertificateExecution.prependCharges, traceBitCost_append]
        let level :=
          stabilizationExecutionLevelBitOperationBound (n + 1) workBits
        calc
          traceBitCost below.charges + traceBitCost current.charges +
                traceBitCost next.charges +
                certificateCompositionBitOperationCost
                  prefixed.value next.certificate.value ≤
              n * smithSearchDecisionBitOperationBound workBits +
                passExecutionBitOperationBound n (workBits + 1) workBits +
                (current.value.result 0 0).natAbs.size * level +
                stabilizationExecutionCompositionBitOperationBound
                  (n + 1) workBits :=
            Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add belowCost currentCost) nextCost)
              compositionCost
          _ ≤ level +
                (current.value.result 0 0).natAbs.size * level := by
            unfold level stabilizationExecutionLevelBitOperationBound
            simp only [Nat.add_sub_cancel]
            omega
          _ = ((current.value.result 0 0).natAbs.size + 1) * level := by
            ring
          _ ≤ measure * level :=
            Nat.mul_le_mul_right level (Nat.succ_le_iff.mpr decreaseMeasure)
      next hbadColumn =>
        let below := firstUndivisibleBelowWithCost A
        have pureNoBadColumn :
            firstUndivisibleBelow? A = none :=
          (firstUndivisibleBelowWithCost_value A).symm.trans hbadColumn
        let hdiv := firstUndivisibleBelow?_eq_none A pureNoBadColumn
        let cleared := clearExecution A hpivot hdiv
        have clearedValue :
            cleared.value = clearDivisibleFirstColumn A :=
          clearExecution_value A hpivot hdiv
        have clearedMatrixBound :
            matrixBitLength cleared.value.result ≤ workBits := by
          rw [clearedValue]
          exact (Nat.size_le_size
            (clear_result_height_le A hrow hdiv)).trans matrixBound
        let lower := firstUndivisibleLowerWithCost cleared.value.result
        have belowCost :
            traceBitCost below.charges ≤
              n * smithSearchDecisionBitOperationBound workBits :=
          firstUndivisibleBelowWithCost_cost_le_uniform
            A workBits matrixBound
        have clearCost :
            traceBitCost cleared.charges ≤
              clearExecutionBitOperationBound (n + 1) workBits :=
          (clearExecution_cost_le A hpivot hdiv).trans
            (clearExecutionBitOperationBound_mono_right
              (n + 1) matrixBound)
        have lowerCost :
            traceBitCost lower.charges ≤
              n * n * smithSearchDecisionBitOperationBound workBits :=
          firstUndivisibleLowerWithCost_cost_le_uniform
            cleared.value.result workBits clearedMatrixBound
        dsimp only
        split
        next _hbadLower =>
          simp only [StabilizationExecution.charges,
            CertificateExecution.appendCharges,
            CertificateExecution.prependCharges, traceBitCost_append]
          let level :=
            stabilizationExecutionLevelBitOperationBound (n + 1) workBits
          have measurePos : 0 < measure := by
            rw [← measureEq, Nat.size_pos]
            exact Int.natAbs_pos.mpr hpivot
          calc
            traceBitCost below.charges + traceBitCost cleared.charges +
                  traceBitCost lower.charges ≤
                n * smithSearchDecisionBitOperationBound workBits +
                  clearExecutionBitOperationBound (n + 1) workBits +
                  n * n * smithSearchDecisionBitOperationBound workBits :=
              Nat.add_le_add (Nat.add_le_add belowCost clearCost) lowerCost
            _ ≤ level := by
              unfold level stabilizationExecutionLevelBitOperationBound
              simp only [Nat.add_sub_cancel]
              omega
            _ = 1 * level := by simp
            _ ≤ measure * level :=
              Nat.mul_le_mul_right level measurePos
        next position hbadLower =>
          let injection := injectExecution cleared.value.result position.2
          let controlled := (cleared.prependCharges below.charges
            below.trace_wellFormed).appendCharges lower.charges
              lower.trace_wellFormed
          let accumulated := composeExecution controlled injection
          let accumulatedDet := result_det_ne_zero accumulated.value hdet
          let current := passExecution accumulated.value.result accumulatedDet
          have shape :
              current.value.result 0 0 ≠ 0 ∧
                current.value.result 0 0 =
                  _root_.normalize (current.value.result 0 0) ∧
                FirstRowCleared current.value.result := by
            rw [passExecution_value]
            exact pass_shape accumulated.value.result accumulatedDet
          let next := stabilizeFromExecution current.value.result
            (result_det_ne_zero current.value accumulatedDet)
            shape.1 shape.2.1 shape.2.2
          let tail := composeExecution current next.certificate
          have injectionValue :
              injection.value =
                injectLowerWitness cleared.value.result position.2 :=
            injectExecution_value cleared.value.result position.2
          have controlledValue : controlled.value = cleared.value := rfl
          have clearedRow : FirstRowCleared cleared.value.result := by
            rw [clearedValue]
            exact clearDivisibleFirstColumn_firstRowCleared A hrow
          have clearedColumn : FirstColumnCleared cleared.value.result := by
            rw [clearedValue]
            exact clearDivisibleFirstColumn_firstColumnCleared A hdiv
          have accumulatedValue :
              accumulated.value =
                compose controlled.value injection.value := by
            simp only [accumulated, composeExecution_value]
          have accumulatedResult :
              accumulated.value.result = injection.value.result := by
            rw [accumulatedValue]
            rfl
          have accumulatedPivot :
              accumulated.value.result 0 0 = A 0 0 := by
            rw [accumulatedResult, injectionValue]
            exact (injectLowerWitness_pivot
              cleared.value.result position.2 clearedRow).trans <| by
                rw [clearedValue]
                exact clearDivisibleFirstColumn_pivot A
          have target :
              accumulated.value.result position.1.succ 0 =
                cleared.value.result position.1.succ position.2.succ := by
            rw [accumulatedResult, injectionValue]
            exact injectLowerWitness_target
              cleared.value.result position.1 position.2 clearedColumn
          have pureBadLower :
              firstUndivisibleLower? cleared.value.result = some position :=
            (firstUndivisibleLowerWithCost_value
              cleared.value.result).symm.trans hbadLower
          have hnot :
              ¬ accumulated.value.result 0 0 ∣
                accumulated.value.result position.1.succ 0 := by
            rw [accumulatedPivot, target, clearedValue,
              ← clearDivisibleFirstColumn_pivot A]
            exact firstUndivisibleLower?_some_not_dvd
              (clearDivisibleFirstColumn A).result (by
                simpa [clearedValue] using pureBadLower)
          have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
            accumulated.value.result accumulatedDet
            (by simpa [accumulatedPivot] using hpivot)
            position.1.succ hnot
          have decreaseMeasure :
              (current.value.result 0 0).natAbs.size < measure := by
            simpa [current, measureEq, accumulatedPivot,
              passExecution_value] using decrease
          have injectionMatrixBound :
              matrixBitLength injection.value.result ≤ workBits + 1 := by
            rw [injectionValue]
            exact (injection_result_bitLength_le
              cleared.value.result position.2).trans <| by omega
          have accumulatedDetBits :
              integerBitLength accumulated.value.result.det =
                integerBitLength A.det :=
            congrArg Nat.size
              (certificate_result_det_natAbs accumulated.value)
          have currentMatrixBound :
              matrixBitLength current.value.result ≤ workBits := by
            simp only [current, passExecution_value]
            exact (pass_result_bitLength_le_determinant
              accumulated.value.result accumulatedDet).trans <| by
                rw [accumulatedDetBits]
                exact detBound
          have currentDetBits :
              integerBitLength current.value.result.det =
              integerBitLength A.det := by
            simp only [current, passExecution_value]
            exact (congrArg Nat.size
              (certificate_result_det_natAbs
                (pass accumulated.value.result accumulatedDet))).trans
                  accumulatedDetBits
          have nextCost := ih _ decreaseMeasure current.value.result
            (result_det_ne_zero current.value accumulatedDet)
            shape.1 shape.2.1 shape.2.2 currentMatrixBound
            (currentDetBits ▸ detBound) rfl
          have injectionCost :
              traceBitCost injection.charges ≤
                injectExecutionBitOperationBound (n + 1) workBits :=
            (injectExecution_cost_le cleared.value.result position.2).trans
              (injectExecutionBitOperationBound_mono_right
                (n + 1) clearedMatrixBound)
          have passCost :
              traceBitCost current.charges ≤
                passExecutionBitOperationBound n (workBits + 1) workBits :=
            (passExecution_cost_le
              accumulated.value.result accumulatedDet).trans <|
                passExecutionBitOperationBound_mono n
                  (by simpa [accumulatedResult] using injectionMatrixBound)
                  (by rw [accumulatedDetBits]; exact detBound)
          have clearTransform :
              certificateTransformBitLength cleared.value ≤
                stabilizationTransformWorkBound (n + 1) workBits := by
            rw [clearedValue]
            exact (clear_transformBitLength_le_uniform A matrixBound).trans
              (stabilizationFactor_le_transformWorkBound n workBits)
          have injectionTransform :
              certificateTransformBitLength injection.value ≤
                stabilizationTransformWorkBound (n + 1) workBits := by
            rw [injectionValue]
            exact (injection_transformBitLength_le_uniform
              cleared.value.result position.2).trans
                (stabilizationFactor_le_transformWorkBound n workBits)
          have controlledTransform :
              certificateTransformBitLength controlled.value ≤
                stabilizationTransformWorkBound (n + 1) workBits := by
            rw [controlledValue]
            exact clearTransform
          have accumulatedTransform :
              certificateTransformBitLength accumulated.value ≤
                stabilizationExecutionTransformBitLengthBound
                  (n + 1) workBits := by
            rw [accumulatedValue]
            apply (compose_transformBitLength_le
              controlled.value injection.value).trans
            unfold stabilizationExecutionTransformBitLengthBound
            calc
              Nat.size (n + 1) +
                    certificateTransformBitLength controlled.value +
                    certificateTransformBitLength injection.value ≤
                  Nat.size (n + 1) +
                    stabilizationTransformWorkBound (n + 1) workBits +
                    stabilizationTransformWorkBound (n + 1) workBits :=
                Nat.add_le_add
                  (Nat.add_le_add_left controlledTransform _)
                  injectionTransform
              _ = Nat.size (n + 1) +
                    2 * stabilizationTransformWorkBound
                      (n + 1) workBits := by ring
          have currentTransform :
              certificateTransformBitLength current.value ≤
                stabilizationTransformWorkBound (n + 1) workBits := by
            simp only [current, passExecution_value]
            exact (pass_transformBitLength_le_uniform
              accumulated.value.result accumulatedDet
              (by simpa [accumulatedResult] using injectionMatrixBound)
              (by rw [accumulatedDetBits]; exact detBound)).trans
                (stabilizationFactor_le_transformWorkBound n workBits)
          have currentPivotBound :
              (current.value.result 0 0).natAbs.size ≤ workBits :=
            (entry_bitLength_le_matrixBitLength
              current.value.result 0 0).trans currentMatrixBound
          have nextTransform :
              certificateTransformBitLength next.certificate.value ≤
                stabilizationTransformWorkBound (n + 1) workBits := by
            simp only [next, stabilizeFromExecution_replay]
            exact (stabilizeFrom_transformBitLength_le current.value.result
              (result_det_ne_zero current.value accumulatedDet)
              shape.1 shape.2.1 shape.2.2 currentMatrixBound
              (currentDetBits ▸ detBound)).trans <|
                stabilizationContinuation_le_transformWorkBound
                  n workBits _ currentPivotBound
          have tailTransform :
              certificateTransformBitLength tail.value ≤
                stabilizationExecutionTransformBitLengthBound
                  (n + 1) workBits := by
            simp only [tail, composeExecution_value]
            exact (compose_transformBitLength_le
              current.value next.certificate.value).trans <| by
                unfold stabilizationExecutionTransformBitLengthBound
                omega
          have firstCompositionCost :
              certificateCompositionBitOperationCost
                  cleared.value injection.value ≤
                stabilizationExecutionCompositionBitOperationBound
                  (n + 1) workBits := by
            apply certificateCompositionBitOperationCost_le_execution
            · exact clearTransform.trans
                (stabilizationTransformWorkBound_le_execution _ _)
            · exact injectionTransform.trans
                (stabilizationTransformWorkBound_le_execution _ _)
          have secondCompositionCost :
              certificateCompositionBitOperationCost
                  current.value next.certificate.value ≤
                stabilizationExecutionCompositionBitOperationBound
                  (n + 1) workBits :=
            certificateCompositionBitOperationCost_le_execution
              current.value next.certificate.value
              (currentTransform.trans
                (stabilizationTransformWorkBound_le_execution _ _))
              (nextTransform.trans
                (stabilizationTransformWorkBound_le_execution _ _))
          have thirdCompositionCost :
              certificateCompositionBitOperationCost
                  accumulated.value tail.value ≤
                stabilizationExecutionCompositionBitOperationBound
                  (n + 1) workBits :=
            certificateCompositionBitOperationCost_le_execution
              accumulated.value tail.value
              accumulatedTransform tailTransform
          change
            traceBitCost (composeExecution accumulated tail).charges ≤
              measure *
                stabilizationExecutionLevelBitOperationBound
                  (n + 1) workBits
          rw [composeExecution_cost_eq]
          have accumulatedCost := composeExecution_cost_eq
            controlled injection
          have tailCost := composeExecution_cost_eq
            current next.certificate
          rw [show traceBitCost accumulated.charges =
              traceBitCost controlled.charges +
                traceBitCost injection.charges +
                certificateCompositionBitOperationCost
                  controlled.value injection.value by
                simpa only [accumulated] using accumulatedCost,
            show traceBitCost tail.charges =
              traceBitCost current.charges +
                traceBitCost next.charges +
                certificateCompositionBitOperationCost
                  current.value next.certificate.value by
                simpa only [tail, StabilizationExecution.charges]
                  using tailCost]
          simp only [controlled, CertificateExecution.appendCharges,
            CertificateExecution.prependCharges, traceBitCost_append]
          let level :=
            stabilizationExecutionLevelBitOperationBound (n + 1) workBits
          have totalCost :
            traceBitCost below.charges + traceBitCost cleared.charges +
                  traceBitCost lower.charges + traceBitCost injection.charges +
                  certificateCompositionBitOperationCost
                    cleared.value injection.value +
                  traceBitCost current.charges +
                  traceBitCost next.charges +
                  certificateCompositionBitOperationCost
                    current.value next.certificate.value +
                  certificateCompositionBitOperationCost
                    accumulated.value tail.value ≤
              measure * level := by
            calc
              traceBitCost below.charges + traceBitCost cleared.charges +
                    traceBitCost lower.charges +
                      traceBitCost injection.charges +
                    certificateCompositionBitOperationCost
                      cleared.value injection.value +
                    traceBitCost current.charges +
                    traceBitCost next.charges +
                    certificateCompositionBitOperationCost
                      current.value next.certificate.value +
                    certificateCompositionBitOperationCost
                      accumulated.value tail.value ≤
                  n * smithSearchDecisionBitOperationBound workBits +
                    clearExecutionBitOperationBound (n + 1) workBits +
                    n * n * smithSearchDecisionBitOperationBound workBits +
                    injectExecutionBitOperationBound (n + 1) workBits +
                    stabilizationExecutionCompositionBitOperationBound
                      (n + 1) workBits +
                    passExecutionBitOperationBound n (workBits + 1) workBits +
                    (current.value.result 0 0).natAbs.size * level +
                    stabilizationExecutionCompositionBitOperationBound
                      (n + 1) workBits +
                    stabilizationExecutionCompositionBitOperationBound
                      (n + 1) workBits :=
                Nat.add_le_add
                  (Nat.add_le_add
                    (Nat.add_le_add
                      (Nat.add_le_add
                        (Nat.add_le_add
                          (Nat.add_le_add
                            (Nat.add_le_add
                              (Nat.add_le_add belowCost clearCost) lowerCost)
                            injectionCost)
                          firstCompositionCost)
                        passCost)
                      nextCost)
                    secondCompositionCost)
                  thirdCompositionCost
              _ ≤ level +
                  (current.value.result 0 0).natAbs.size * level := by
                unfold level stabilizationExecutionLevelBitOperationBound
                simp only [Nat.add_sub_cancel]
                omega
              _ = ((current.value.result 0 0).natAbs.size + 1) * level := by
                ring
              _ ≤ measure * level :=
                Nat.mul_le_mul_right level
                  (Nat.succ_le_iff.mpr decreaseMeasure)
          simpa only [level, Nat.add_assoc] using totalCost

public theorem stabilizeExecution_cost_le {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0)
    (matrixBound : matrixBitLength A ≤ workBits)
    (detBound : integerBitLength A.det ≤ workBits) :
    traceBitCost (stabilizeExecution A hdet).charges ≤
      stabilizationExecutionBitOperationBound (n + 1) workBits := by
  let initial := passExecution A hdet
  have shape :
      initial.value.result 0 0 ≠ 0 ∧
        initial.value.result 0 0 =
          _root_.normalize (initial.value.result 0 0) ∧
        FirstRowCleared initial.value.result := by
    rw [passExecution_value]
    exact pass_shape A hdet
  let rest := stabilizeFromExecution initial.value.result
    (result_det_ne_zero initial.value hdet)
    shape.1 shape.2.1 shape.2.2
  have initialMatrixBound :
      matrixBitLength initial.value.result ≤ workBits := by
    simp only [initial, passExecution_value]
    exact (pass_result_bitLength_le_determinant A hdet).trans detBound
  have initialDetBits :
      integerBitLength initial.value.result.det = integerBitLength A.det := by
    simp only [initial, passExecution_value]
    exact congrArg Nat.size
      (certificate_result_det_natAbs (pass A hdet))
  have initialCost :
      traceBitCost initial.charges ≤
        passExecutionBitOperationBound n (workBits + 1) workBits :=
    (passExecution_cost_le A hdet).trans <|
      passExecutionBitOperationBound_mono n
        (matrixBound.trans <| by omega) detBound
  have restCost :
      traceBitCost rest.charges ≤
        (initial.value.result 0 0).natAbs.size *
          stabilizationExecutionLevelBitOperationBound
            (n + 1) workBits :=
    stabilizeFromExecution_cost_le initial.value.result
      (result_det_ne_zero initial.value hdet)
      shape.1 shape.2.1 shape.2.2 initialMatrixBound
      (initialDetBits ▸ detBound)
  have initialTransform :
      certificateTransformBitLength initial.value ≤
        stabilizationTransformWorkBound (n + 1) workBits := by
    simp only [initial, passExecution_value]
    exact (pass_transformBitLength_le_uniform A hdet
      (matrixBound.trans <| by omega) detBound).trans
        (stabilizationFactor_le_transformWorkBound n workBits)
  have initialPivotBound :
      (initial.value.result 0 0).natAbs.size ≤ workBits :=
    (entry_bitLength_le_matrixBitLength initial.value.result 0 0).trans
      initialMatrixBound
  have restTransform :
      certificateTransformBitLength rest.certificate.value ≤
        stabilizationTransformWorkBound (n + 1) workBits := by
    simp only [rest, stabilizeFromExecution_replay]
    exact (stabilizeFrom_transformBitLength_le initial.value.result
      (result_det_ne_zero initial.value hdet)
      shape.1 shape.2.1 shape.2.2 initialMatrixBound
      (initialDetBits ▸ detBound)).trans <|
        stabilizationContinuation_le_transformWorkBound
          n workBits _ initialPivotBound
  have compositionCost :
      certificateCompositionBitOperationCost
          initial.value rest.certificate.value ≤
        stabilizationExecutionCompositionBitOperationBound
          (n + 1) workBits := by
    apply certificateCompositionBitOperationCost_le_execution
    · exact initialTransform.trans
        (stabilizationTransformWorkBound_le_execution _ _)
    · exact restTransform.trans
        (stabilizationTransformWorkBound_le_execution _ _)
  change
    traceBitCost (composeExecution initial rest.certificate).charges ≤ _
  rw [composeExecution_cost_eq]
  let level :=
    stabilizationExecutionLevelBitOperationBound (n + 1) workBits
  unfold stabilizationExecutionBitOperationBound
  calc
    traceBitCost initial.charges + traceBitCost rest.charges +
          certificateCompositionBitOperationCost
            initial.value rest.certificate.value ≤
        passExecutionBitOperationBound n (workBits + 1) workBits +
          (initial.value.result 0 0).natAbs.size * level +
          stabilizationExecutionCompositionBitOperationBound
            (n + 1) workBits :=
      Nat.add_le_add (Nat.add_le_add initialCost restCost) compositionCost
    _ ≤ level + workBits * level := by
      have pivotProduct := Nat.mul_le_mul_right level initialPivotBound
      have fixedCost :
          passExecutionBitOperationBound n (workBits + 1) workBits +
              stabilizationExecutionCompositionBitOperationBound
                (n + 1) workBits ≤
            level := by
        unfold level stabilizationExecutionLevelBitOperationBound
        simp only [Nat.add_sub_cancel]
        omega
      omega
    _ = (workBits + 1) * level := by ring

end NormalForms.Research.KannanBachem
