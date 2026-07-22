/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Research.KannanBachem
import all NormalForms.Research.KannanBachem.Hermite.BoundedXGCD
meta import all NormalForms.Research.KannanBachem
meta import all NormalForms.Matrix.Hermite.Algorithm

set_option linter.privateModule false
set_option linter.hashCommand false

/-! Executable and theorem-level regressions for the first HNF research seam. -/

namespace NormalForms.Tests.Research.KannanBachem

open scoped Matrix
open NormalForms.Matrix.Hermite
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

private def primitiveTrace : RowTrace Int 2 :=
  [ ReversibleRowStep.swap 0 1
  , ReversibleRowStep.add 0 1 3 (by decide)
  , ReversibleRowStep.unitScale 0 (-1 : Intˣ)
  , ReversibleRowStep.bezoutPair 6 15 ]

#guard primitiveTrace.IsPrimitive
#guard primitiveTrace.operationCount =
  { swaps := 1, additions := 1, unitScales := 1, bezoutPairs := 1 }

private def liftedTrace : RowTrace Int 3 :=
  RowTrace.leadingLift primitiveTrace

#guard liftedTrace.IsPrimitive
#guard liftedTrace.operationCount = primitiveTrace.operationCount

example :
    primitiveTrace.inverseAccumulator * primitiveTrace.accumulator = 1 :=
  RowTrace.inverse_mul_accumulator primitiveTrace

example :
    primitiveTrace.accumulator * primitiveTrace.inverseAccumulator = 1 :=
  RowTrace.accumulator_mul_inverse primitiveTrace

example :
    liftedTrace.accumulator = leadingLiftMatrix primitiveTrace.accumulator :=
  RowTrace.accumulator_leadingLift primitiveTrace

private def input : Matrix (Fin 2) (Fin 3) Int :=
  !![6, 15, 9;
     4, 10, 6]

private def expected : Matrix (Fin 2) (Fin 3) Int :=
  !![2, 5, 3;
     0, 0, 0]

#guard (semanticReference input).H = expected
#guard ¬ (semanticReferenceTrace input).steps.IsPrimitive
#guard (primitiveHermiteNormalForm input).H = expected
#guard (primitiveHermiteTrace input).steps.IsPrimitive
#guard (primitiveHermiteTrace input).steps.length = 5
#guard (primitiveHermiteTrace input).steps.operationCount =
  { swaps := 2, additions := 0, unitScales := 2, bezoutPairs := 1 }
#guard (primitiveHermiteTrace input).steps.operationCount.certifiedBlocks = 0
#guard (primitiveHermiteTrace input).steps.replay input =
  (primitiveHermiteNormalForm input).H
#guard primitiveHermiteRingOperations input =
  { additions := 6, multiplications := 18, xgcdCalls := 1, normalizations := 2 }
#guard (primitiveHermiteRingOperations input).total = 27
#guard hermiteRingOperationBound 2 3 = 696

example :
    (semanticReference input).U * input = (semanticReference input).H :=
  semanticReference_equation input

example :
    (semanticReference input).U_cert.inverse * (semanticReference input).H = input :=
  semanticReference_inverse_equation input

example :
    (semanticReferenceTrace input).steps.replay input = (semanticReference input).H :=
  ExecutionTrace.replay_eq_result (semanticReferenceTrace input)

example :
    (primitiveHermiteNormalForm input).U * input =
      (primitiveHermiteNormalForm input).H :=
  primitiveHermite_equation input

example :
    (primitiveHermiteNormalForm input).U_cert.inverse *
        (primitiveHermiteNormalForm input).H = input :=
  primitiveHermite_inverse_equation input

example :
    IsHermiteNormalFormFin (primitiveHermiteNormalForm input).H :=
  primitiveHermite_isHermite input

example :
    (primitiveHermiteNormalForm input).H = (semanticReference input).H :=
  primitiveHermite_eq_reference input

example :
    (primitiveHermiteTrace input).steps.length ≤ 4 * 2 * 3 :=
  primitiveHermiteTrace_length_le input

example :
    (primitiveHermiteRingOperations input).total ≤
      hermiteRingOperationBound 2 3 :=
  primitiveHermiteRingOperations_total_le input

private def emptyRows : Matrix (Fin 0) (Fin 3) Int := 0
private def emptyCols : Matrix (Fin 3) (Fin 0) Int := 0

#guard (primitiveHermiteTrace emptyRows).steps = []
#guard (primitiveHermiteTrace emptyCols).steps = []
#guard (primitiveHermiteNormalForm emptyRows).H = emptyRows
#guard (primitiveHermiteNormalForm emptyCols).H = emptyCols

private def rectangularRankDeficient : Matrix (Fin 3) (Fin 2) Int :=
  !![4, 6;
     2, 3;
     0, 0]

#guard (primitiveHermiteTrace rectangularRankDeficient).steps.IsPrimitive
#guard (primitiveHermiteTrace rectangularRankDeficient).steps.operationCount.certifiedBlocks = 0

example :
    (primitiveHermiteNormalForm rectangularRankDeficient).U_cert.inverse *
        (primitiveHermiteNormalForm rectangularRankDeficient).H =
      rectangularRankDeficient :=
  primitiveHermite_inverse_equation rectangularRankDeficient

/-! The distinct principal-minor schedule is exercised independently. -/

private def principalInput : Matrix (Fin 3) (Fin 3) Int :=
  !![2, 3, 5;
     4, 7, 11;
     6, 13, 17]

private def principalExpected : Matrix (Fin 3) (Fin 3) Int :=
  !![2, 0, 0;
     0, 1, 1;
     0, 0, 2]

#guard principalRingOperationBound 3 = 783
#guard matrixHeight principalInput = 17
#guard matrixBitLength principalInput = 5
#guard integerBitLength (-17) = 5
#guard determinantBitLengthBound 3 (matrixBitLength principalInput) = 23
#guard Principal.boundedIntXGCDCoefficientHeight 240 46 = 58081
#guard Principal.boundedIntXGCDBitOperationCost 240 46 ≤
  Principal.boundedIntXGCDBitOperationBound 240 46
#guard Principal.stageMinorHeightBound 2 (matrixHeight principalInput) = 29478

/- Evaluate the costly principal run once, then freeze every exact observation. -/
#guard
  let run := principalRun principalInput
  let operations := RingOperationCount.ofTrace 3 run.steps
  let matrixMaximum := run.steps.intermediateMatrixHeight principalInput
  let operandMaximum := arithmeticEventListHeight run.arithmeticEvents
  run.matrix = principalExpected ∧
    run.steps.IsPrimitive ∧
    run.steps.operationCount =
      { swaps := 0, additions := 4, unitScales := 3, bezoutPairs := 3 } ∧
    operations =
      { additions := 30, multiplications := 57, xgcdCalls := 3,
        normalizations := 3 } ∧
    operations.total = 93 ∧
    matrixHeight principalInput ≤ matrixMaximum ∧
    matrixHeight run.matrix ≤ matrixMaximum ∧
    matrixMaximum = 17 ∧
    Nat.size matrixMaximum = 5 ∧
    matrixHeight run.matrix ≤ principalInput.det.natAbs ∧
    matrixBitLength run.matrix ≤
      determinantBitLengthBound 3 (matrixBitLength principalInput) ∧
    (run.steps.intermediates principalInput).length = run.steps.length + 1 ∧
    run.events =
      [ .normalize 0
      , .gcdEliminate 0 1
      , .normalize 1
      , .reduceAbove 0 1
      , .gcdEliminate 0 2
      , .gcdEliminate 1 2
      , .reduceAbove 0 1
      , .normalize 2
      , .reduceAbove 0 2
      , .reduceAbove 1 2 ] ∧
    run.arithmeticEvents =
      [ .normalize 0 2
      , .xgcd 0 1 2 4
      , .normalize 1 1
      , .divMod 0 1 3 1
      , .xgcd 0 2 2 6
      , .xgcd 1 2 1 13
      , .divMod 0 1 0 1
      , .normalize 2 (-2)
      , .divMod 0 2 2 2
      , .divMod 1 2 1 2 ] ∧
    operandMaximum = 13 ∧
    Nat.size operandMaximum = 4 ∧
    run.steps.intermediateMultiplierHeight = 21 ∧
    Nat.size run.steps.intermediateMultiplierHeight = 5 ∧
    run.steps.intermediateInverseMultiplierHeight = 13 ∧
    Nat.size run.steps.intermediateInverseMultiplierHeight = 4 ∧
    operandMaximum ≤ matrixMaximum ∧
    run.arithmeticEvents.length = run.steps.length

#guard (checkPrincipalRun principalInput).isOk

example : principalInput.det ≠ 0 := by decide

private theorem principalInputReady : Principal.PrincipalReady principalInput := by
  intro k hk
  interval_cases k <;> decide_cbv

example :
    principalIntermediateMatrixBitLength principalInput ≤
      Principal.principalIntermediateBitLengthBound 3
        (matrixBitLength principalInput) :=
  principalIntermediateMatrixBitLength_le_of_ready principalInput
    principalInputReady

example :
    principalIntermediateMatrixBitLength principalInput ≤
      Principal.principalPolynomialBitLengthBound 3
        (matrixBitLength principalInput) :=
  principalIntermediateMatrixBitLength_le_polynomial_of_ready principalInput
    principalInputReady

example :
    principalArithmeticOperandBitLength principalInput ≤
      Principal.principalPolynomialBitLengthBound 3
        (matrixBitLength principalInput) :=
  principalArithmeticOperandBitLength_le_polynomial_of_ready principalInput
    principalInputReady

example :
    principalIntermediateMultiplierBitLength principalInput ≤
      Principal.principalMultiplierPrefixPolynomialBitLengthBound 3
        (matrixBitLength principalInput) :=
  principalIntermediateMultiplierBitLength_le_polynomial_of_ready
    principalInput principalInputReady

example :
    principalIntermediateInverseBitLength principalInput ≤
      Principal.principalInversePrefixPolynomialBitLengthBound 3
        (matrixBitLength principalInput) :=
  principalIntermediateInverseBitLength_le_polynomial_of_ready
    principalInput principalInputReady

example :
    240 * (Principal.boundedIntXGCD 240 46).leftCoeff +
        46 * (Principal.boundedIntXGCD 240 46).rightCoeff =
      (Principal.boundedIntXGCD 240 46).gcd :=
  Principal.boundedIntXGCD_bezout 240 46

example :
    Principal.boundedIntXGCDBitOperationCost 240 46 ≤
      Principal.boundedIntXGCDBitOperationBound 240 46 :=
  Principal.boundedIntXGCDBitOperationCost_le 240 46

example :
    principalHNFBitOperationCost principalInput ≤
      principalHNFBitOperationBound 3 (matrixBitLength principalInput) :=
  principalHNFBitOperationCost_le_of_ready principalInput principalInputReady

example : IsHermiteNormalFormFin (principalRun principalInput).matrix :=
  principalRun_isHermite_of_det_ne_zero principalInput (by decide)

example : (principalRun principalInput).steps.length ≤ 3 ^ 3 :=
  principalRun_steps_length_le principalInput

example :
    (principalRingOperations principalInput).total ≤
      principalRingOperationBound 3 :=
  principalRingOperations_total_le principalInput

example :
    (principalHermiteNormalForm principalInput (by decide)).H =
      (semanticReference principalInput).H :=
  principalHermiteNormalForm_eq_reference principalInput (by decide)

private def principalEmpty : Matrix (Fin 0) (Fin 0) Int := 0

#guard (checkPrincipalRun principalEmpty).isOk

example : IsHermiteNormalFormFin (principalRun principalEmpty).matrix :=
  principalRun_isHermite_of_det_ne_zero principalEmpty (by decide)

/-- Total correctness does not require a nonzero initial leading entry. -/
private def principalZeroLeading : Matrix (Fin 2) (Fin 2) Int :=
  !![0, 1;
     1, 0]

#guard (checkPrincipalRun principalZeroLeading).isOk

private def principalZeroLeadingPrepared :
    Principal.Preparation principalZeroLeading :=
  Principal.prepare principalZeroLeading (by decide)

#guard (Principal.lastColumnScan principalZeroLeading).value = some 0
#guard principalZeroLeadingPrepared.rowPermutation 0 = 1
#guard principalZeroLeadingPrepared.rowPermutation 1 = 0
#guard principalZeroLeadingPrepared.matrix =
  !![1, 0;
     0, 1]

#guard
  let result := Principal.preparedPrincipalHermiteNormalForm
    principalZeroLeading (by decide)
  result.H = !![1, 0; 0, 1] ∧
    result.U * principalZeroLeading = result.H ∧
    result.U_cert.inverse * result.U = 1 ∧
    result.U * result.U_cert.inverse = 1

example : IsHermiteNormalFormFin (principalRun principalZeroLeading).matrix :=
  principalRun_isHermite_of_det_ne_zero principalZeroLeading (by decide)

example : Principal.PrincipalReady principalZeroLeadingPrepared.matrix :=
  principalZeroLeadingPrepared.ready

example :
    principalZeroLeadingPrepared.transform * principalZeroLeading =
      principalZeroLeadingPrepared.matrix :=
  principalZeroLeadingPrepared.equation

example :
    (Principal.preparedPrincipalHermiteNormalForm
        principalZeroLeading (by decide)).H =
      (semanticReference principalZeroLeading).H :=
  Principal.preparedPrincipalHermiteNormalForm_eq_reference
    principalZeroLeading (by decide)

example :
    principalHNFBitOperationCost principalZeroLeadingPrepared.matrix ≤
      principalHNFBitOperationBound 2
        (matrixBitLength principalZeroLeading) :=
  preparedPrincipalKernelBitOperationCost_le
    principalZeroLeading (by decide)

example :
    (Principal.lastColumnScan principalZeroLeading).cost ≤
      2 *
        (DivisionFreeDeterminant.determinantBitOperationBound 1
          (matrixBitLength principalZeroLeading) + 1) :=
  Principal.lastColumnScan_cost_le principalZeroLeading

example :
    preparedPrincipalHNFBitOperationCost principalZeroLeading (by decide) ≤
      preparedPrincipalHNFBitOperationBound 2
        (matrixBitLength principalZeroLeading) :=
  preparedPrincipalHNFBitOperationCost_le principalZeroLeading (by decide)

private def birdInputTwo : Matrix (Fin 2) (Fin 2) Int :=
  !![1, 2;
     3, 4]

private def birdInputThree : Matrix (Fin 3) (Fin 3) Int :=
  !![1, 2, 3;
     0, 4, 5;
     1, 0, 6]

#guard
  (DivisionFreeDeterminant.evaluateWithCost birdInputTwo).value.value = -2

#guard
  (DivisionFreeDeterminant.evaluateWithCost birdInputThree).value.value = 22

#guard
  DivisionFreeDeterminant.matrixBirdDet birdInputTwo = birdInputTwo.det

#guard
  DivisionFreeDeterminant.matrixBirdDet birdInputThree = birdInputThree.det

#guard
  (DivisionFreeDeterminant.evaluateWithCost birdInputThree).cost ≤
    DivisionFreeDeterminant.determinantBitOperationBound 3
      (matrixBitLength birdInputThree)

example :
    (DivisionFreeDeterminant.evaluateWithCost birdInputThree).value.value =
      DivisionFreeDeterminant.matrixBirdDet birdInputThree :=
  DivisionFreeDeterminant.evaluateWithCost_value birdInputThree

example :
    DivisionFreeDeterminant.matrixBirdDet birdInputThree =
      birdInputThree.det :=
  DivisionFreeDeterminant.matrixBirdDet_eq_det birdInputThree

example :
    (DivisionFreeDeterminant.evaluateWithCost birdInputThree).value.value =
      birdInputThree.det :=
  DivisionFreeDeterminant.evaluateWithCost_value_eq_det birdInputThree

example :
    (DivisionFreeDeterminant.evaluateWithCost birdInputThree).cost ≤
      DivisionFreeDeterminant.determinantBitOperationBound 3
        (matrixBitLength birdInputThree) :=
  DivisionFreeDeterminant.evaluateWithCost_cost_le birdInputThree

example :
    (principalRun principalInput).steps.replay principalInput =
      (principalRun principalInput).matrix :=
  principalRun_replay principalInput

example :
    (principalRun principalInput).steps.inverseAccumulator *
        (principalRun principalInput).matrix = principalInput :=
  principalRun_inverse_equation principalInput

example :
    (principalRun principalInput).events.Forall (PrincipalEvent.Valid 3) :=
  (principalRun principalInput).validEvents

example :
    (principalRun principalInput).arithmeticEvents.Forall
      (PrincipalArithmeticEvent.Valid 3) :=
  (principalRun principalInput).validArithmeticEvents

example {result : HNFResultFin principalInput}
    (success : checkPrincipalRun principalInput = .ok result) :
    result.H = (principalRun principalInput).matrix :=
  (checkPrincipalRun_result success).1

example {result : HNFResultFin principalInput}
    (success : checkPrincipalRun principalInput = .ok result) :
    result.H = (semanticReference principalInput).H :=
  checkPrincipalRun_eq_reference success

example {result : HNFResultFin principalInput}
    (success : checkPrincipalRun principalInput = .ok result) :
    (checkedPrincipalTrace success).steps.IsPrimitive :=
  checkedPrincipalTrace_isPrimitive success

/-! The total and fuelled Smith paths execute both pivot-descent branches. -/

private def smithRepeatInput : Matrix (Fin 2) (Fin 2) Int :=
  !![2, 1;
     0, 2]

private def smithRepeatExpected : Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 4]

private def smithInjectionInput : Matrix (Fin 2) (Fin 2) Int :=
  !![2, 0;
     0, 3]

private def smithInjectionExpected : Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 6]

#guard
  match stabilize? 5 smithRepeatInput (by decide) with
  | none => false
  | some result =>
      result.certificate.result = smithRepeatExpected ∧
        result.passes = 2 ∧ result.injections = 0

#guard
  match stabilize? 5 smithInjectionInput (by decide) with
  | none => false
  | some result =>
      result.certificate.result = smithInjectionExpected ∧
        result.passes = 2 ∧ result.injections = 1

#guard
  match smith? 5 smithRepeatInput (by decide) with
  | none => false
  | some result =>
      result.S = smithRepeatExpected ∧
        result.U * smithRepeatInput * result.V = result.S ∧
        result.U_cert.inverse * result.S * result.V_cert.inverse =
          smithRepeatInput

#guard
  match smith? 5 smithInjectionInput (by decide) with
  | none => false
  | some result => result.S = smithInjectionExpected

#guard
  let result := stabilize smithRepeatInput (by decide)
  result.certificate.result = smithRepeatExpected ∧
    result.passes = 1 ∧ result.injections = 0

#guard
  let result := stabilize smithInjectionInput (by decide)
  result.certificate.result = smithInjectionExpected ∧
    result.passes = 2 ∧ result.injections = 1

#guard (smith smithRepeatInput (by decide)).S = smithRepeatExpected
#guard (smith smithInjectionInput (by decide)).S = smithInjectionExpected

#guard stabilizeOperationCount smithRepeatInput (by decide) =
  { additions := 12, multiplications := 26, xgcdCalls := 2,
    normalizations := 3, divModCalls := 1 }

#guard smithOperationCount smithRepeatInput (by decide) =
  { additions := 12, multiplications := 28, xgcdCalls := 2,
    normalizations := 5, divModCalls := 1 }

#guard stabilizeOperationCount smithInjectionInput (by decide) =
  { additions := 26, multiplications := 54, xgcdCalls := 4,
    normalizations := 6, divModCalls := 2 }

#guard smithOperationCount smithInjectionInput (by decide) =
  { additions := 26, multiplications := 56, xgcdCalls := 4,
    normalizations := 8, divModCalls := 2 }

/- Freeze actual bit-operation charges for the repeated-pass and injection paths. -/
#guard
  boundedColumnBitOperationCost smithRepeatInput = 2521951 ∧
    passBitOperationCost smithRepeatInput (by decide) = 1130155896875 ∧
    stabilizeBitOperationCost smithRepeatInput (by decide) = 1130155898469 ∧
    smithBitOperationCost smithRepeatInput (by decide) = 1130326542472

#guard
  boundedColumnBitOperationCost smithInjectionInput = 2521951 ∧
    passBitOperationCost smithInjectionInput (by decide) = 1130155896826 ∧
    stabilizeBitOperationCost smithInjectionInput (by decide) = 3012262037638 ∧
    smithBitOperationCost smithInjectionInput (by decide) = 3012432681653

example :
    (stabilize smithInjectionInput (by decide)).passes ≤
      ((pass smithInjectionInput (by decide)).result 0 0).natAbs.size + 1 :=
  stabilize_passes_le smithInjectionInput (by decide)

example :
    (stabilize smithInjectionInput (by decide)).passes ≤
      matrixBitLength smithInjectionInput + 1 :=
  stabilize_passes_le_inputBitLength smithInjectionInput (by decide)

example :
    (smithOperationCount smithInjectionInput (by decide)).total ≤
      smithPolynomialRingOperationBound 2
        (matrixBitLength smithInjectionInput) :=
  smithOperationCount_total_le_polynomial smithInjectionInput (by decide)

example :
    stabilizeBitOperationCost smithInjectionInput (by decide) ≤
      stabilizationPolynomialBitOperationBound 2
        (matrixBitLength smithInjectionInput) :=
  stabilizeBitOperationCost_le_polynomial smithInjectionInput (by decide)

example :
    smithBitOperationCost smithInjectionInput (by decide) ≤
      smithPolynomialBitOperationBound 2
        (matrixBitLength smithInjectionInput) :=
  smithBitOperationCost_le_polynomial smithInjectionInput (by decide)

example :
    smithTransformBitLength (smith smithInjectionInput (by decide)) ≤
      smithCertificatePolynomialBitLengthBound 2
        (matrixBitLength smithInjectionInput) :=
  smith_transformBitLength_le_polynomial smithInjectionInput (by decide)

example :
    matrixBitLength (smith smithInjectionInput (by decide)).S ≤
      determinantBitLengthBound 2 (matrixBitLength smithInjectionInput) :=
  smith_result_bitLength_le_polynomial smithInjectionInput (by decide)

example :
    let profile := smithCoefficientProfile
      (smith smithInjectionInput (by decide))
    profile.resultBitLength ≤
        determinantBitLengthBound 2 (matrixBitLength smithInjectionInput) ∧
      profile.leftBitLength ≤
        smithCertificatePolynomialBitLengthBound 2
          (matrixBitLength smithInjectionInput) ∧
      profile.leftInverseBitLength ≤
        smithCertificatePolynomialBitLengthBound 2
          (matrixBitLength smithInjectionInput) ∧
      profile.rightBitLength ≤
        smithCertificatePolynomialBitLengthBound 2
          (matrixBitLength smithInjectionInput) ∧
      profile.rightInverseBitLength ≤
        smithCertificatePolynomialBitLengthBound 2
          (matrixBitLength smithInjectionInput) :=
  smith_coefficientProfile_le_polynomial smithInjectionInput (by decide)

example :
    (smith smithInjectionInput (by decide)).U * smithInjectionInput *
          (smith smithInjectionInput (by decide)).V =
        (smith smithInjectionInput (by decide)).S ∧
      (smith smithInjectionInput (by decide)).U_cert.inverse *
          (smith smithInjectionInput (by decide)).S *
          (smith smithInjectionInput (by decide)).V_cert.inverse =
        smithInjectionInput ∧
      NormalForms.Matrix.Smith.IsSmithNormalFormFin
        (smith smithInjectionInput (by decide)).S :=
  smith_sound smithInjectionInput (by decide)

example :
    (smith smithInjectionInput (by decide)).S =
      (NormalForms.Matrix.Smith.smithNormalFormFin smithInjectionInput).S :=
  smith_eq_reference smithInjectionInput (by decide)

example {result : NormalForms.Matrix.Smith.SNFResultFin smithInjectionInput}
    (success : smith? 5 smithInjectionInput (by decide) = some result) :
    result.U * smithInjectionInput * result.V = result.S ∧
      result.U_cert.inverse * result.S * result.V_cert.inverse =
        smithInjectionInput ∧
      NormalForms.Matrix.Smith.IsSmithNormalFormFin result.S :=
  smith?_sound smithInjectionInput (by decide) success

example {result : NormalForms.Matrix.Smith.SNFResultFin smithInjectionInput}
    (success : smith? 5 smithInjectionInput (by decide) = some result) :
    result.S =
      (NormalForms.Matrix.Smith.smithNormalFormFin smithInjectionInput).S :=
  smith?_eq_reference smithInjectionInput (by decide) success

end NormalForms.Tests.Research.KannanBachem
