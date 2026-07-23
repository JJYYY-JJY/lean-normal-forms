/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Polynomial
public import NormalForms.Research.KannanBachem.Execution.SmithComplexity
public import NormalForms.Research.KannanBachem.Encoding

/-! # Fixed-Polynomial Envelopes for the Instrumented Execution -/

public section

namespace NormalForms.Research.KannanBachem

open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminant
open NormalForms.Research.KannanBachem.Smith

@[expose] public def smithOutputPolynomialEntryBitBound
    (dimension inputBits : Nat) : Nat :=
  max (determinantBitLengthBound dimension inputBits)
    (smithCertificatePolynomialBitLengthBound dimension inputBits)

namespace PolynomialBounds

public def additionCost
    {left right : Nat → Nat → Nat}
    (hleft : PolyEnvelope left) (hright : PolyEnvelope right) :
    PolyEnvelope (fun dimension inputBits ↦
      additionCostForBitLengths
        (left dimension inputBits) (right dimension inputBits)) := by
  simpa only [additionCostForBitLengths] using
    PolyEnvelope.add (PolyEnvelope.constant 1) <|
      PolyEnvelope.mul (PolyEnvelope.constant 2) <|
        PolyEnvelope.pow
          (PolyEnvelope.add
            (PolyEnvelope.add hleft hright)
            (PolyEnvelope.constant 1)) 2

public def multiplicationCost
    {left right : Nat → Nat → Nat}
    (hleft : PolyEnvelope left) (hright : PolyEnvelope right) :
    PolyEnvelope (fun dimension inputBits ↦
      multiplicationCostForBitLengths
        (left dimension inputBits) (right dimension inputBits)) := by
  simpa only [multiplicationCostForBitLengths] using
    PolyEnvelope.add (PolyEnvelope.constant 1) <|
      PolyEnvelope.mul hright <|
        PolyEnvelope.add (PolyEnvelope.constant 1) <|
          PolyEnvelope.pow
            (PolyEnvelope.add
              (PolyEnvelope.add
                (PolyEnvelope.mul (PolyEnvelope.constant 2) hleft)
                hright)
              (PolyEnvelope.constant 2)) 2

public def divisionCost
    {numerator divisor : Nat → Nat → Nat}
    (hnumerator : PolyEnvelope numerator)
    (hdivisor : PolyEnvelope divisor) :
    PolyEnvelope (fun dimension inputBits ↦
      divisionCostForBitLengths
        (numerator dimension inputBits) (divisor dimension inputBits)) := by
  simpa only [divisionCostForBitLengths] using
    PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.add
          (PolyEnvelope.constant 8)
          (PolyEnvelope.mul hnumerator <|
            PolyEnvelope.add (PolyEnvelope.constant 3) <|
              PolyEnvelope.mul (PolyEnvelope.constant 2) hdivisor))
        (PolyEnvelope.mul (PolyEnvelope.constant 3) hnumerator))
      (PolyEnvelope.mul (PolyEnvelope.constant 3) hdivisor)

public def dotTerm
    {count left right : Nat → Nat → Nat}
    (hcount : PolyEnvelope count)
    (hleft : PolyEnvelope left) (hright : PolyEnvelope right) :
    PolyEnvelope (fun dimension inputBits ↦
      dotTermBitOperationBound
        (count dimension inputBits)
        (left dimension inputBits)
        (right dimension inputBits)) := by
  let sum := PolyEnvelope.add hleft hright
  let accumulator := PolyEnvelope.mul hcount
    (PolyEnvelope.add sum (PolyEnvelope.constant 1))
  simpa only [dotTermBitOperationBound] using
    PolyEnvelope.add
      (multiplicationCost hleft hright)
      (additionCost sum accumulator)

public def matrixMultiplication
    {dimension left right : Nat → Nat → Nat}
    (hdimension : PolyEnvelope dimension)
    (hleft : PolyEnvelope left) (hright : PolyEnvelope right) :
    PolyEnvelope (fun outerDimension inputBits ↦
      matrixMultiplicationBitOperationBound
        (dimension outerDimension inputBits)
        (left outerDimension inputBits)
        (right outerDimension inputBits)) := by
  simpa only [matrixMultiplicationBitOperationBound] using
    PolyEnvelope.mul (PolyEnvelope.pow hdimension 3)
      (dotTerm hdimension hleft hright)

public def certificateComposition
    {dimension left right : Nat → Nat → Nat}
    (hdimension : PolyEnvelope dimension)
    (hleft : PolyEnvelope left) (hright : PolyEnvelope right) :
    PolyEnvelope (fun outerDimension inputBits ↦
      certificateCompositionBitOperationBound
        (dimension outerDimension inputBits)
        (left outerDimension inputBits)
        (right outerDimension inputBits)) := by
  simpa only [certificateCompositionBitOperationBound] using
    PolyEnvelope.add
      (PolyEnvelope.mul (PolyEnvelope.constant 2)
        (matrixMultiplication hdimension hleft hright))
      (PolyEnvelope.mul (PolyEnvelope.constant 2)
        (matrixMultiplication hdimension hright hleft))

public def determinantBitLength :
    PolyEnvelope determinantBitLengthBound := by
  change PolyEnvelope (fun dimension inputBits ↦
    dimension * (Nat.size dimension + inputBits) + 2)
  exact PolyEnvelope.add
      (PolyEnvelope.mul PolyEnvelope.dimension <|
        PolyEnvelope.add
          (PolyEnvelope.natSize PolyEnvelope.dimension)
          PolyEnvelope.inputBits)
      (PolyEnvelope.constant 2)

public def iterationBitLength
    {dimension inputBits steps : Nat → Nat → Nat}
    (hdimension : PolyEnvelope dimension)
    (hinputBits : PolyEnvelope inputBits)
    (hsteps : PolyEnvelope steps) :
    PolyEnvelope (fun outerDimension outerBits ↦
      iterationBitLengthBound
        (dimension outerDimension outerBits)
        (inputBits outerDimension outerBits)
        (steps outerDimension outerBits)) := by
  simpa only [iterationBitLengthBound] using
    PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.mul hsteps <|
          PolyEnvelope.add
            (PolyEnvelope.add
              (PolyEnvelope.natSize hdimension) hinputBits)
            (PolyEnvelope.constant 3))
        hinputBits)
      (PolyEnvelope.constant 2)

public def determinantEntryExecution
    {dimension inputBits currentBits : Nat → Nat → Nat}
    (hdimension : PolyEnvelope dimension)
    (hinputBits : PolyEnvelope inputBits)
    (hcurrentBits : PolyEnvelope currentBits) :
    PolyEnvelope (fun outerDimension outerBits ↦
      determinantEntryExecutionBitOperationBound
        (dimension outerDimension outerBits)
        (inputBits outerDimension outerBits)
        (currentBits outerDimension outerBits)) := by
  let diagonal := PolyEnvelope.mul hdimension
    (PolyEnvelope.add hcurrentBits (PolyEnvelope.constant 1))
  let trailing := PolyEnvelope.mul hdimension
    (PolyEnvelope.add
      (PolyEnvelope.add hcurrentBits hinputBits)
      (PolyEnvelope.constant 1))
  let oldEntry :=
    PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.add
          (PolyEnvelope.add
            (PolyEnvelope.mul hdimension
              (additionCost hcurrentBits diagonal))
            (PolyEnvelope.constant 1))
          (multiplicationCost diagonal hinputBits))
        (PolyEnvelope.mul hdimension
          (dotTerm hdimension hcurrentBits hinputBits)))
      (additionCost
        (PolyEnvelope.add diagonal hinputBits) trailing)
  simpa only [determinantEntryExecutionBitOperationBound,
    entryBitOperationBound] using
      PolyEnvelope.add oldEntry
        (multiplicationCost (PolyEnvelope.constant 1) diagonal)

public def determinantExecution :
    PolyEnvelope determinantExecutionBitOperationBound := by
  let operand := iterationBitLength PolyEnvelope.dimension
    PolyEnvelope.inputBits PolyEnvelope.dimension
  change PolyEnvelope (fun dimension inputBits ↦
    dimension * dimension * dimension *
        determinantEntryExecutionBitOperationBound dimension inputBits
          (iterationBitLengthBound dimension inputBits dimension) +
      multiplicationCostForBitLengths 1
        (iterationBitLengthBound dimension inputBits dimension))
  exact PolyEnvelope.add
      (PolyEnvelope.mul
        (PolyEnvelope.mul
          (PolyEnvelope.mul PolyEnvelope.dimension
            PolyEnvelope.dimension)
          PolyEnvelope.dimension)
        (determinantEntryExecution PolyEnvelope.dimension
          PolyEnvelope.inputBits operand))
      (multiplicationCost (PolyEnvelope.constant 1) operand)

public def stageMinor :
    PolyEnvelope Principal.stageMinorPolynomialBits := by
  change PolyEnvelope (fun dimension inputBits ↦
    (dimension + 1) * ((dimension + 1) + (inputBits + 1)) + 2)
  exact PolyEnvelope.add
      (PolyEnvelope.mul
        (PolyEnvelope.add PolyEnvelope.dimension
          (PolyEnvelope.constant 1))
        (PolyEnvelope.add
          (PolyEnvelope.add PolyEnvelope.dimension
            (PolyEnvelope.constant 1))
          (PolyEnvelope.add PolyEnvelope.inputBits
            (PolyEnvelope.constant 1))))
      (PolyEnvelope.constant 2)

public def stagePairOperand :
    PolyEnvelope Principal.stagePairOperandPolynomialBits := by
  change PolyEnvelope (fun dimension inputBits ↦
    (inputBits + 1) +
      Principal.stageMinorPolynomialBits dimension inputBits)
  exact PolyEnvelope.add
      (PolyEnvelope.add PolyEnvelope.inputBits
        (PolyEnvelope.constant 1))
      stageMinor

public def stagePairCoefficient :
    PolyEnvelope Principal.stagePairCoefficientPolynomialBits := by
  change PolyEnvelope (fun dimension inputBits ↦
    2 * (Principal.stagePairOperandPolynomialBits
      dimension inputBits + 1) + 1)
  exact PolyEnvelope.add
      (PolyEnvelope.mul (PolyEnvelope.constant 2) <|
        PolyEnvelope.add stagePairOperand (PolyEnvelope.constant 1))
      (PolyEnvelope.constant 1)

public def stagePairRow :
    PolyEnvelope Principal.stagePairRowPolynomialBits := by
  change PolyEnvelope (fun dimension inputBits ↦
    2 + Principal.stagePairCoefficientPolynomialBits dimension inputBits +
      Principal.stagePairOperandPolynomialBits dimension inputBits)
  exact PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.constant 2) stagePairCoefficient)
      stagePairOperand

public def stageBase :
    PolyEnvelope Principal.stageBasePolynomialBits := by
  change PolyEnvelope (fun dimension inputBits ↦
    (inputBits + 1) +
      Principal.stageMinorPolynomialBits dimension inputBits +
      Principal.stagePairRowPolynomialBits dimension inputBits)
  exact PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.add PolyEnvelope.inputBits
          (PolyEnvelope.constant 1))
        stageMinor)
      stagePairRow

public def stageIntermediate :
    PolyEnvelope Principal.stageIntermediatePolynomialBits := by
  change PolyEnvelope (fun dimension inputBits ↦
    (Principal.stageBasePolynomialBits dimension inputBits + 1) +
      (dimension *
        (Principal.stagePairRowPolynomialBits dimension inputBits + 3) + 1))
  exact PolyEnvelope.add
      (PolyEnvelope.add stageBase (PolyEnvelope.constant 1))
      (PolyEnvelope.add
        (PolyEnvelope.mul PolyEnvelope.dimension <|
          PolyEnvelope.add stagePairRow (PolyEnvelope.constant 3))
        (PolyEnvelope.constant 1))

public def stagePolynomial :
    PolyEnvelope Principal.stagePolynomialBitLengthBound := by
  change PolyEnvelope (fun dimension inputBits ↦
    (Principal.stageIntermediatePolynomialBits dimension inputBits + 1) +
      (Principal.stageMinorPolynomialBits dimension inputBits + 1))
  exact PolyEnvelope.add
      (PolyEnvelope.add stageIntermediate (PolyEnvelope.constant 1))
      (PolyEnvelope.add stageMinor (PolyEnvelope.constant 1))

public def stageBoundary :
    PolyEnvelope Principal.stageBoundaryPolynomialBits := by
  change PolyEnvelope (fun dimension inputBits ↦
    2 * inputBits + 2 * dimension +
      2 * dimension * (dimension + inputBits) + 4)
  exact PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.add
          (PolyEnvelope.mul (PolyEnvelope.constant 2)
            PolyEnvelope.inputBits)
          (PolyEnvelope.mul (PolyEnvelope.constant 2)
            PolyEnvelope.dimension))
        (PolyEnvelope.mul
          (PolyEnvelope.mul (PolyEnvelope.constant 2)
            PolyEnvelope.dimension)
          (PolyEnvelope.add PolyEnvelope.dimension
            PolyEnvelope.inputBits)))
      (PolyEnvelope.constant 4)

public def principalPolynomial :
    PolyEnvelope Principal.principalPolynomialBitLengthBound := by
  let stageAtBoundary :=
    PolyEnvelope.monotoneSubstitution stagePolynomial
      PolyEnvelope.dimension stageBoundary
  change PolyEnvelope (fun dimension inputBits ↦
    (inputBits + 1) +
      Principal.stagePolynomialBitLengthBound dimension
        (Principal.stageBoundaryPolynomialBits dimension inputBits))
  exact PolyEnvelope.add
      (PolyEnvelope.add PolyEnvelope.inputBits
        (PolyEnvelope.constant 1))
      stageAtBoundary

public def boundedColumnIntermediate :
    PolyEnvelope boundedColumnIntermediatePolynomialBitLengthBound := by
  let upper :=
    PolyEnvelope.add
      (PolyEnvelope.add PolyEnvelope.inputBits <|
        PolyEnvelope.mul PolyEnvelope.dimension <|
          PolyEnvelope.add
            (PolyEnvelope.add
              (PolyEnvelope.natSize PolyEnvelope.dimension)
              (PolyEnvelope.mul (PolyEnvelope.constant 2) <|
                PolyEnvelope.add PolyEnvelope.inputBits
                  (PolyEnvelope.constant 1)))
            (PolyEnvelope.constant 6))
      (PolyEnvelope.constant 1)
  apply PolyEnvelope.of_le upper
  intro dimension inputBits
  cases dimension with
  | zero =>
      simp [boundedColumnIntermediatePolynomialBitLengthBound]
  | succ order =>
      simp only [boundedColumnIntermediatePolynomialBitLengthBound]
      gcongr
      omega

public def boundedColumnMultiplier :
    PolyEnvelope boundedColumnMultiplierPolynomialBitLengthBound := by
  let determinantAtInput :=
    PolyEnvelope.monotoneSubstitution determinantBitLength
      PolyEnvelope.dimension PolyEnvelope.inputBits
  let upper :=
    PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.natSize PolyEnvelope.dimension)
        boundedColumnIntermediate)
      determinantAtInput
  apply PolyEnvelope.of_le upper
  intro dimension inputBits
  cases dimension with
  | zero =>
      simp [boundedColumnMultiplierPolynomialBitLengthBound]
  | succ order =>
      simp only [boundedColumnMultiplierPolynomialBitLengthBound,
        determinantBitLengthBound]
      have sizeMono : Nat.size order ≤ Nat.size (order + 1) :=
        Nat.size_le_size (Nat.le_succ order)
      gcongr
      omega

public def boundedColumnInverse :
    PolyEnvelope boundedColumnInversePolynomialBitLengthBound := by
  let determinantAtIntermediate :=
    PolyEnvelope.monotoneSubstitution determinantBitLength
      PolyEnvelope.dimension boundedColumnIntermediate
  let upper :=
    PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.natSize PolyEnvelope.dimension)
        PolyEnvelope.inputBits)
      determinantAtIntermediate
  apply PolyEnvelope.of_le upper
  intro dimension inputBits
  cases dimension with
  | zero =>
      simp [boundedColumnInversePolynomialBitLengthBound]
  | succ order =>
      simp only [boundedColumnInversePolynomialBitLengthBound,
        determinantBitLengthBound]
      have sizeMono : Nat.size order ≤ Nat.size (order + 1) :=
        Nat.size_le_size (Nat.le_succ order)
      gcongr
      omega

public def principalMultiplier :
    PolyEnvelope Principal.principalMultiplierPrefixPolynomialBitLengthBound := by
  let upper :=
    PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.add PolyEnvelope.dimension principalPolynomial)
        (PolyEnvelope.mul PolyEnvelope.dimension <|
          PolyEnvelope.add PolyEnvelope.dimension
            PolyEnvelope.inputBits))
      (PolyEnvelope.constant 2)
  apply PolyEnvelope.of_le upper
  intro dimension inputBits
  cases dimension with
  | zero =>
      simp [Principal.principalMultiplierPrefixPolynomialBitLengthBound]
  | succ order =>
      simp only [Principal.principalMultiplierPrefixPolynomialBitLengthBound]
      have productLe :
          order * (order + inputBits) ≤
            (order + 1) * (order + 1 + inputBits) :=
        Nat.mul_le_mul (Nat.le_succ order) (by omega)
      omega

public def principalInverse :
    PolyEnvelope Principal.principalInversePrefixPolynomialBitLengthBound := by
  let upper :=
    PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.add PolyEnvelope.dimension PolyEnvelope.inputBits)
        (PolyEnvelope.mul PolyEnvelope.dimension <|
          PolyEnvelope.add PolyEnvelope.dimension principalPolynomial))
      (PolyEnvelope.constant 2)
  apply PolyEnvelope.of_le upper
  intro dimension inputBits
  cases dimension with
  | zero =>
      simp [Principal.principalInversePrefixPolynomialBitLengthBound]
  | succ order =>
      simp only [Principal.principalInversePrefixPolynomialBitLengthBound]
      have productLe :
          order *
              (order +
                Principal.principalPolynomialBitLengthBound
                  (order + 1) inputBits) ≤
            (order + 1) *
              (order + 1 +
                Principal.principalPolynomialBitLengthBound
                  (order + 1) inputBits) :=
        Nat.mul_le_mul (Nat.le_succ order) (by omega)
      omega

public def boundedXGCDCoefficient :
    PolyEnvelope (fun _ inputBits ↦
      boundedXGCDCoefficientBitLengthBound inputBits) := by
  simpa only [boundedXGCDCoefficientBitLengthBound] using
    PolyEnvelope.mul (PolyEnvelope.constant 2) <|
      PolyEnvelope.add PolyEnvelope.inputBits
        (PolyEnvelope.constant 2)

public def boundedXGCDRawCoefficient :
    PolyEnvelope (fun _ inputBits ↦
      boundedXGCDRawCoefficientBitLengthBound inputBits) := by
  change PolyEnvelope (fun _ inputBits ↦
    inputBits +
      2 * boundedXGCDCoefficientBitLengthBound inputBits + 2)
  exact PolyEnvelope.add
    (PolyEnvelope.add PolyEnvelope.inputBits <|
      PolyEnvelope.mul (PolyEnvelope.constant 2)
        boundedXGCDCoefficient)
    (PolyEnvelope.constant 2)

public def boundedXGCDReduction :
    PolyEnvelope (fun _ inputBits ↦
      boundedXGCDReductionCostBound inputBits) := by
  let rawPlusOne :=
    PolyEnvelope.add boundedXGCDRawCoefficient
      (PolyEnvelope.constant 1)
  let finalRight :=
    PolyEnvelope.add
      (PolyEnvelope.add boundedXGCDRawCoefficient
        (PolyEnvelope.constant 1))
      PolyEnvelope.inputBits
  let comparison :=
    PolyEnvelope.add
      (PolyEnvelope.mul (PolyEnvelope.constant 2) PolyEnvelope.inputBits)
      (PolyEnvelope.constant 2)
  change PolyEnvelope (fun _ inputBits ↦
    (2 * inputBits + 2) +
      divisionCostForBitLengths
        (boundedXGCDRawCoefficientBitLengthBound inputBits) inputBits +
      multiplicationCostForBitLengths
        (boundedXGCDRawCoefficientBitLengthBound inputBits + 1) inputBits +
      additionCostForBitLengths
        (boundedXGCDRawCoefficientBitLengthBound inputBits)
        (boundedXGCDRawCoefficientBitLengthBound inputBits + 1 + inputBits))
  exact PolyEnvelope.add
    (PolyEnvelope.add
      (PolyEnvelope.add
        comparison
        (divisionCost boundedXGCDRawCoefficient
          PolyEnvelope.inputBits))
      (multiplicationCost rawPlusOne PolyEnvelope.inputBits))
    (additionCost boundedXGCDRawCoefficient finalRight)

public def boundedXGCDEuclideanUpdate :
    PolyEnvelope (fun _ inputBits ↦
      boundedXGCDEuclideanUpdateCostBound inputBits) := by
  let inputPlusOne :=
    PolyEnvelope.add PolyEnvelope.inputBits (PolyEnvelope.constant 1)
  let additionRight :=
    PolyEnvelope.add inputPlusOne boundedXGCDCoefficient
  change PolyEnvelope (fun _ inputBits ↦
    1 + divisionCostForBitLengths inputBits inputBits +
      multiplicationCostForBitLengths (inputBits + 1)
        (boundedXGCDCoefficientBitLengthBound inputBits) +
      additionCostForBitLengths
        (boundedXGCDCoefficientBitLengthBound inputBits)
        (inputBits + 1 +
          boundedXGCDCoefficientBitLengthBound inputBits))
  exact PolyEnvelope.add
    (PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.constant 1)
        (divisionCost PolyEnvelope.inputBits PolyEnvelope.inputBits))
      (multiplicationCost inputPlusOne boundedXGCDCoefficient))
    (additionCost boundedXGCDCoefficient additionRight)

public def boundedXGCDStep :
    PolyEnvelope (fun _ inputBits ↦
      boundedXGCDStepCostBound inputBits) := by
  change PolyEnvelope (fun _ inputBits ↦
    boundedXGCDEuclideanUpdateCostBound inputBits +
      boundedXGCDReductionCostBound inputBits)
  exact PolyEnvelope.add boundedXGCDEuclideanUpdate boundedXGCDReduction

public def boundedIntXGCDUniform :
    PolyEnvelope (fun _ inputBits ↦
      Principal.boundedIntXGCDUniformBitOperationBound inputBits) := by
  change PolyEnvelope (fun _ inputBits ↦
    3 + (2 * inputBits + 1) * boundedXGCDStepCostBound inputBits)
  exact PolyEnvelope.add
    (PolyEnvelope.constant 3) <|
      PolyEnvelope.mul
        (PolyEnvelope.add
          (PolyEnvelope.mul (PolyEnvelope.constant 2)
            PolyEnvelope.inputBits)
          (PolyEnvelope.constant 1))
        boundedXGCDStep

public def integerDivMod :
    PolyEnvelope (fun _ inputBits ↦
      Principal.integerDivModBitOperationBound inputBits) := by
  change PolyEnvelope (fun _ inputBits ↦
    divisionCostForBitLengths inputBits inputBits)
  exact divisionCost PolyEnvelope.inputBits PolyEnvelope.inputBits

public def principalScalarTransition :
    PolyEnvelope (fun _ inputBits ↦
      principalScalarTransitionBitOperationBound inputBits) := by
  change PolyEnvelope (fun _ inputBits ↦
    Principal.boundedIntXGCDUniformBitOperationBound inputBits + 1 +
      3 * Principal.integerDivModBitOperationBound inputBits + 1)
  exact PolyEnvelope.add
    (PolyEnvelope.add
      (PolyEnvelope.add boundedIntXGCDUniform
        (PolyEnvelope.constant 1))
      (PolyEnvelope.mul (PolyEnvelope.constant 3) integerDivMod))
    (PolyEnvelope.constant 1)

public def smithSearchDecision :
    PolyEnvelope (fun _ inputBits ↦
      smithSearchDecisionBitOperationBound inputBits) := by
  change PolyEnvelope (fun _ inputBits ↦
    2 + divisionCostForBitLengths inputBits inputBits)
  exact PolyEnvelope.add (PolyEnvelope.constant 2)
    (divisionCost PolyEnvelope.inputBits PolyEnvelope.inputBits)

public def rowTraceTransform
    {dimension forward inverse : Nat → Nat → Nat}
    (hdimension : PolyEnvelope dimension)
    (hforward : PolyEnvelope forward)
    (hinverse : PolyEnvelope inverse) :
    PolyEnvelope (fun outerDimension inputBits ↦
      rowTraceTransformBitLengthBound
        (dimension outerDimension inputBits)
        (forward outerDimension inputBits)
        (inverse outerDimension inputBits)) := by
  change PolyEnvelope (fun outerDimension inputBits ↦
    Nat.size (dimension outerDimension inputBits) +
      forward outerDimension inputBits +
      inverse outerDimension inputBits)
  exact PolyEnvelope.add
    (PolyEnvelope.add (PolyEnvelope.natSize hdimension) hforward)
    hinverse

public def rowTraceDense
    {dimension steps matrix forward inverse : Nat → Nat → Nat}
    (hdimension : PolyEnvelope dimension)
    (hsteps : PolyEnvelope steps)
    (hmatrix : PolyEnvelope matrix)
    (hforward : PolyEnvelope forward)
    (hinverse : PolyEnvelope inverse) :
    PolyEnvelope (fun outerDimension inputBits ↦
      rowTraceDenseBitOperationBound
        (dimension outerDimension inputBits)
        (steps outerDimension inputBits)
        (matrix outerDimension inputBits)
        (forward outerDimension inputBits)
        (inverse outerDimension inputBits)) := by
  let transform := rowTraceTransform hdimension hforward hinverse
  change PolyEnvelope (fun outerDimension inputBits ↦
    steps outerDimension inputBits *
      (matrixMultiplicationBitOperationBound
          (dimension outerDimension inputBits)
          (Nat.size (dimension outerDimension inputBits) +
            forward outerDimension inputBits +
            inverse outerDimension inputBits)
          (matrix outerDimension inputBits) +
        2 * matrixMultiplicationBitOperationBound
          (dimension outerDimension inputBits)
          (Nat.size (dimension outerDimension inputBits) +
            forward outerDimension inputBits +
            inverse outerDimension inputBits)
          (Nat.size (dimension outerDimension inputBits) +
            forward outerDimension inputBits +
            inverse outerDimension inputBits)))
  exact PolyEnvelope.mul hsteps <|
    PolyEnvelope.add
      (matrixMultiplication hdimension transform hmatrix)
      (PolyEnvelope.mul (PolyEnvelope.constant 2) <|
        matrixMultiplication hdimension transform transform)

public def principalExecution :
    PolyEnvelope principalExecutionBitOperationBound := by
  let scalarAtOperand :=
    PolyEnvelope.monotoneSubstitution principalScalarTransition
      (PolyEnvelope.constant 0) principalPolynomial
  let dense :=
    rowTraceDense PolyEnvelope.dimension
      (PolyEnvelope.pow PolyEnvelope.dimension 3)
      principalPolynomial principalMultiplier principalInverse
  change PolyEnvelope (fun dimension inputBits ↦
    dimension ^ 3 *
        principalScalarTransitionBitOperationBound
          (Principal.principalPolynomialBitLengthBound
            dimension inputBits) +
      rowTraceDenseBitOperationBound dimension (dimension ^ 3)
        (Principal.principalPolynomialBitLengthBound dimension inputBits)
        (Principal.principalMultiplierPrefixPolynomialBitLengthBound
          dimension inputBits)
        (Principal.principalInversePrefixPolynomialBitLengthBound
          dimension inputBits))
  exact PolyEnvelope.add
    (PolyEnvelope.mul
      (PolyEnvelope.pow PolyEnvelope.dimension 3) scalarAtOperand)
    dense

public def preparationExecution :
    PolyEnvelope preparationExecutionBitOperationBound := by
  let previousDimension :=
    PolyEnvelope.sub (g := fun _ _ ↦ 1)
      PolyEnvelope.dimension
  let previousDeterminant :=
    PolyEnvelope.monotoneSubstitution determinantExecution
      previousDimension PolyEnvelope.inputBits
  let step :=
    PolyEnvelope.mul PolyEnvelope.dimension <|
      PolyEnvelope.add previousDeterminant (PolyEnvelope.constant 1)
  apply PolyEnvelope.dimensionRecursion
    (PolyEnvelope.constant 0) step
  intro dimension inputBits
  rw [preparationExecutionBitOperationBound]
  simp only [Nat.add_sub_cancel]
  omega

public def preparedPrincipalExecution :
    PolyEnvelope preparedPrincipalExecutionBitOperationBound := by
  let forwardProduct :=
    matrixMultiplication PolyEnvelope.dimension
      principalMultiplier (PolyEnvelope.constant 1)
  let inverseProduct :=
    matrixMultiplication PolyEnvelope.dimension
      (PolyEnvelope.constant 1) principalInverse
  change PolyEnvelope (fun dimension inputBits ↦
    preparationExecutionBitOperationBound dimension inputBits +
      (principalExecutionBitOperationBound dimension inputBits +
        matrixMultiplicationBitOperationBound dimension
          (Principal.principalMultiplierPrefixPolynomialBitLengthBound
            dimension inputBits) 1 +
        matrixMultiplicationBitOperationBound dimension 1
          (Principal.principalInversePrefixPolynomialBitLengthBound
            dimension inputBits)))
  exact PolyEnvelope.add preparationExecution <|
    PolyEnvelope.add
      (PolyEnvelope.add principalExecution forwardProduct)
      inverseProduct

public def boundedColumnExecution :
    PolyEnvelope boundedColumnExecutionBitOperationBound := by
  let dense :=
    rowTraceDense PolyEnvelope.dimension PolyEnvelope.dimension
      boundedColumnIntermediate boundedColumnMultiplier boundedColumnInverse
  change PolyEnvelope (fun dimension inputBits ↦
    dimension * principalScalarTransitionBitOperationBound inputBits +
      rowTraceDenseBitOperationBound dimension dimension
        (boundedColumnIntermediatePolynomialBitLengthBound
          dimension inputBits)
        (boundedColumnMultiplierPolynomialBitLengthBound
          dimension inputBits)
        (boundedColumnInversePolynomialBitLengthBound
          dimension inputBits))
  exact PolyEnvelope.add
    (PolyEnvelope.mul PolyEnvelope.dimension principalScalarTransition)
    dense

public def clearExecution :
    PolyEnvelope clearExecutionBitOperationBound := by
  let previousDimension :=
    PolyEnvelope.sub (g := fun _ _ ↦ 1)
      PolyEnvelope.dimension
  change PolyEnvelope (fun dimension inputBits ↦
    (dimension - 1) *
        Principal.integerDivModBitOperationBound inputBits +
      matrixMultiplicationBitOperationBound dimension
        (inputBits + 1) inputBits)
  exact PolyEnvelope.add
    (PolyEnvelope.mul previousDimension integerDivMod)
    (matrixMultiplication PolyEnvelope.dimension
      (PolyEnvelope.add PolyEnvelope.inputBits
        (PolyEnvelope.constant 1))
      PolyEnvelope.inputBits)

public def injectExecution :
    PolyEnvelope injectExecutionBitOperationBound := by
  change PolyEnvelope (fun dimension inputBits ↦
    matrixMultiplicationBitOperationBound dimension inputBits 1)
  exact matrixMultiplication PolyEnvelope.dimension
    PolyEnvelope.inputBits (PolyEnvelope.constant 1)

public def preparedMultiplier
    {order inputBits determinantBits : Nat → Nat → Nat}
    (horder : PolyEnvelope order)
    (hinputBits : PolyEnvelope inputBits)
    (hdeterminantBits : PolyEnvelope determinantBits) :
    PolyEnvelope (fun dimension outerBits ↦
      preparedMultiplierBits
        (order dimension outerBits)
        (inputBits dimension outerBits)
        (determinantBits dimension outerBits)) := by
  let orderPlusOne :=
    PolyEnvelope.add horder (PolyEnvelope.constant 1)
  let determinantAtInput :=
    PolyEnvelope.monotoneSubstitution determinantBitLength
      horder hinputBits
  change PolyEnvelope (fun dimension outerBits ↦
    Nat.size (order dimension outerBits + 1) +
      determinantBits dimension outerBits +
      determinantBitLengthBound
        (order dimension outerBits) (inputBits dimension outerBits))
  exact PolyEnvelope.add
    (PolyEnvelope.add
      (PolyEnvelope.natSize orderPlusOne) hdeterminantBits)
    determinantAtInput

public def preparedInverse
    {order inputBits determinantBits : Nat → Nat → Nat}
    (horder : PolyEnvelope order)
    (hinputBits : PolyEnvelope inputBits)
    (hdeterminantBits : PolyEnvelope determinantBits) :
    PolyEnvelope (fun dimension outerBits ↦
      preparedInverseBits
        (order dimension outerBits)
        (inputBits dimension outerBits)
        (determinantBits dimension outerBits)) := by
  let orderPlusOne :=
    PolyEnvelope.add horder (PolyEnvelope.constant 1)
  let determinantAtDeterminant :=
    PolyEnvelope.monotoneSubstitution determinantBitLength
      horder hdeterminantBits
  change PolyEnvelope (fun dimension outerBits ↦
    Nat.size (order dimension outerBits + 1) +
      inputBits dimension outerBits +
      determinantBitLengthBound
        (order dimension outerBits) (determinantBits dimension outerBits))
  exact PolyEnvelope.add
    (PolyEnvelope.add
      (PolyEnvelope.natSize orderPlusOne) hinputBits)
    determinantAtDeterminant

public def passTransform
    {order inputBits determinantBits : Nat → Nat → Nat}
    (horder : PolyEnvelope order)
    (hinputBits : PolyEnvelope inputBits)
    (hdeterminantBits : PolyEnvelope determinantBits) :
    PolyEnvelope (fun dimension outerBits ↦
      passTransformBitLengthBound
        (order dimension outerBits)
        (inputBits dimension outerBits)
        (determinantBits dimension outerBits)) := by
  let dimension :=
    PolyEnvelope.add horder (PolyEnvelope.constant 1)
  let intermediate :=
    PolyEnvelope.monotoneSubstitution boundedColumnIntermediate
      dimension hinputBits
  let boundedForward :=
    PolyEnvelope.monotoneSubstitution boundedColumnMultiplier
      dimension hinputBits
  let boundedInverse :=
    PolyEnvelope.monotoneSubstitution boundedColumnInverse
      dimension hinputBits
  let preparedForward :=
    preparedMultiplier horder intermediate hdeterminantBits
  let preparedBackward :=
    preparedInverse horder intermediate hdeterminantBits
  change PolyEnvelope (fun outerDimension outerBits ↦
    Nat.max
      (boundedColumnMultiplierPolynomialBitLengthBound
        (order outerDimension outerBits + 1)
        (inputBits outerDimension outerBits))
      (Nat.max
        (boundedColumnInversePolynomialBitLengthBound
          (order outerDimension outerBits + 1)
          (inputBits outerDimension outerBits))
        (Nat.max
          (preparedMultiplierBits
            (order outerDimension outerBits)
            (boundedColumnIntermediatePolynomialBitLengthBound
              (order outerDimension outerBits + 1)
              (inputBits outerDimension outerBits))
            (determinantBits outerDimension outerBits))
          (preparedInverseBits
            (order outerDimension outerBits)
            (boundedColumnIntermediatePolynomialBitLengthBound
              (order outerDimension outerBits + 1)
              (inputBits outerDimension outerBits))
            (determinantBits outerDimension outerBits)))))
  exact PolyEnvelope.max boundedForward <|
    PolyEnvelope.max boundedInverse <|
      PolyEnvelope.max preparedForward preparedBackward

public def passPhaseTransform
    {order inputBits determinantBits : Nat → Nat → Nat}
    (horder : PolyEnvelope order)
    (hinputBits : PolyEnvelope inputBits)
    (hdeterminantBits : PolyEnvelope determinantBits) :
    PolyEnvelope (fun dimension outerBits ↦
      passPhaseTransformBitLengthBound
        (order dimension outerBits)
        (inputBits dimension outerBits)
        (determinantBits dimension outerBits)) := by
  change PolyEnvelope (fun dimension outerBits ↦
    Nat.max 1
      (passTransformBitLengthBound
        (order dimension outerBits)
        (inputBits dimension outerBits)
        (determinantBits dimension outerBits)))
  exact PolyEnvelope.max (PolyEnvelope.constant 1)
    (passTransform horder hinputBits hdeterminantBits)

public def passExecution
    {order inputBits determinantBits : Nat → Nat → Nat}
    (horder : PolyEnvelope order)
    (hinputBits : PolyEnvelope inputBits)
    (hdeterminantBits : PolyEnvelope determinantBits) :
    PolyEnvelope (fun dimension outerBits ↦
      passExecutionBitOperationBound
        (order dimension outerBits)
        (inputBits dimension outerBits)
        (determinantBits dimension outerBits)) := by
  let dimension :=
    PolyEnvelope.add horder (PolyEnvelope.constant 1)
  let leftBits :=
    PolyEnvelope.monotoneSubstitution boundedColumnIntermediate
      dimension hinputBits
  let transformBits :=
    passPhaseTransform horder hinputBits hdeterminantBits
  let leftCost :=
    PolyEnvelope.monotoneSubstitution boundedColumnExecution
      dimension hinputBits
  let rightCost :=
    PolyEnvelope.monotoneSubstitution preparedPrincipalExecution
      dimension leftBits
  change PolyEnvelope (fun outerDimension outerBits ↦
    boundedColumnExecutionBitOperationBound
        (order outerDimension outerBits + 1)
        (inputBits outerDimension outerBits) +
      preparedPrincipalExecutionBitOperationBound
        (order outerDimension outerBits + 1)
        (boundedColumnIntermediatePolynomialBitLengthBound
          (order outerDimension outerBits + 1)
          (inputBits outerDimension outerBits)) +
      certificateCompositionBitOperationBound
        (order outerDimension outerBits + 1)
        (passPhaseTransformBitLengthBound
          (order outerDimension outerBits)
          (inputBits outerDimension outerBits)
          (determinantBits outerDimension outerBits))
        (passPhaseTransformBitLengthBound
          (order outerDimension outerBits)
          (inputBits outerDimension outerBits)
          (determinantBits outerDimension outerBits)))
  exact PolyEnvelope.add
    (PolyEnvelope.add leftCost rightCost)
    (certificateComposition dimension transformBits transformBits)

public def stabilizationFactor :
    PolyEnvelope stabilizationFactorBitLengthBound := by
  let workPlusOne :=
    PolyEnvelope.add PolyEnvelope.inputBits (PolyEnvelope.constant 1)
  let pass :=
    passTransform PolyEnvelope.dimension workPlusOne
      PolyEnvelope.inputBits
  change PolyEnvelope (fun order workBits ↦
    Nat.max
      (passTransformBitLengthBound order (workBits + 1) workBits)
      (workBits + 1))
  exact PolyEnvelope.max pass workPlusOne

public def stabilizationComposition :
    PolyEnvelope stabilizationCompositionBitLength := by
  let orderPlusOne :=
    PolyEnvelope.add PolyEnvelope.dimension (PolyEnvelope.constant 1)
  change PolyEnvelope (fun order workBits ↦
    Nat.size (order + 1) +
      stabilizationFactorBitLengthBound order workBits)
  exact PolyEnvelope.add
    (PolyEnvelope.natSize orderPlusOne) stabilizationFactor

public def stabilizationTransform :
    PolyEnvelope stabilizationTransformWorkBound := by
  let previousDimension :=
    PolyEnvelope.sub (g := fun _ _ ↦ 1)
      PolyEnvelope.dimension
  let compositionAtPrevious :=
    PolyEnvelope.monotoneSubstitution stabilizationComposition
      previousDimension PolyEnvelope.inputBits
  change PolyEnvelope (fun dimension workBits ↦
    (3 * workBits + 2) *
      stabilizationCompositionBitLength (dimension - 1) workBits)
  exact PolyEnvelope.mul
    (PolyEnvelope.add
      (PolyEnvelope.mul (PolyEnvelope.constant 3)
        PolyEnvelope.inputBits)
      (PolyEnvelope.constant 2))
    compositionAtPrevious

public def stabilizationExecutionTransform :
    PolyEnvelope stabilizationExecutionTransformBitLengthBound := by
  change PolyEnvelope (fun dimension workBits ↦
    Nat.size dimension +
      2 * stabilizationTransformWorkBound dimension workBits)
  exact PolyEnvelope.add
    (PolyEnvelope.natSize PolyEnvelope.dimension)
    (PolyEnvelope.mul (PolyEnvelope.constant 2)
      stabilizationTransform)

public def stabilizationExecutionComposition :
    PolyEnvelope stabilizationExecutionCompositionBitOperationBound := by
  change PolyEnvelope (fun dimension workBits ↦
    certificateCompositionBitOperationBound dimension
      (stabilizationExecutionTransformBitLengthBound dimension workBits)
      (stabilizationExecutionTransformBitLengthBound dimension workBits))
  exact certificateComposition PolyEnvelope.dimension
    stabilizationExecutionTransform stabilizationExecutionTransform

public def stabilizationExecutionLevel :
    PolyEnvelope stabilizationExecutionLevelBitOperationBound := by
  let previousDimension :=
    PolyEnvelope.sub (g := fun _ _ ↦ 1)
      PolyEnvelope.dimension
  let workPlusOne :=
    PolyEnvelope.add PolyEnvelope.inputBits (PolyEnvelope.constant 1)
  let pass :=
    passExecution previousDimension workPlusOne PolyEnvelope.inputBits
  change PolyEnvelope (fun dimension workBits ↦
    (dimension - 1) * smithSearchDecisionBitOperationBound workBits +
      (dimension - 1) * (dimension - 1) *
        smithSearchDecisionBitOperationBound workBits +
      passExecutionBitOperationBound (dimension - 1)
        (workBits + 1) workBits +
      clearExecutionBitOperationBound dimension workBits +
      injectExecutionBitOperationBound dimension workBits +
      3 * stabilizationExecutionCompositionBitOperationBound
        dimension workBits)
  exact PolyEnvelope.add
    (PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.add
          (PolyEnvelope.add
            (PolyEnvelope.mul previousDimension smithSearchDecision)
            (PolyEnvelope.mul
              (PolyEnvelope.mul previousDimension previousDimension)
              smithSearchDecision))
          pass)
        clearExecution)
      injectExecution)
    (PolyEnvelope.mul (PolyEnvelope.constant 3)
      stabilizationExecutionComposition)

public def stabilizationExecution :
    PolyEnvelope stabilizationExecutionBitOperationBound := by
  change PolyEnvelope (fun dimension workBits ↦
    (workBits + 1) *
      stabilizationExecutionLevelBitOperationBound dimension workBits)
  exact PolyEnvelope.mul
    (PolyEnvelope.add PolyEnvelope.inputBits (PolyEnvelope.constant 1))
    stabilizationExecutionLevel

public def smithTransform :
    PolyEnvelope smithTransformWorkBound := by
  let step :=
    PolyEnvelope.add
      (PolyEnvelope.add
        (PolyEnvelope.natSize PolyEnvelope.dimension)
        stabilizationTransform)
      (PolyEnvelope.constant 1)
  apply PolyEnvelope.dimensionRecursion
    (PolyEnvelope.constant 0) step
  intro dimension workBits
  rw [smithTransformWorkBound]
  omega

public def smithCoefficientWork :
    PolyEnvelope smithCoefficientWorkBitLength := by
  change PolyEnvelope (fun dimension inputBits ↦
    max inputBits (determinantBitLengthBound dimension inputBits))
  exact PolyEnvelope.max PolyEnvelope.inputBits determinantBitLength

public def smithCertificatePolynomial :
    PolyEnvelope smithCertificatePolynomialBitLengthBound := by
  change PolyEnvelope (fun dimension inputBits ↦
    smithTransformWorkBound dimension
      (smithCoefficientWorkBitLength dimension inputBits))
  exact PolyEnvelope.monotoneSubstitution
    smithTransform PolyEnvelope.dimension smithCoefficientWork

public def smithExecutionWork :
    PolyEnvelope smithExecutionBitOperationWorkBound := by
  let previousDimension :=
    PolyEnvelope.sub (g := fun _ _ ↦ 1)
      PolyEnvelope.dimension
  let recursiveTransform :=
    PolyEnvelope.monotoneSubstitution smithTransform
      previousDimension PolyEnvelope.inputBits
  let recursiveTransformAtLeastOne :=
    PolyEnvelope.max (PolyEnvelope.constant 1) recursiveTransform
  let composition :=
    certificateComposition PolyEnvelope.dimension
      stabilizationTransform recursiveTransformAtLeastOne
  let step := PolyEnvelope.add stabilizationExecution composition
  apply PolyEnvelope.dimensionRecursion
    (PolyEnvelope.constant 0) step
  intro dimension workBits
  rw [smithExecutionBitOperationWorkBound]
  simp only [Nat.add_sub_cancel]
  have maxEq :
      max 1 (smithTransformWorkBound dimension workBits) =
        Nat.max 1 (smithTransformWorkBound dimension workBits) := rfl
  rw [maxEq]
  omega

public def smithExecutionPolynomial :
    PolyEnvelope smithExecutionPolynomialBitOperationBound := by
  change PolyEnvelope (fun dimension inputBits ↦
    smithExecutionBitOperationWorkBound dimension
      (smithCoefficientWorkBitLength dimension inputBits))
  exact PolyEnvelope.monotoneSubstitution
    smithExecutionWork PolyEnvelope.dimension smithCoefficientWork

public def smithOutputEntry :
    PolyEnvelope smithOutputPolynomialEntryBitBound := by
  change PolyEnvelope (fun dimension inputBits ↦
    max (determinantBitLengthBound dimension inputBits)
      (smithCertificatePolynomialBitLengthBound dimension inputBits))
  exact PolyEnvelope.max determinantBitLength smithCertificatePolynomial

public def matrixEncoding :
    PolyEnvelope matrixEncodingLengthBound := by
  change PolyEnvelope (fun dimension entryBits ↦
    2 * (2 * dimension.size + 2 +
      dimension * dimension * (2 * (entryBits + 2))) + 2)
  exact PolyEnvelope.add
    (PolyEnvelope.mul (PolyEnvelope.constant 2) <|
      PolyEnvelope.add
        (PolyEnvelope.add
          (PolyEnvelope.mul (PolyEnvelope.constant 2) <|
            PolyEnvelope.natSize PolyEnvelope.dimension)
          (PolyEnvelope.constant 2))
        (PolyEnvelope.mul
          (PolyEnvelope.mul PolyEnvelope.dimension
            PolyEnvelope.dimension)
          (PolyEnvelope.mul (PolyEnvelope.constant 2) <|
            PolyEnvelope.add PolyEnvelope.inputBits
              (PolyEnvelope.constant 2))))
    (PolyEnvelope.constant 2)

public def smithOutputEncoding :
    PolyEnvelope smithOutputEncodingLengthBound := by
  change PolyEnvelope (fun dimension entryBits ↦
    2 * (5 * matrixEncodingLengthBound dimension entryBits) + 2)
  exact PolyEnvelope.add
    (PolyEnvelope.mul (PolyEnvelope.constant 2) <|
      PolyEnvelope.mul (PolyEnvelope.constant 5) matrixEncoding)
    (PolyEnvelope.constant 2)

public def smithOutputEncodingPolynomial :
    PolyEnvelope (fun dimension inputBits ↦
      smithOutputEncodingLengthBound dimension
        (smithOutputPolynomialEntryBitBound dimension inputBits)) := by
  exact PolyEnvelope.monotoneSubstitution smithOutputEncoding
    PolyEnvelope.dimension smithOutputEntry

end PolynomialBounds

end NormalForms.Research.KannanBachem
