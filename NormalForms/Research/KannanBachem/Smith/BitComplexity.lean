/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.RecursiveCoefficientSize
public import NormalForms.Research.KannanBachem.Hermite.PreparedBitComplexity
import all NormalForms.Research.KannanBachem.Smith.RecursiveCoefficientSize
import all NormalForms.Research.KannanBachem.Hermite.PreparedBitComplexity

/-!
# Bit Complexity of Kannan--Bachem Smith Normal Form

This module charges the arithmetic executed by every stabilization branch and
the outer Smith recursion.  The charge includes bounded XGCD and division,
row and column arithmetic, prepared principal HNF, and all four dense matrix
products needed when strong certificates are composed.  The final bound
depends only on the original dimension and coefficient bit length.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix BigOperators
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith
open NormalForms.Research
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminant

/-- One costed scalar entry of the reference dense matrix product. -/
@[expose] def matrixEntryWithCost {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int) (row column : Fin n) :
    BitCost.WithCost BitCost.SignMagnitude :=
  dotWithCost (List.finRange n)
    (fun index => BitCost.SignMagnitude.ofInt (left row index))
    (fun index => BitCost.SignMagnitude.ofInt (right index column))

/-- Value matrix returned by the costed dense multiplication reference. -/
@[expose] def matrixProductWithCost {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int) :
    Matrix (Fin n) (Fin n) BitCost.SignMagnitude :=
  fun row column => (matrixEntryWithCost left right row column).value

/-- Sum of the actual scalar reference costs for one dense matrix product. -/
@[expose] def matrixMultiplicationBitOperationCost {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int) : Nat :=
  ∑ row, ∑ column, (matrixEntryWithCost left right row column).cost

/-- Schoolbook bit-operation budget for one dense square matrix product. -/
@[expose] def matrixMultiplicationBitOperationBound
    (dimension leftBits rightBits : Nat) : Nat :=
  dimension ^ 3 *
    dotTermBitOperationBound dimension leftBits rightBits

theorem finRange_sum_eq_univ {n : Nat} (values : Fin n → Int) :
    (List.map values (List.finRange n)).sum = ∑ index, values index := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map,
        NormalForms.Matrix.Constructive.sum_univ_succ]
      rw [ih]
      simp [Function.comp_apply]

theorem matrixEntryWithCost_value {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int) (row column : Fin n) :
    (matrixEntryWithCost left right row column).value.value =
      (left * right) row column := by
  rw [matrixEntryWithCost, dotWithCost_value, finRange_sum_eq_univ]
  simp [Matrix.mul_apply]

theorem matrixProductWithCost_value {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int) (row column : Fin n) :
    (matrixProductWithCost left right row column).value =
      (left * right) row column :=
  matrixEntryWithCost_value left right row column

theorem matrixEntryWithCost_cost_le {n leftBits rightBits : Nat}
    (left right : Matrix (Fin n) (Fin n) Int)
    (leftBound : matrixBitLength left ≤ leftBits)
    (rightBound : matrixBitLength right ≤ rightBits)
    (row column : Fin n) :
    (matrixEntryWithCost left right row column).cost ≤
      n * dotTermBitOperationBound n leftBits rightBits := by
  unfold matrixEntryWithCost
  simpa only [List.length_finRange] using
    dotWithCost_cost_le (List.finRange n)
      (fun index => BitCost.SignMagnitude.ofInt (left row index))
      (fun index => BitCost.SignMagnitude.ofInt (right index column))
      n leftBits rightBits (by simp)
      (by
        intro index _member
        rw [BitCost.SignMagnitude.bitLength_eq_natSize_natAbs,
          BitCost.SignMagnitude.value_ofInt]
        exact (entry_bitLength_le_matrixBitLength left row index).trans
          leftBound)
      (by
        intro index _member
        rw [BitCost.SignMagnitude.bitLength_eq_natSize_natAbs,
          BitCost.SignMagnitude.value_ofInt]
        exact (entry_bitLength_le_matrixBitLength right index column).trans
          rightBound)

theorem matrixMultiplicationBitOperationCost_le {n leftBits rightBits : Nat}
    (left right : Matrix (Fin n) (Fin n) Int)
    (leftBound : matrixBitLength left ≤ leftBits)
    (rightBound : matrixBitLength right ≤ rightBits) :
    matrixMultiplicationBitOperationCost left right ≤
      matrixMultiplicationBitOperationBound n leftBits rightBits := by
  unfold matrixMultiplicationBitOperationCost
    matrixMultiplicationBitOperationBound
  calc
    (∑ row, ∑ column, (matrixEntryWithCost left right row column).cost) ≤
        ∑ _row : Fin n, ∑ _column : Fin n,
          n * dotTermBitOperationBound n leftBits rightBits := by
      apply Finset.sum_le_sum
      intro row _rowMember
      apply Finset.sum_le_sum
      intro column _columnMember
      exact matrixEntryWithCost_cost_le left right leftBound rightBound
        row column
    _ = n ^ 3 * dotTermBitOperationBound n leftBits rightBits := by
      simp [pow_succ]
      ring

theorem matrixMultiplicationBitOperationBound_mono
    (dimension : Nat) {leftSmall leftLarge rightSmall rightLarge : Nat}
    (leftLe : leftSmall ≤ leftLarge) (rightLe : rightSmall ≤ rightLarge) :
    matrixMultiplicationBitOperationBound dimension leftSmall rightSmall ≤
      matrixMultiplicationBitOperationBound dimension leftLarge rightLarge := by
  unfold matrixMultiplicationBitOperationBound dotTermBitOperationBound
    BitCost.multiplicationCostForBitLengths
    BitCost.additionCostForBitLengths
  gcongr

/-- Actual reference cost of the four products in strong-certificate composition. -/
@[expose] def certificateCompositionBitOperationCost {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (first : TwoSidedCertificate A)
    (second : TwoSidedCertificate first.result) : Nat :=
  matrixMultiplicationBitOperationCost second.U first.U +
    matrixMultiplicationBitOperationCost first.U_cert.inverse
      second.U_cert.inverse +
    matrixMultiplicationBitOperationCost first.V second.V +
    matrixMultiplicationBitOperationCost second.V_cert.inverse
      first.V_cert.inverse

/-- Width-only budget for all four products in certificate composition. -/
@[expose] def certificateCompositionBitOperationBound
    (dimension leftBits rightBits : Nat) : Nat :=
  2 * matrixMultiplicationBitOperationBound dimension leftBits rightBits +
    2 * matrixMultiplicationBitOperationBound dimension rightBits leftBits

theorem certificateCompositionBitOperationBound_mono
    (dimension : Nat) {leftSmall leftLarge rightSmall rightLarge : Nat}
    (leftLe : leftSmall ≤ leftLarge) (rightLe : rightSmall ≤ rightLarge) :
    certificateCompositionBitOperationBound dimension leftSmall rightSmall ≤
      certificateCompositionBitOperationBound dimension leftLarge rightLarge := by
  unfold certificateCompositionBitOperationBound
  exact Nat.add_le_add
    (Nat.mul_le_mul_left 2 <|
      matrixMultiplicationBitOperationBound_mono dimension leftLe rightLe)
    (Nat.mul_le_mul_left 2 <|
      matrixMultiplicationBitOperationBound_mono dimension rightLe leftLe)

theorem certificateCompositionBitOperationCost_le {n leftBits rightBits : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (first : TwoSidedCertificate A)
    (second : TwoSidedCertificate first.result)
    (firstBound : certificateTransformBitLength first ≤ leftBits)
    (secondBound : certificateTransformBitLength second ≤ rightBits) :
    certificateCompositionBitOperationCost first second ≤
      certificateCompositionBitOperationBound n leftBits rightBits := by
  have firstU : matrixBitLength first.U ≤ leftBits :=
    (le_max_left _ _).trans firstBound
  have firstUInv : matrixBitLength first.U_cert.inverse ≤ leftBits :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans firstBound
  have firstV : matrixBitLength first.V ≤ leftBits :=
    ((le_max_left _ _).trans <| (le_max_right _ _).trans
      (le_max_right _ _)).trans firstBound
  have firstVInv : matrixBitLength first.V_cert.inverse ≤ leftBits :=
    ((le_max_right _ _).trans <| (le_max_right _ _).trans
      (le_max_right _ _)).trans firstBound
  have secondU : matrixBitLength second.U ≤ rightBits :=
    (le_max_left _ _).trans secondBound
  have secondUInv : matrixBitLength second.U_cert.inverse ≤ rightBits :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans secondBound
  have secondV : matrixBitLength second.V ≤ rightBits :=
    ((le_max_left _ _).trans <| (le_max_right _ _).trans
      (le_max_right _ _)).trans secondBound
  have secondVInv : matrixBitLength second.V_cert.inverse ≤ rightBits :=
    ((le_max_right _ _).trans <| (le_max_right _ _).trans
      (le_max_right _ _)).trans secondBound
  have leftForward := matrixMultiplicationBitOperationCost_le
    second.U first.U secondU firstU
  have leftInverse := matrixMultiplicationBitOperationCost_le
    first.U_cert.inverse second.U_cert.inverse firstUInv secondUInv
  have rightForward := matrixMultiplicationBitOperationCost_le
    first.V second.V firstV secondV
  have rightInverse := matrixMultiplicationBitOperationCost_le
    second.V_cert.inverse first.V_cert.inverse secondVInv firstVInv
  unfold certificateCompositionBitOperationCost
    certificateCompositionBitOperationBound
  omega

theorem matrixBitLength_one_le {n : Nat} :
    matrixBitLength
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) ≤ 1 := by
  unfold matrixBitLength
  apply (Nat.size_le_size (matrixHeight_le (bound := 1) ?_)).trans
  · simp
  · intro row column
    exact show
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
        row column).natAbs ≤ 1 by
        rw [Matrix.one_apply]
        split <;> simp

/-- Common width budget for the two one-sided certificates in one pass. -/
@[expose] def passPhaseTransformBitLengthBound
    (order inputBits determinantBits : Nat) : Nat :=
  max 1 (passTransformBitLengthBound order inputBits determinantBits)

theorem pass_phase_transformBitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0) :
    let left := leftHermitePhase A
    let right := rightHermitePhase left.result
      (result_det_ne_zero left hdet)
    certificateTransformBitLength left ≤
        passPhaseTransformBitLengthBound n (matrixBitLength A)
          (integerBitLength A.det) ∧
      certificateTransformBitLength right ≤
        passPhaseTransformBitLengthBound n (matrixBitLength A)
          (integerBitLength A.det) := by
  let left := leftHermitePhase A
  let leftDet : left.result.det ≠ 0 := result_det_ne_zero left hdet
  let right := rightHermitePhase left.result leftDet
  let transformBits := passTransformBitLengthBound n
    (matrixBitLength A) (integerBitLength A.det)
  have passBound : certificateTransformBitLength (pass A hdet) ≤
      transformBits := pass_transformBitLength_le A hdet
  have oneBits : matrixBitLength
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) ≤
        max 1 transformBits :=
    matrixBitLength_one_le.trans (le_max_left _ _)
  have leftUBound : matrixBitLength left.U ≤ max 1 transformBits := by
    have component : matrixBitLength (pass A hdet).U ≤ transformBits :=
      (le_max_left _ _).trans passBound
    simpa [left, leftHermitePhase, pass, compose, rightHermitePhase,
      rightHermiteResult] using component.trans (le_max_right _ _)
  have leftInvBound : matrixBitLength left.U_cert.inverse ≤
      max 1 transformBits := by
    have component : matrixBitLength (pass A hdet).U_cert.inverse ≤
        transformBits :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans passBound
    simpa [left, leftHermitePhase, pass, compose, rightHermitePhase,
      rightHermiteResult, MatrixInverseCertificate.mul,
      MatrixInverseCertificate.one] using
        component.trans (le_max_right _ _)
  have leftCertificate : certificateTransformBitLength left ≤
      max 1 transformBits := by
    unfold certificateTransformBitLength
    apply max_le leftUBound
    apply max_le leftInvBound
    apply max_le
    · simpa [left, leftHermitePhase] using oneBits
    · simpa [left, leftHermitePhase,
        MatrixInverseCertificate.one] using oneBits
  have rightUBound : matrixBitLength right.V ≤ max 1 transformBits := by
    have component : matrixBitLength (pass A hdet).V ≤ transformBits :=
      ((le_max_left _ _).trans <| (le_max_right _ _).trans
        (le_max_right _ _)).trans passBound
    simpa [right, left, leftDet, pass, compose, leftHermitePhase] using
      component.trans (le_max_right _ _)
  have rightInvBound : matrixBitLength right.V_cert.inverse ≤
      max 1 transformBits := by
    have component : matrixBitLength (pass A hdet).V_cert.inverse ≤
        transformBits :=
      ((le_max_right _ _).trans <| (le_max_right _ _).trans
        (le_max_right _ _)).trans passBound
    simpa [right, left, leftDet, pass, compose, leftHermitePhase,
      MatrixInverseCertificate.mul, MatrixInverseCertificate.one] using
        component.trans (le_max_right _ _)
  have rightCertificate : certificateTransformBitLength right ≤
      max 1 transformBits := by
    unfold certificateTransformBitLength
    apply max_le
    · simpa [right, rightHermitePhase] using oneBits
    apply max_le
    · simpa [right, rightHermitePhase,
        MatrixInverseCertificate.one] using oneBits
    exact max_le rightUBound rightInvBound
  simpa [left, right, transformBits,
    passPhaseTransformBitLengthBound] using
      And.intro leftCertificate rightCertificate

/-- Actual Step-4 charge from its bounded-XGCD arithmetic event trace. -/
@[expose] def boundedColumnBitOperationCost {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Nat :=
  let operandBits := boundedColumnIntermediatePolynomialBitLengthBound
    (n + 1) (matrixBitLength A)
  arithmeticEventListBitOperationCost (n + 1) operandBits
    (boundedColumnArithmeticEvents A)

/-- Uniform Step-4 budget at one matrix dimension and input width. -/
@[expose] def boundedColumnBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  let operandBits :=
    boundedColumnIntermediatePolynomialBitLengthBound dimension inputBits
  dimension *
    Principal.principalTransitionBitOperationBound dimension operandBits

theorem inputBitLength_le_boundedColumnIntermediateBound
    (dimension inputBits : Nat) :
    inputBits ≤
      boundedColumnIntermediatePolynomialBitLengthBound dimension inputBits := by
  cases dimension with
  | zero => simp [boundedColumnIntermediatePolynomialBitLengthBound]
  | succ order =>
      simp only [boundedColumnIntermediatePolynomialBitLengthBound]
      omega

theorem boundedColumnBitOperationCost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    boundedColumnBitOperationCost A ≤
      boundedColumnBitOperationBound (n + 1) (matrixBitLength A) := by
  let operandBits := boundedColumnIntermediatePolynomialBitLengthBound
    (n + 1) (matrixBitLength A)
  have allWidths : ∀ event ∈ boundedColumnArithmeticEvents A,
      event.operandBitLength ≤ operandBits := by
    intro event member
    exact (event.operandBitLength_le_list_of_mem
      (boundedColumnArithmeticEvents A) member).trans <|
        (boundedColumnArithmeticOperandBitLength_le_input A).trans <|
          inputBitLength_le_boundedColumnIntermediateBound _ _
  have costBound := arithmeticEventListBitOperationCost_le
    (boundedColumnArithmeticEvents A) (n + 1) operandBits allWidths
  simpa [boundedColumnBitOperationCost, boundedColumnBitOperationBound,
    operandBits, boundedColumnArithmeticEvents_length] using costBound

theorem preparedPrincipalHNFBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    preparedPrincipalHNFBitOperationBound dimension smaller ≤
      preparedPrincipalHNFBitOperationBound dimension larger := by
  unfold preparedPrincipalHNFBitOperationBound
  exact Nat.add_le_add
    (Nat.mul_le_mul_left (dimension * dimension) <|
      Nat.add_le_add_right
        (DivisionFreeDeterminant.determinantBitOperationBound_mono_right
          dimension hle) 1)
    (principalHNFBitOperationBound_mono_right dimension hle)

/-- Actual division and row-arithmetic charge for one Step-6 clearing row. -/
@[expose] def clearRowBitOperationCost {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (row : Fin n) : Nat :=
  let inputBits := matrixBitLength A
  Principal.integerDivModBitOperationCost (A row.succ 0) (A 0 0) + 1 +
    (n + 1) *
      BitCost.multiplicationCostForBitLengths (inputBits + 1) inputBits +
    (n + 1) *
      BitCost.additionCostForBitLengths (2 * inputBits + 1) inputBits

/-- Actual Step-6 charge for clearing the divisible first column. -/
@[expose] def clearBitOperationCost {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Nat :=
  ∑ row : Fin n, clearRowBitOperationCost A row

/-- Uniform Step-6 clearing budget. -/
@[expose] def clearBitOperationBound (dimension inputBits : Nat) : Nat :=
  (dimension - 1) *
    (Principal.integerDivModBitOperationBound inputBits + 1 +
      dimension *
        BitCost.multiplicationCostForBitLengths (inputBits + 1) inputBits +
      dimension *
        BitCost.additionCostForBitLengths (2 * inputBits + 1) inputBits)

theorem clearBitOperationCost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    clearBitOperationCost A ≤
      clearBitOperationBound (n + 1) (matrixBitLength A) := by
  unfold clearBitOperationCost clearBitOperationBound
  simp only [Nat.add_sub_cancel]
  calc
    (∑ row : Fin n, clearRowBitOperationCost A row) ≤
        ∑ _row : Fin n,
          (Principal.integerDivModBitOperationBound (matrixBitLength A) + 1 +
              (n + 1) * BitCost.multiplicationCostForBitLengths
                (matrixBitLength A + 1) (matrixBitLength A) +
            (n + 1) * BitCost.additionCostForBitLengths
              (2 * matrixBitLength A + 1) (matrixBitLength A)) := by
      apply Finset.sum_le_sum
      intro row _member
      have numeratorWidth := entry_bitLength_le_matrixBitLength A row.succ 0
      have divisorWidth := entry_bitLength_le_matrixBitLength A 0 0
      unfold clearRowBitOperationCost
      exact Nat.add_le_add_right
        (Nat.add_le_add_right
          (Nat.add_le_add_right
            (Principal.integerDivModBitOperationCost_le
              (A row.succ 0) (A 0 0) (matrixBitLength A)
              numeratorWidth divisorWidth) 1) _) _
    _ = n *
        (Principal.integerDivModBitOperationBound (matrixBitLength A) + 1 +
            (n + 1) * BitCost.multiplicationCostForBitLengths
              (matrixBitLength A + 1) (matrixBitLength A) +
          (n + 1) * BitCost.additionCostForBitLengths
            (2 * matrixBitLength A + 1) (matrixBitLength A)) := by simp

/-- Actual Step-7 column-injection arithmetic charge. -/
@[expose] def injectionBitOperationCost {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Nat :=
  let inputBits := matrixBitLength A
  (n + 1) *
    (BitCost.multiplicationCostForBitLengths 1 inputBits +
      BitCost.additionCostForBitLengths inputBits (inputBits + 1))

/-- Uniform Step-7 injection budget. -/
@[expose] def injectionBitOperationBound (dimension inputBits : Nat) : Nat :=
  dimension *
    (BitCost.multiplicationCostForBitLengths 1 inputBits +
      BitCost.additionCostForBitLengths inputBits (inputBits + 1))

theorem injectionBitOperationCost_eq_bound {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    injectionBitOperationCost A =
      injectionBitOperationBound (n + 1) (matrixBitLength A) :=
  rfl

/-- Actual Step-4/Step-5 pass charge, including certificate composition. -/
@[expose] def passBitOperationCost {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) : Nat :=
  let left := leftHermitePhase A
  let leftDet := result_det_ne_zero left hdet
  let right := rightHermitePhase left.result leftDet
  boundedColumnBitOperationCost A +
    preparedPrincipalHNFBitOperationCost left.result.transpose
      (by simpa using leftDet) +
    certificateCompositionBitOperationCost left right

/-- Uniform bit-operation budget for one full pass. -/
@[expose] def passBitOperationBound
    (order inputBits determinantBits : Nat) : Nat :=
  let dimension := order + 1
  let leftBits := boundedColumnIntermediatePolynomialBitLengthBound
    dimension inputBits
  let transformBits := passPhaseTransformBitLengthBound
    order inputBits determinantBits
  boundedColumnBitOperationBound dimension inputBits +
    preparedPrincipalHNFBitOperationBound dimension leftBits +
    certificateCompositionBitOperationBound dimension
      transformBits transformBits

theorem passBitOperationCost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    passBitOperationCost A hdet ≤
      passBitOperationBound n (matrixBitLength A)
        (integerBitLength A.det) := by
  let left := leftHermitePhase A
  let leftDet := result_det_ne_zero left hdet
  let right := rightHermitePhase left.result leftDet
  have leftCost := boundedColumnBitOperationCost_le A
  have rightCost := preparedPrincipalHNFBitOperationCost_le
    left.result.transpose (by simpa using leftDet)
  have leftBits : matrixBitLength left.result.transpose ≤
      boundedColumnIntermediatePolynomialBitLengthBound
        (n + 1) (matrixBitLength A) := by
    rw [matrixBitLength_transpose]
    exact leftHermitePhase_result_bitLength_le A
  have rightUniform := rightCost.trans <|
    preparedPrincipalHNFBitOperationBound_mono_right (n + 1) leftBits
  have phaseBounds := pass_phase_transformBitLength_le A hdet
  have compositionCost : certificateCompositionBitOperationCost left right ≤
      certificateCompositionBitOperationBound (n + 1)
        (passPhaseTransformBitLengthBound n (matrixBitLength A)
          (integerBitLength A.det))
        (passPhaseTransformBitLengthBound n (matrixBitLength A)
          (integerBitLength A.det)) := by
    apply certificateCompositionBitOperationCost_le
    · simpa [left] using phaseBounds.1
    · simpa [left, right, leftDet] using phaseBounds.2
  unfold passBitOperationCost passBitOperationBound
  dsimp only
  exact Nat.add_le_add (Nat.add_le_add leftCost rightUniform) compositionCost

theorem boundedColumnIntermediateBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    boundedColumnIntermediatePolynomialBitLengthBound dimension smaller ≤
      boundedColumnIntermediatePolynomialBitLengthBound dimension larger := by
  cases dimension with
  | zero =>
      simp only [boundedColumnIntermediatePolynomialBitLengthBound]
      omega
  | succ order =>
      simp only [boundedColumnIntermediatePolynomialBitLengthBound]
      have factorLe :
          Nat.size (order + 1) + 2 * (smaller + 1) + 6 ≤
            Nat.size (order + 1) + 2 * (larger + 1) + 6 := by
        omega
      exact Nat.add_le_add_right
        (Nat.add_le_add hle (Nat.mul_le_mul_left order factorLe)) 1

theorem boundedColumnBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    boundedColumnBitOperationBound dimension smaller ≤
      boundedColumnBitOperationBound dimension larger := by
  unfold boundedColumnBitOperationBound
  exact Nat.mul_le_mul_left dimension <|
    Principal.principalTransitionBitOperationBound_mono_right dimension
      (boundedColumnIntermediateBound_mono_right dimension hle)

theorem passBitOperationBound_mono
    (order : Nat) {inputSmall inputLarge detSmall detLarge : Nat}
    (inputLe : inputSmall ≤ inputLarge) (detLe : detSmall ≤ detLarge) :
    passBitOperationBound order inputSmall detSmall ≤
      passBitOperationBound order inputLarge detLarge := by
  unfold passBitOperationBound
  dsimp only
  have leftBitsLe := boundedColumnIntermediateBound_mono_right
    (order + 1) inputLe
  have transformLe :
      passPhaseTransformBitLengthBound order inputSmall detSmall ≤
        passPhaseTransformBitLengthBound order inputLarge detLarge := by
    unfold passPhaseTransformBitLengthBound
    exact max_le (le_max_left _ _) <|
      (passTransformBitLengthBound_mono
        (order := order) inputLe detLe).trans (le_max_right _ _)
  exact Nat.add_le_add
    (Nat.add_le_add
      (boundedColumnBitOperationBound_mono_right (order + 1) inputLe)
      (preparedPrincipalHNFBitOperationBound_mono_right
        (order + 1) leftBitsLe))
    (certificateCompositionBitOperationBound_mono
      (order + 1) transformLe transformLe)

theorem clearBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    clearBitOperationBound dimension smaller ≤
      clearBitOperationBound dimension larger := by
  unfold clearBitOperationBound Principal.integerDivModBitOperationBound
    BitCost.divisionCostForBitLengths
    BitCost.multiplicationCostForBitLengths
    BitCost.additionCostForBitLengths
  gcongr

theorem injectionBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    injectionBitOperationBound dimension smaller ≤
      injectionBitOperationBound dimension larger := by
  unfold injectionBitOperationBound
    BitCost.multiplicationCostForBitLengths
    BitCost.additionCostForBitLengths
  gcongr

/-- Exact branch-recursive arithmetic charge mirroring `stabilizeFrom`. -/
@[expose] def stabilizeFromBitOperationCost {n : Nat} :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) →
      A.det ≠ 0 → A 0 0 ≠ 0 →
        A 0 0 = normalize (A 0 0) → FirstRowCleared A → Nat
  | A, hdet, _hpivot, _hnormalized, hrow =>
      match hbadColumn : firstUndivisibleBelow? A with
      | some _row =>
          let current := pass A hdet
          let shape := pass_shape A hdet
          let next := stabilizeFrom current.result
            (pass_result_det_ne_zero A hdet) shape.1 shape.2.1 shape.2.2
          passBitOperationCost A hdet +
            stabilizeFromBitOperationCost current.result
              (pass_result_det_ne_zero A hdet) shape.1 shape.2.1 shape.2.2 +
            certificateCompositionBitOperationCost current next.certificate
      | none =>
          let hdiv := firstUndivisibleBelow?_eq_none A hbadColumn
          let cleared := clearDivisibleFirstColumn A
          let _hclearedColumn :=
            clearDivisibleFirstColumn_firstColumnCleared A hdiv
          let _hclearedRow :=
            clearDivisibleFirstColumn_firstRowCleared A hrow
          match _hbadLower : firstUndivisibleLower? cleared.result with
          | none => clearBitOperationCost A
          | some position =>
              let injection := injectLowerWitness cleared.result position.2
              let accumulated := compose cleared injection
              let accumulatedDet := result_det_ne_zero accumulated hdet
              let current := pass accumulated.result accumulatedDet
              let shape := pass_shape accumulated.result accumulatedDet
              let next := stabilizeFrom current.result
                (pass_result_det_ne_zero accumulated.result accumulatedDet)
                shape.1 shape.2.1 shape.2.2
              clearBitOperationCost A +
                injectionBitOperationCost cleared.result +
                certificateCompositionBitOperationCost cleared injection +
                passBitOperationCost accumulated.result accumulatedDet +
                stabilizeFromBitOperationCost current.result
                  (pass_result_det_ne_zero accumulated.result accumulatedDet)
                  shape.1 shape.2.1 shape.2.2 +
                certificateCompositionBitOperationCost current
                  next.certificate +
                certificateCompositionBitOperationCost accumulated
                  (compose current next.certificate)
termination_by A _ _ _ _ => (A 0 0).natAbs.size
decreasing_by
  · exact pass_pivot_natSize_lt_of_not_dvd_entry A hdet _hpivot _row.succ
      (firstUndivisibleBelow?_some_not_dvd A hbadColumn)
  · have accumulatedPivot : accumulated.result 0 0 = A 0 0 := by
      exact (injectLowerWitness_pivot cleared.result position.2
        _hclearedRow).trans (clearDivisibleFirstColumn_pivot A)
    have target : accumulated.result position.1.succ 0 =
        cleared.result position.1.succ position.2.succ :=
      injectLowerWitness_target cleared.result position.1 position.2
        _hclearedColumn
    have hnot : ¬ accumulated.result 0 0 ∣
        accumulated.result position.1.succ 0 := by
      rw [accumulatedPivot, target]
      have original := firstUndivisibleLower?_some_not_dvd
        cleared.result _hbadLower
      rw [← show cleared.result 0 0 = A 0 0 by
        exact clearDivisibleFirstColumn_pivot A]
      exact original
    have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
      accumulated.result accumulatedDet
      (by simpa [accumulatedPivot] using _hpivot) position.1.succ hnot
    simpa [accumulatedPivot] using decrease

/-- End-to-end arithmetic charge for total pivot stabilization. -/
@[expose] def stabilizeBitOperationCost {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) : Nat :=
  let initial := pass A hdet
  let shape := pass_shape A hdet
  let rest := stabilizeFrom initial.result
    (pass_result_det_ne_zero A hdet) shape.1 shape.2.1 shape.2.2
  passBitOperationCost A hdet +
    stabilizeFromBitOperationCost initial.result
      (pass_result_det_ne_zero A hdet) shape.1 shape.2.1 shape.2.2 +
    certificateCompositionBitOperationCost initial rest.certificate

/-- Uniform charge for one stabilization certificate composition. -/
@[expose] def stabilizationCompositionBitOperationBound
    (dimension workBits : Nat) : Nat :=
  let transformBits := stabilizationTransformWorkBound dimension workBits
  certificateCompositionBitOperationBound dimension
    transformBits transformBits

/-- Uniform charge for one pivot-size descent level. -/
@[expose] def stabilizationLevelBitOperationBound
    (dimension workBits : Nat) : Nat :=
  passBitOperationBound (dimension - 1) (workBits + 1) workBits +
    clearBitOperationBound dimension workBits +
    injectionBitOperationBound dimension workBits +
    3 * stabilizationCompositionBitOperationBound dimension workBits

/-- Closed stabilization budget over all possible pivot-size descents. -/
@[expose] def stabilizationBitOperationBound
    (dimension workBits : Nat) : Nat :=
  (workBits + 1) * stabilizationLevelBitOperationBound dimension workBits

theorem stabilizationFactor_le_transformWorkBound
    (order workBits : Nat) :
    stabilizationFactorBitLengthBound order workBits ≤
      stabilizationTransformWorkBound (order + 1) workBits := by
  let factor := stabilizationFactorBitLengthBound order workBits
  let composition := stabilizationCompositionBitLength order workBits
  have factorLe : factor ≤ composition := by
    simp only [factor, composition, stabilizationCompositionBitLength]
    omega
  have coefficient : 1 ≤ 3 * workBits + 2 := by omega
  unfold stabilizationTransformWorkBound
  simp only [Nat.add_sub_cancel]
  exact factorLe.trans <| by
    simpa only [one_mul] using
      Nat.mul_le_mul_right composition coefficient

theorem stabilizationTwoFactors_le_transformWorkBound
    (order workBits : Nat) :
    Nat.size (order + 1) +
        stabilizationFactorBitLengthBound order workBits +
        stabilizationFactorBitLengthBound order workBits ≤
      stabilizationTransformWorkBound (order + 1) workBits := by
  let factor := stabilizationFactorBitLengthBound order workBits
  let composition := stabilizationCompositionBitLength order workBits
  have pairLe : Nat.size (order + 1) + factor + factor ≤
      2 * composition := by
    simp only [composition, stabilizationCompositionBitLength]
    omega
  unfold stabilizationTransformWorkBound
  simp only [Nat.add_sub_cancel]
  exact pairLe.trans <| Nat.mul_le_mul_right composition (by omega)

theorem stabilizationContinuation_le_transformWorkBound
    (order workBits pivotBits : Nat) (pivotLe : pivotBits ≤ workBits) :
    (3 * pivotBits + 1) *
        stabilizationCompositionBitLength order workBits ≤
      stabilizationTransformWorkBound (order + 1) workBits := by
  unfold stabilizationTransformWorkBound
  simp only [Nat.add_sub_cancel]
  exact Nat.mul_le_mul_right _ (by omega)

theorem stabilizationFactorThenContinuation_le_transformWorkBound
    (order workBits pivotBits : Nat) (pivotLe : pivotBits ≤ workBits) :
    Nat.size (order + 1) +
        stabilizationFactorBitLengthBound order workBits +
        (3 * pivotBits + 1) *
          stabilizationCompositionBitLength order workBits ≤
      stabilizationTransformWorkBound (order + 1) workBits := by
  unfold stabilizationTransformWorkBound
    stabilizationCompositionBitLength
  simp only [Nat.add_sub_cancel]
  rw [show Nat.size (order + 1) +
      stabilizationFactorBitLengthBound order workBits +
      (3 * pivotBits + 1) *
        (Nat.size (order + 1) +
          stabilizationFactorBitLengthBound order workBits) =
      (3 * pivotBits + 2) *
        (Nat.size (order + 1) +
          stabilizationFactorBitLengthBound order workBits) by ring]
  exact Nat.mul_le_mul_right _ (by omega)

theorem passBitOperationCost_le_uniform {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0)
    (matrixBound : matrixBitLength A ≤ workBits + 1)
    (detBound : integerBitLength A.det ≤ workBits) :
    passBitOperationCost A hdet ≤
      passBitOperationBound n (workBits + 1) workBits :=
  (passBitOperationCost_le A hdet).trans <|
    passBitOperationBound_mono n matrixBound detBound

theorem clearBitOperationCost_le_uniform {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (matrixBound : matrixBitLength A ≤ workBits) :
    clearBitOperationCost A ≤ clearBitOperationBound (n + 1) workBits :=
  (clearBitOperationCost_le A).trans <|
    clearBitOperationBound_mono_right (n + 1) matrixBound

theorem injectionBitOperationCost_le_uniform {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (matrixBound : matrixBitLength A ≤ workBits) :
    injectionBitOperationCost A ≤
      injectionBitOperationBound (n + 1) workBits := by
  rw [injectionBitOperationCost_eq_bound]
  exact injectionBitOperationBound_mono_right (n + 1) matrixBound

theorem certificateCompositionBitOperationCost_le_uniform
    {dimension workBits : Nat}
    {A : Matrix (Fin dimension) (Fin dimension) Int}
    (first : TwoSidedCertificate A)
    (second : TwoSidedCertificate first.result)
    (leftBound : certificateTransformBitLength first ≤
      stabilizationTransformWorkBound dimension workBits)
    (rightBound : certificateTransformBitLength second ≤
      stabilizationTransformWorkBound dimension workBits) :
    certificateCompositionBitOperationCost first second ≤
      stabilizationCompositionBitOperationBound dimension workBits := by
  unfold stabilizationCompositionBitOperationBound
  exact certificateCompositionBitOperationCost_le first second
    leftBound rightBound

theorem stabilizeFromBitOperationCost_le {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = normalize (A 0 0))
    (hrow : FirstRowCleared A)
    (matrixBound : matrixBitLength A ≤ workBits)
    (detBound : integerBitLength A.det ≤ workBits) :
    stabilizeFromBitOperationCost A hdet hpivot hnormalized hrow ≤
      (A 0 0).natAbs.size *
        stabilizationLevelBitOperationBound (n + 1) workBits := by
  generalize measureEq : (A 0 0).natAbs.size = measure
  induction measure using Nat.strong_induction_on generalizing A with
  | h measure ih =>
      rw [stabilizeFromBitOperationCost.eq_1]
      split
      next row hbadColumn =>
        dsimp only
        let current := pass A hdet
        let next := stabilizeFrom current.result
          (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
          (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
        have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
          A hdet hpivot row.succ
            (firstUndivisibleBelow?_some_not_dvd A hbadColumn)
        have decreaseMeasure :
            (current.result 0 0).natAbs.size < measure := by
          simpa [current, measureEq] using decrease
        have currentMatrixBound : matrixBitLength current.result ≤ workBits :=
          (pass_result_bitLength_le_determinant A hdet).trans detBound
        have currentDetBits :
            integerBitLength current.result.det = integerBitLength A.det :=
          congrArg Nat.size (certificate_result_det_natAbs current)
        have nextCost := ih _ decreaseMeasure current.result
          (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
          (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
          currentMatrixBound (currentDetBits ▸ detBound) rfl
        have passCost := passBitOperationCost_le_uniform A hdet
          (matrixBound.trans (by omega)) detBound
        have currentTransform : certificateTransformBitLength current ≤
            stabilizationTransformWorkBound (n + 1) workBits :=
          (pass_transformBitLength_le_uniform A hdet
            (matrixBound.trans (by omega)) detBound).trans <|
              stabilizationFactor_le_transformWorkBound n workBits
        have currentPivotBound :
            (current.result 0 0).natAbs.size ≤ workBits :=
          (entry_bitLength_le_matrixBitLength current.result 0 0).trans
            currentMatrixBound
        have nextTransformRaw := stabilizeFrom_transformBitLength_le
          current.result (pass_result_det_ne_zero A hdet)
          (pass_shape A hdet).1 (pass_shape A hdet).2.1
          (pass_shape A hdet).2.2 currentMatrixBound
          (currentDetBits ▸ detBound)
        have nextTransform : certificateTransformBitLength next.certificate ≤
            stabilizationTransformWorkBound (n + 1) workBits :=
          nextTransformRaw.trans <|
            stabilizationContinuation_le_transformWorkBound
              n workBits _ currentPivotBound
        have compositionCost :=
          certificateCompositionBitOperationCost_le_uniform
            current next.certificate currentTransform nextTransform
        let level := stabilizationLevelBitOperationBound (n + 1) workBits
        calc
          passBitOperationCost A hdet +
                stabilizeFromBitOperationCost current.result
                  (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
                  (pass_shape A hdet).2.1 (pass_shape A hdet).2.2 +
                certificateCompositionBitOperationCost current
                  next.certificate ≤
              passBitOperationBound n (workBits + 1) workBits +
                (current.result 0 0).natAbs.size * level +
                stabilizationCompositionBitOperationBound
                  (n + 1) workBits :=
            Nat.add_le_add
              (Nat.add_le_add passCost nextCost) compositionCost
          _ ≤ level + (current.result 0 0).natAbs.size * level := by
            unfold level stabilizationLevelBitOperationBound
            simp only [Nat.add_sub_cancel]
            omega
          _ = ((current.result 0 0).natAbs.size + 1) * level := by ring
          _ ≤ measure * level := by
            exact Nat.mul_le_mul_right _
              (Nat.succ_le_iff.mpr decreaseMeasure)
      next hnoBadColumn =>
        dsimp only
        split
        next _hnoBadLower =>
          have clearCost := clearBitOperationCost_le_uniform A matrixBound
          have measurePos : 0 < measure := by
            rw [← measureEq, Nat.size_pos]
            exact Int.natAbs_pos.mpr hpivot
          let level := stabilizationLevelBitOperationBound (n + 1) workBits
          calc
            clearBitOperationCost A ≤
                clearBitOperationBound (n + 1) workBits := clearCost
            _ ≤ level := by
              unfold level stabilizationLevelBitOperationBound
              omega
            _ = 1 * level := by simp
            _ ≤ measure * level := Nat.mul_le_mul_right _ measurePos
        next position hbadLower =>
          let cleared := clearDivisibleFirstColumn A
          let hdiv := firstUndivisibleBelow?_eq_none A hnoBadColumn
          let hclearedColumn :=
            clearDivisibleFirstColumn_firstColumnCleared A hdiv
          let hclearedRow :=
            clearDivisibleFirstColumn_firstRowCleared A hrow
          let injection := injectLowerWitness cleared.result position.2
          let accumulated := compose cleared injection
          let accumulatedDet := result_det_ne_zero accumulated hdet
          let current := pass accumulated.result accumulatedDet
          let next := stabilizeFrom current.result
            (pass_result_det_ne_zero accumulated.result accumulatedDet)
            (pass_shape accumulated.result accumulatedDet).1
            (pass_shape accumulated.result accumulatedDet).2.1
            (pass_shape accumulated.result accumulatedDet).2.2
          have accumulatedPivot : accumulated.result 0 0 = A 0 0 := by
            exact (injectLowerWitness_pivot cleared.result position.2
              hclearedRow).trans (clearDivisibleFirstColumn_pivot A)
          have target : accumulated.result position.1.succ 0 =
              cleared.result position.1.succ position.2.succ :=
            injectLowerWitness_target cleared.result position.1 position.2
              hclearedColumn
          have hnot : ¬ accumulated.result 0 0 ∣
              accumulated.result position.1.succ 0 := by
            rw [accumulatedPivot, target]
            have original := firstUndivisibleLower?_some_not_dvd
              cleared.result hbadLower
            rw [← show cleared.result 0 0 = A 0 0 by
              exact clearDivisibleFirstColumn_pivot A]
            exact original
          have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
            accumulated.result accumulatedDet
            (by simpa [accumulatedPivot] using hpivot) position.1.succ hnot
          have decreaseMeasure :
              (current.result 0 0).natAbs.size < measure := by
            simpa [current, accumulatedPivot, measureEq] using decrease
          have clearedHeight := clear_result_height_le A hrow hdiv
          have clearedMatrixBound :
              matrixBitLength cleared.result ≤ workBits :=
            (Nat.size_le_size clearedHeight).trans matrixBound
          have injectionMatrixBound :
              matrixBitLength injection.result ≤ workBits + 1 :=
            (injection_result_bitLength_le cleared.result position.2).trans <| by
              omega
          have accumulatedResult : accumulated.result = injection.result := rfl
          have accumulatedDetBits :
              integerBitLength accumulated.result.det = integerBitLength A.det :=
            congrArg Nat.size (certificate_result_det_natAbs accumulated)
          have currentMatrixBound : matrixBitLength current.result ≤ workBits :=
            (pass_result_bitLength_le_determinant
              accumulated.result accumulatedDet).trans <| by
                rw [accumulatedDetBits]
                exact detBound
          have currentDetBits :
              integerBitLength current.result.det = integerBitLength A.det := by
            rw [show integerBitLength current.result.det =
                integerBitLength accumulated.result.det from
              congrArg Nat.size (certificate_result_det_natAbs current)]
            exact accumulatedDetBits
          have nextCost := ih _ decreaseMeasure current.result
            (pass_result_det_ne_zero accumulated.result accumulatedDet)
            (pass_shape accumulated.result accumulatedDet).1
            (pass_shape accumulated.result accumulatedDet).2.1
            (pass_shape accumulated.result accumulatedDet).2.2
            currentMatrixBound (currentDetBits ▸ detBound) rfl
          have clearCost := clearBitOperationCost_le_uniform A matrixBound
          have injectionCost := injectionBitOperationCost_le_uniform
            cleared.result clearedMatrixBound
          have passCost := passBitOperationCost_le_uniform
            accumulated.result accumulatedDet
            (by simpa [accumulatedResult] using injectionMatrixBound) <| by
              rw [accumulatedDetBits]
              exact detBound
          have clearTransform : certificateTransformBitLength cleared ≤
              stabilizationTransformWorkBound (n + 1) workBits :=
            (clear_transformBitLength_le_uniform A matrixBound).trans <|
              stabilizationFactor_le_transformWorkBound n workBits
          have injectionTransform : certificateTransformBitLength injection ≤
              stabilizationTransformWorkBound (n + 1) workBits :=
            (injection_transformBitLength_le_uniform
              cleared.result position.2).trans <|
                stabilizationFactor_le_transformWorkBound n workBits
          have accumulatedRaw := compose_transformBitLength_le
            cleared injection
          have accumulatedTransform :
              certificateTransformBitLength accumulated ≤
                stabilizationTransformWorkBound (n + 1) workBits :=
            accumulatedRaw.trans <| by
              apply (Nat.add_le_add
                (Nat.add_le_add_left
                  (clear_transformBitLength_le_uniform A matrixBound) _)
                (injection_transformBitLength_le_uniform
                  cleared.result position.2)).trans
              exact stabilizationTwoFactors_le_transformWorkBound n workBits
          have currentTransform : certificateTransformBitLength current ≤
              stabilizationTransformWorkBound (n + 1) workBits :=
            (pass_transformBitLength_le_uniform accumulated.result
              accumulatedDet
              (by simpa [accumulatedResult] using injectionMatrixBound) <| by
                rw [accumulatedDetBits]
                exact detBound).trans <|
              stabilizationFactor_le_transformWorkBound n workBits
          have currentPivotBound :
              (current.result 0 0).natAbs.size ≤ workBits :=
            (entry_bitLength_le_matrixBitLength current.result 0 0).trans
              currentMatrixBound
          have nextTransformRaw := stabilizeFrom_transformBitLength_le
            current.result
            (pass_result_det_ne_zero accumulated.result accumulatedDet)
            (pass_shape accumulated.result accumulatedDet).1
            (pass_shape accumulated.result accumulatedDet).2.1
            (pass_shape accumulated.result accumulatedDet).2.2
            currentMatrixBound (currentDetBits ▸ detBound)
          have nextTransform : certificateTransformBitLength next.certificate ≤
              stabilizationTransformWorkBound (n + 1) workBits :=
            nextTransformRaw.trans <|
              stabilizationContinuation_le_transformWorkBound
                n workBits _ currentPivotBound
          have innerRaw := compose_transformBitLength_le
            current next.certificate
          have innerTransform :
              certificateTransformBitLength
                  (compose current next.certificate) ≤
                stabilizationTransformWorkBound (n + 1) workBits :=
            innerRaw.trans <| by
              apply (Nat.add_le_add
                (Nat.add_le_add_left
                  (pass_transformBitLength_le_uniform accumulated.result
                    accumulatedDet
                    (by simpa [accumulatedResult] using injectionMatrixBound) <| by
                      rw [accumulatedDetBits]
                      exact detBound) _)
                nextTransformRaw).trans
              exact stabilizationFactorThenContinuation_le_transformWorkBound
                n workBits _ currentPivotBound
          have firstCompositionCost :=
            certificateCompositionBitOperationCost_le_uniform
              cleared injection clearTransform injectionTransform
          have secondCompositionCost :=
            certificateCompositionBitOperationCost_le_uniform
              current next.certificate currentTransform nextTransform
          have thirdCompositionCost :=
            certificateCompositionBitOperationCost_le_uniform
              accumulated (compose current next.certificate)
                accumulatedTransform innerTransform
          let level := stabilizationLevelBitOperationBound (n + 1) workBits
          calc
            clearBitOperationCost A +
                  injectionBitOperationCost cleared.result +
                  certificateCompositionBitOperationCost cleared injection +
                  passBitOperationCost accumulated.result accumulatedDet +
                  stabilizeFromBitOperationCost current.result
                    (pass_result_det_ne_zero accumulated.result accumulatedDet)
                    (pass_shape accumulated.result accumulatedDet).1
                    (pass_shape accumulated.result accumulatedDet).2.1
                    (pass_shape accumulated.result accumulatedDet).2.2 +
                  certificateCompositionBitOperationCost current
                    next.certificate +
                  certificateCompositionBitOperationCost accumulated
                    (compose current next.certificate) ≤
                clearBitOperationBound (n + 1) workBits +
                  injectionBitOperationBound (n + 1) workBits +
                  stabilizationCompositionBitOperationBound
                    (n + 1) workBits +
                  passBitOperationBound n (workBits + 1) workBits +
                  (current.result 0 0).natAbs.size * level +
                  stabilizationCompositionBitOperationBound
                    (n + 1) workBits +
                  stabilizationCompositionBitOperationBound
                    (n + 1) workBits := by
              exact Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add
                    (Nat.add_le_add
                      (Nat.add_le_add
                        (Nat.add_le_add clearCost injectionCost)
                        firstCompositionCost)
                      passCost)
                    nextCost)
                  secondCompositionCost)
                thirdCompositionCost
            _ ≤ level + (current.result 0 0).natAbs.size * level := by
              unfold level stabilizationLevelBitOperationBound
              simp only [Nat.add_sub_cancel]
              omega
            _ = ((current.result 0 0).natAbs.size + 1) * level := by ring
            _ ≤ measure * level := by
              exact Nat.mul_le_mul_right _
                (Nat.succ_le_iff.mpr decreaseMeasure)

theorem stabilizeBitOperationCost_le_work {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0)
    (matrixBound : matrixBitLength A ≤ workBits)
    (detBound : integerBitLength A.det ≤ workBits) :
    stabilizeBitOperationCost A hdet ≤
      stabilizationBitOperationBound (n + 1) workBits := by
  let initial := pass A hdet
  let rest := stabilizeFrom initial.result
    (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
    (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
  have initialMatrixBound : matrixBitLength initial.result ≤ workBits :=
    (pass_result_bitLength_le_determinant A hdet).trans detBound
  have initialDetBits :
      integerBitLength initial.result.det = integerBitLength A.det :=
    congrArg Nat.size (certificate_result_det_natAbs initial)
  have initialCost := passBitOperationCost_le_uniform A hdet
    (matrixBound.trans (by omega)) detBound
  have restCost := stabilizeFromBitOperationCost_le initial.result
    (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
    (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
    initialMatrixBound (initialDetBits ▸ detBound)
  have initialTransform : certificateTransformBitLength initial ≤
      stabilizationTransformWorkBound (n + 1) workBits :=
    (pass_transformBitLength_le_uniform A hdet
      (matrixBound.trans (by omega)) detBound).trans <|
        stabilizationFactor_le_transformWorkBound n workBits
  have initialPivotBound :
      (initial.result 0 0).natAbs.size ≤ workBits :=
    (entry_bitLength_le_matrixBitLength initial.result 0 0).trans
      initialMatrixBound
  have restTransformRaw := stabilizeFrom_transformBitLength_le initial.result
    (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
    (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
    initialMatrixBound (initialDetBits ▸ detBound)
  have restTransform : certificateTransformBitLength rest.certificate ≤
      stabilizationTransformWorkBound (n + 1) workBits :=
    restTransformRaw.trans <|
      stabilizationContinuation_le_transformWorkBound
        n workBits _ initialPivotBound
  have compositionCost :=
    certificateCompositionBitOperationCost_le_uniform
      initial rest.certificate initialTransform restTransform
  let level := stabilizationLevelBitOperationBound (n + 1) workBits
  unfold stabilizeBitOperationCost stabilizationBitOperationBound
  dsimp only
  calc
    passBitOperationCost A hdet +
          stabilizeFromBitOperationCost initial.result
            (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
            (pass_shape A hdet).2.1 (pass_shape A hdet).2.2 +
          certificateCompositionBitOperationCost initial rest.certificate ≤
        passBitOperationBound n (workBits + 1) workBits +
          (initial.result 0 0).natAbs.size * level +
          stabilizationCompositionBitOperationBound (n + 1) workBits :=
      Nat.add_le_add (Nat.add_le_add initialCost restCost) compositionCost
    _ ≤ level + workBits * level := by
      have pivotProduct := Nat.mul_le_mul_right level initialPivotBound
      have fixedCost :
          passBitOperationBound n (workBits + 1) workBits +
              stabilizationCompositionBitOperationBound (n + 1) workBits ≤
            level := by
        unfold level stabilizationLevelBitOperationBound
        simp only [Nat.add_sub_cancel]
        omega
      omega
    _ = (workBits + 1) * level := by ring

/-- Input-size stabilization budget. -/
@[expose] def stabilizationPolynomialBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  stabilizationBitOperationBound dimension
    (smithCoefficientWorkBitLength dimension inputBits)

theorem stabilizeBitOperationCost_le_polynomial {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    stabilizeBitOperationCost A hdet ≤
      stabilizationPolynomialBitOperationBound
        (n + 1) (matrixBitLength A) := by
  apply stabilizeBitOperationCost_le_work A hdet
  · exact le_max_left _ _
  · exact (determinant_bitLength_le A).trans (le_max_right _ _)

/-- Exact arithmetic charge following the structural recursion of `smith`. -/
@[expose] def smithBitOperationCost : {n : Nat} →
    (A : Matrix (Fin n) (Fin n) Int) → A.det ≠ 0 → Nat
  | 0, _A, _hdet => 0
  | _n + 1, A, hdet =>
      let stabilized := stabilize A hdet
      let transformed := stabilized.certificate.result
      let transformedDet : transformed.det ≠ 0 :=
        stabilized.result_det_ne_zero hdet
      let lowerDet : (lowerRight transformed).det ≠ 0 :=
        stable_lowerRight_det_ne_zero transformed stabilized.stable
          transformedDet
      let lower := smith (lowerRight transformed) lowerDet
      let lifted := liftLowerCertificate transformed stabilized.stable
        (snfCertificate lower)
      stabilizeBitOperationCost A hdet +
        smithBitOperationCost (lowerRight transformed) lowerDet +
        certificateCompositionBitOperationCost stabilized.certificate lifted

/-- Closed recursive budget shared by all Smith levels. -/
@[expose] def smithBitOperationWorkBound : Nat → Nat → Nat
  | 0, _workBits => 0
  | dimension + 1, workBits =>
      stabilizationBitOperationBound (dimension + 1) workBits +
        smithBitOperationWorkBound dimension workBits +
        certificateCompositionBitOperationBound (dimension + 1)
          (stabilizationTransformWorkBound (dimension + 1) workBits)
          (max 1 (smithTransformWorkBound dimension workBits))

theorem smithBitOperationCost_le_work {n workBits : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0)
    (matrixBound : matrixBitLength A ≤ workBits)
    (detBound : integerBitLength A.det ≤ workBits) :
    smithBitOperationCost A hdet ≤
      smithBitOperationWorkBound n workBits := by
  induction n with
  | zero =>
      simp [smithBitOperationCost, smithBitOperationWorkBound]
  | succ n ih =>
      let stabilized := stabilize A hdet
      let transformed := stabilized.certificate.result
      let transformedDet : transformed.det ≠ 0 :=
        stabilized.result_det_ne_zero hdet
      let lowerDet : (lowerRight transformed).det ≠ 0 :=
        stable_lowerRight_det_ne_zero transformed stabilized.stable
          transformedDet
      let lower := smith (lowerRight transformed) lowerDet
      let lifted := liftLowerCertificate transformed stabilized.stable
        (snfCertificate lower)
      have stabilizationCost : stabilizeBitOperationCost A hdet ≤
          stabilizationBitOperationBound (n + 1) workBits :=
        stabilizeBitOperationCost_le_work A hdet matrixBound detBound
      have transformedMatrixBound : matrixBitLength transformed ≤ workBits :=
        (stabilize_result_bitLength_le_determinant A hdet).trans detBound
      have lowerMatrixBound :
          matrixBitLength (lowerRight transformed) ≤ workBits :=
        (lowerRight_bitLength_le transformed).trans transformedMatrixBound
      have lowerDetBound :
          integerBitLength (lowerRight transformed).det ≤ workBits :=
        (Nat.size_le_size (stabilization_lowerRight_det_natAbs_le A hdet)).trans
          detBound
      have recursiveCost :
          smithBitOperationCost (lowerRight transformed) lowerDet ≤
            smithBitOperationWorkBound n workBits :=
        ih (lowerRight transformed) lowerDet lowerMatrixBound lowerDetBound
      have stabilizedTransform :
          certificateTransformBitLength stabilized.certificate ≤
            stabilizationTransformWorkBound (n + 1) workBits :=
        stabilize_transformBitLength_le_work A hdet matrixBound detBound
      have recursiveTransform : smithTransformBitLength lower ≤
          smithTransformWorkBound n workBits :=
        smith_transformBitLength_le_work (lowerRight transformed) lowerDet
          lowerMatrixBound lowerDetBound
      have liftedTransform : certificateTransformBitLength lifted ≤
          max 1 (smithTransformWorkBound n workBits) :=
        (liftLowerCertificate_transformBitLength_le transformed
          stabilized.stable (snfCertificate lower)).trans <| by
            exact max_le (le_max_left _ _) <|
              recursiveTransform.trans (le_max_right _ _)
      have compositionCost := certificateCompositionBitOperationCost_le
        stabilized.certificate lifted stabilizedTransform liftedTransform
      rw [smithBitOperationCost, smithBitOperationWorkBound]
      exact Nat.add_le_add
        (Nat.add_le_add stabilizationCost recursiveCost) compositionCost

/-- Full SNF bit-operation budget in the original dimension and input width. -/
@[expose] def smithPolynomialBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  smithBitOperationWorkBound dimension
    (smithCoefficientWorkBitLength dimension inputBits)

theorem smithBitOperationCost_le_polynomial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    smithBitOperationCost A hdet ≤
      smithPolynomialBitOperationBound n (matrixBitLength A) := by
  apply smithBitOperationCost_le_work A hdet
  · exact le_max_left _ _
  · exact (determinant_bitLength_le A).trans (le_max_right _ _)

end NormalForms.Research.KannanBachem.Smith
