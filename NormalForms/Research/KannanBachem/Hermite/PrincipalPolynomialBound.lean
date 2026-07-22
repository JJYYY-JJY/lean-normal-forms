/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalTraceBound
import all NormalForms.Research.KannanBachem.Hermite.PrincipalTraceBound

/-! Closed polynomial bit-length bounds for the ready principal HNF kernel. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix

namespace Principal

theorem natSize_add_le (left right : Nat) :
    Nat.size (left + right) ≤ Nat.size left + Nat.size right + 1 := by
  rw [Nat.size_le]
  have leftLt : left < 2 ^ Nat.size left := Nat.lt_size_self left
  have rightLt : right < 2 ^ Nat.size right := Nat.lt_size_self right
  have leftPow : 2 ^ Nat.size left ≤
      2 ^ (Nat.size left + Nat.size right) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _)
  have rightPow : 2 ^ Nat.size right ≤
      2 ^ (Nat.size left + Nat.size right) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)
  calc
    left + right <
        2 ^ (Nat.size left + Nat.size right) +
          2 ^ (Nat.size left + Nat.size right) :=
      Nat.add_lt_add (leftLt.trans_le leftPow) (rightLt.trans_le rightPow)
    _ = 2 ^ (Nat.size left + Nat.size right + 1) := by
      rw [pow_succ]
      ring

theorem natSize_mul_le' (left right : Nat) :
    Nat.size (left * right) ≤ Nat.size left + Nat.size right := by
  rw [Nat.size_le, pow_add]
  exact mul_lt_mul''
    (Nat.lt_size_self left)
    (Nat.lt_size_self right)
    (Nat.zero_le _)
    (Nat.zero_le _)

theorem natSize_pow_le' (base exponent : Nat) :
    Nat.size (base ^ exponent) ≤ exponent * Nat.size base + 1 := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
      rw [pow_succ]
      calc
        Nat.size (base ^ exponent * base) ≤
            Nat.size (base ^ exponent) + Nat.size base :=
          natSize_mul_le' _ _
        _ ≤ (exponent * Nat.size base + 1) + Nat.size base :=
          Nat.add_le_add_right ih _
        _ = (exponent + 1) * Nat.size base + 1 := by ring

theorem natSize_succ_le (value : Nat) :
    Nat.size (value + 1) ≤ Nat.size value + 1 := by
  rw [Nat.size_le]
  have valueLt : value < 2 ^ Nat.size value := Nat.lt_size_self value
  have successorLe : value + 1 ≤ 2 ^ Nat.size value := by omega
  exact successorLe.trans_lt <|
    Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)

theorem natSize_le_self (value : Nat) : Nat.size value ≤ value := by
  exact Nat.size_le.2 value.lt_two_pow_self

theorem determinantBitLengthBound_le_polynomial (order inputBits : Nat) :
    determinantBitLengthBound order inputBits ≤
      order * (order + inputBits) + 2 := by
  unfold determinantBitLengthBound
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left order
      (Nat.add_le_add_right (natSize_le_self order) inputBits)) 2

@[expose] public def stageMinorPolynomialBits (target inputBits : Nat) : Nat :=
  (target + 1) * ((target + 1) + (inputBits + 1)) + 2

@[expose] public def stagePairOperandPolynomialBits
    (target inputBits : Nat) : Nat :=
  (inputBits + 1) + stageMinorPolynomialBits target inputBits

@[expose] public def stagePairCoefficientPolynomialBits
    (target inputBits : Nat) : Nat :=
  2 * (stagePairOperandPolynomialBits target inputBits + 1) + 1

@[expose] public def stagePairRowPolynomialBits
    (target inputBits : Nat) : Nat :=
  2 + stagePairCoefficientPolynomialBits target inputBits +
    stagePairOperandPolynomialBits target inputBits

@[expose] public def stageBasePolynomialBits (target inputBits : Nat) : Nat :=
  (inputBits + 1) + stageMinorPolynomialBits target inputBits +
    stagePairRowPolynomialBits target inputBits

@[expose] public def stageIntermediatePolynomialBits
    (target inputBits : Nat) : Nat :=
  (stageBasePolynomialBits target inputBits + 1) +
    (target * (stagePairRowPolynomialBits target inputBits + 3) + 1)

/-- Closed polynomial bit budget for every matrix inside one ready stage. -/
@[expose] public def stagePolynomialBitLengthBound
    (target inputBits : Nat) : Nat :=
  (stageIntermediatePolynomialBits target inputBits + 1) +
    (stageMinorPolynomialBits target inputBits + 1)

theorem stageMinor_size_le (target inputBits : Nat) :
    Nat.size (stageMinorHeightBound target (2 ^ inputBits)) ≤
      stageMinorPolynomialBits target inputBits := by
  have powerPositive : 0 < 2 ^ inputBits := pow_pos (by omega) _
  unfold stageMinorHeightBound stageMinorPolynomialBits
  rw [max_eq_right powerPositive]
  have exactBound := factorial_mul_pow_size_le (target + 1) (2 ^ inputBits)
  rw [Nat.size_pow] at exactBound
  exact exactBound.trans
    (determinantBitLengthBound_le_polynomial (target + 1) (inputBits + 1))

theorem stagePairOperand_size_le (target inputBits : Nat) :
    Nat.size (stagePairOperandHeightBound target (2 ^ inputBits)) ≤
      stagePairOperandPolynomialBits target inputBits := by
  unfold stagePairOperandHeightBound stagePairOperandPolynomialBits
  rw [natSize_max, Nat.size_pow]
  exact max_le
    (Nat.le_add_right _ _)
    ((stageMinor_size_le target inputBits).trans (Nat.le_add_left _ _))

theorem stagePairCoefficient_size_le (target inputBits : Nat) :
    Nat.size (stagePairCoefficientHeightBound target (2 ^ inputBits)) ≤
      stagePairCoefficientPolynomialBits target inputBits := by
  unfold stagePairCoefficientHeightBound
  calc
    Nat.size
        ((stagePairOperandHeightBound target (2 ^ inputBits) + 1) ^ 2) ≤
      2 * Nat.size
          (stagePairOperandHeightBound target (2 ^ inputBits) + 1) + 1 :=
        natSize_pow_le' _ 2
    _ ≤ 2 * (stagePairOperandPolynomialBits target inputBits + 1) + 1 := by
      gcongr
      exact (natSize_succ_le _).trans
        (Nat.add_le_add_right (stagePairOperand_size_le target inputBits) 1)
    _ = stagePairCoefficientPolynomialBits target inputBits := rfl

theorem stagePairRow_size_le (target inputBits : Nat) :
    Nat.size (stagePairRowHeightBound target (2 ^ inputBits)) ≤
      stagePairRowPolynomialBits target inputBits := by
  unfold stagePairRowHeightBound stagePairRowPolynomialBits
  calc
    Nat.size
        (2 * stagePairCoefficientHeightBound target (2 ^ inputBits) *
          stagePairOperandHeightBound target (2 ^ inputBits)) ≤
      Nat.size
          (2 * stagePairCoefficientHeightBound target (2 ^ inputBits)) +
        Nat.size (stagePairOperandHeightBound target (2 ^ inputBits)) :=
      natSize_mul_le' _ _
    _ ≤ (Nat.size 2 +
          Nat.size (stagePairCoefficientHeightBound target (2 ^ inputBits))) +
        Nat.size (stagePairOperandHeightBound target (2 ^ inputBits)) :=
      Nat.add_le_add_right (natSize_mul_le' _ _) _
    _ ≤ 2 + stagePairCoefficientPolynomialBits target inputBits +
        stagePairOperandPolynomialBits target inputBits := by
      exact Nat.add_le_add
        (Nat.add_le_add_left (stagePairCoefficient_size_le target inputBits) 2)
        (stagePairOperand_size_le target inputBits)

theorem stageBase_size_le (target inputBits : Nat) :
    Nat.size
        (max (2 ^ inputBits)
          (max (stageMinorHeightBound target (2 ^ inputBits))
            (stagePairRowHeightBound target (2 ^ inputBits)))) ≤
      stageBasePolynomialBits target inputBits := by
  unfold stageBasePolynomialBits
  rw [natSize_max, natSize_max, Nat.size_pow]
  apply max_le
  · omega
  · apply max_le
    · exact (stageMinor_size_le target inputBits).trans (by omega)
    · exact (stagePairRow_size_le target inputBits).trans (by omega)

theorem stageIntermediate_size_le (target inputBits : Nat) :
    Nat.size
        (stageIntermediateHeightBound target target (2 ^ inputBits)) ≤
      stageIntermediatePolynomialBits target inputBits := by
  unfold stageIntermediateHeightBound stageIntermediatePolynomialBits
  let base := max (2 ^ inputBits)
    (max (stageMinorHeightBound target (2 ^ inputBits))
      (stagePairRowHeightBound target (2 ^ inputBits)))
  let row := stagePairRowHeightBound target (2 ^ inputBits)
  have rowSize : Nat.size row ≤
      stagePairRowPolynomialBits target inputBits := by
    simpa [row] using stagePairRow_size_le target inputBits
  have rowAddSize : Nat.size (row + 2) ≤
      stagePairRowPolynomialBits target inputBits + 3 := by
    calc
      Nat.size (row + 2) ≤ Nat.size row + Nat.size 2 + 1 :=
        natSize_add_le row 2
      _ ≤ stagePairRowPolynomialBits target inputBits + 3 := by
        have sizeTwo : Nat.size 2 = 2 := by decide
        rw [sizeTwo]
        omega
  calc
    Nat.size ((base + 1) * (row + 2) ^ target) ≤
        Nat.size (base + 1) + Nat.size ((row + 2) ^ target) :=
      natSize_mul_le' _ _
    _ ≤ Nat.size (base + 1) +
        (target * Nat.size (row + 2) + 1) :=
      Nat.add_le_add_left (natSize_pow_le' _ target) _
    _ ≤ (stageBasePolynomialBits target inputBits + 1) +
        (target * (stagePairRowPolynomialBits target inputBits + 3) + 1) := by
      apply Nat.add_le_add
      · exact (natSize_succ_le base).trans
          (Nat.add_le_add_right (stageBase_size_le target inputBits) 1)
      · exact Nat.add_le_add_right
          (Nat.mul_le_mul_left target rowAddSize) 1

theorem completedStage_size_le_stagePolynomial (target inputBits : Nat) :
    Nat.size (completedStageHeightBound target (2 ^ inputBits)) ≤
      stagePolynomialBitLengthBound target inputBits := by
  unfold completedStageHeightBound stagePolynomialBitLengthBound
  calc
    Nat.size
        ((stageIntermediateHeightBound target target (2 ^ inputBits) + 1) *
          (stageMinorHeightBound target (2 ^ inputBits) + 1)) ≤
      Nat.size
          (stageIntermediateHeightBound target target (2 ^ inputBits) + 1) +
        Nat.size (stageMinorHeightBound target (2 ^ inputBits) + 1) :=
      natSize_mul_le' _ _
    _ ≤ (stageIntermediatePolynomialBits target inputBits + 1) +
        (stageMinorPolynomialBits target inputBits + 1) :=
      Nat.add_le_add
        ((natSize_succ_le _).trans
          (Nat.add_le_add_right (stageIntermediate_size_le target inputBits) 1))
        ((natSize_succ_le _).trans
          (Nat.add_le_add_right (stageMinor_size_le target inputBits) 1))

/-- Polynomial stage-boundary budget uniform below a fixed dimension. -/
@[expose] public def stageBoundaryPolynomialBits
    (dimension inputBits : Nat) : Nat :=
  2 * inputBits + 2 * dimension +
    2 * dimension * (dimension + inputBits) + 4

theorem determinantBitLengthBound_le_dimensionPolynomial
    {order dimension inputBits : Nat} (hle : order ≤ dimension) :
    determinantBitLengthBound order inputBits ≤
      dimension * (dimension + inputBits) + 2 := by
  exact (determinantBitLengthBound_le_polynomial order inputBits).trans <|
    Nat.add_le_add_right
      (Nat.mul_le_mul hle (Nat.add_le_add_right hle inputBits)) 2

theorem stageStartBitLengthBound_le_boundaryPolynomial
    {k dimension inputBits : Nat} (hle : k ≤ dimension) :
    stageStartBitLengthBound k inputBits ≤
      stageBoundaryPolynomialBits dimension inputBits := by
  cases k with
  | zero =>
      change max inputBits 0 ≤ stageBoundaryPolynomialBits dimension inputBits
      rw [max_eq_left (Nat.zero_le inputBits)]
      unfold stageBoundaryPolynomialBits
      calc
        inputBits ≤ 2 * inputBits :=
          Nat.le_mul_of_pos_left inputBits (by omega)
        _ ≤ 2 * inputBits +
              (2 * dimension +
                2 * dimension * (dimension + inputBits) + 4) :=
          Nat.le_add_right _ _
        _ = 2 * inputBits + 2 * dimension +
              2 * dimension * (dimension + inputBits) + 4 := by ring
  | succ order =>
      have sizeLe : Nat.size (order + 1) ≤ dimension :=
        (natSize_le_self (order + 1)).trans hle
      have currentDet :
          determinantBitLengthBound (order + 1) inputBits ≤
            dimension * (dimension + inputBits) + 2 :=
        determinantBitLengthBound_le_dimensionPolynomial hle
      have previousLe : order ≤ dimension := by omega
      have previousDet : determinantBitLengthBound order inputBits ≤
          dimension * (dimension + inputBits) + 2 :=
        determinantBitLengthBound_le_dimensionPolynomial previousLe
      simp only [stageStartBitLengthBound,
        stageProcessedRowsBitLengthBound,
        stageLeadingMultiplierBitLengthBound,
        stageLeadingBitLengthBound]
      apply max_le
      · unfold stageBoundaryPolynomialBits
        omega
      · unfold stageBoundaryPolynomialBits
        calc
          Nat.size (order + 1) +
                (Nat.size (order + 1) +
                  determinantBitLengthBound (order + 1) inputBits +
                  determinantBitLengthBound order inputBits) +
              inputBits ≤
            dimension +
                (dimension +
                  (dimension * (dimension + inputBits) + 2) +
                  (dimension * (dimension + inputBits) + 2)) +
              inputBits := by omega
          _ = inputBits + 2 * dimension +
                2 * (dimension * (dimension + inputBits)) + 4 := by ring
          _ ≤ 2 * inputBits + 2 * dimension +
                2 * dimension * (dimension + inputBits) + 4 := by
            ring_nf
            omega

theorem stagePolynomialBitLengthBound_mono
    {smallerTarget largerTarget smallerBits largerBits : Nat}
    (target_le : smallerTarget ≤ largerTarget)
    (bits_le : smallerBits ≤ largerBits) :
    stagePolynomialBitLengthBound smallerTarget smallerBits ≤
      stagePolynomialBitLengthBound largerTarget largerBits := by
  unfold stagePolynomialBitLengthBound stageIntermediatePolynomialBits
    stageBasePolynomialBits stagePairRowPolynomialBits
    stagePairCoefficientPolynomialBits stagePairOperandPolynomialBits
    stageMinorPolynomialBits
  gcongr

/--
Closed polynomial coefficient-length budget for a ready square input.  Its
body contains only constants, addition, and multiplication of the dimension
and input bit length.
-/
@[expose] public def principalPolynomialBitLengthBound
    (dimension inputBits : Nat) : Nat :=
  (inputBits + 1) +
    stagePolynomialBitLengthBound dimension
      (stageBoundaryPolynomialBits dimension inputBits)

theorem principalIntermediateHeightBound_size_le_polynomial
    (k dimension inputBits : Nat) (hle : k ≤ dimension) :
    Nat.size (principalIntermediateHeightBound k inputBits) ≤
      principalPolynomialBitLengthBound dimension inputBits := by
  induction k with
  | zero =>
      rw [principalIntermediateHeightBound, Nat.size_pow]
      unfold principalPolynomialBitLengthBound
      exact Nat.le_add_right _ _
  | succ k ih =>
      rw [principalIntermediateHeightBound, natSize_max]
      apply max_le
      · exact ih (by omega)
      · have targetLe : k ≤ dimension := by omega
        have boundaryLe := stageStartBitLengthBound_le_boundaryPolynomial
          (k := k) (inputBits := inputBits) targetLe
        have stageSize := completedStage_size_le_stagePolynomial k
          (stageStartBitLengthBound k inputBits)
        unfold stageStartHeightBound
        refine stageSize.trans ?_
        unfold principalPolynomialBitLengthBound
        exact (stagePolynomialBitLengthBound_mono targetLe boundaryLe).trans
          (Nat.le_add_left _ _)

end Principal

/-- Ready principal traces have a closed polynomial coefficient-length bound. -/
public theorem principalIntermediateMatrixBitLength_le_polynomial_of_ready
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int)
    (ready : Principal.PrincipalReady A) :
    principalIntermediateMatrixBitLength A ≤
      Principal.principalPolynomialBitLengthBound n (matrixBitLength A) := by
  exact (principalIntermediateMatrixBitLength_le_of_ready A ready).trans <| by
    unfold Principal.principalIntermediateBitLengthBound
    exact Principal.principalIntermediateHeightBound_size_le_polynomial
      n n (matrixBitLength A) le_rfl

/-- All recorded Euclidean operands inherit the same polynomial bit budget. -/
public theorem principalArithmeticOperandBitLength_le_polynomial_of_ready
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int)
    (ready : Principal.PrincipalReady A) :
    principalArithmeticOperandBitLength A ≤
      Principal.principalPolynomialBitLengthBound n (matrixBitLength A) :=
  (principalArithmeticOperandBitLength_le_intermediateMatrixBitLength A).trans
    (principalIntermediateMatrixBitLength_le_polynomial_of_ready A ready)

end NormalForms.Research.KannanBachem.Hermite
