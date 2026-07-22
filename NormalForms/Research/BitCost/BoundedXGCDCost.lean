/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.BoundedXGCD

/-!
# Polynomial Primitive Cost for Bounded Extended GCD

The costed loop from `BoundedXGCD` reduces coefficients after every Euclidean
update.  This file converts the magnitude theorem into a uniform coefficient
bit budget, bounds one complete division/update/reduction level, and composes
those levels along the exact quotient path.
-/

public section

namespace NormalForms.Research.BitCost

/-- Long-division cost expressed only in operand bit lengths. -/
@[expose] public def divisionCostForBitLengths
    (numeratorBits divisorBits : Nat) : Nat :=
  8 + numeratorBits * (3 + 2 * divisorBits) +
    3 * numeratorBits + 3 * divisorBits

namespace Internal

public theorem divModBitOperationBound_le_lengths
    (numerator divisor : SignMagnitude)
    (numeratorBits divisorBits : Nat)
    (numeratorWidth : numerator.bitLength ≤ numeratorBits)
    (divisorWidth : divisor.bitLength ≤ divisorBits) :
    divModBitOperationBound numerator divisor ≤
      divisionCostForBitLengths numeratorBits divisorBits := by
  have factorWidth :
      3 + 2 * divisor.bitLength ≤ 3 + 2 * divisorBits := by omega
  have productWidth :
      numerator.bitLength * (3 + 2 * divisor.bitLength) ≤
        numeratorBits * (3 + 2 * divisorBits) :=
    Nat.mul_le_mul numeratorWidth factorWidth
  simp only [divModBitOperationBound, divisionCostForBitLengths]
  omega

end Internal

/-- Uniform bit budget for every reduced coefficient at an operand width. -/
@[expose] public def boundedXGCDCoefficientBitLengthBound
    (operandBits : Nat) : Nat :=
  2 * (operandBits + 2)

/-- Uniform bit budget immediately after the ordinary Euclidean update. -/
@[expose] public def boundedXGCDRawCoefficientBitLengthBound
    (operandBits : Nat) : Nat :=
  operandBits +
    2 * boundedXGCDCoefficientBitLengthBound operandBits + 2

namespace Internal

theorem boundedXGCDCoefficientHeight_size_le
    (left right : SignMagnitude) (operandBits : Nat)
    (leftWidth : left.bitLength ≤ operandBits)
    (rightWidth : right.bitLength ≤ operandBits) :
    Nat.size (boundedXGCDCoefficientHeight left right) ≤
      boundedXGCDCoefficientBitLengthBound operandBits := by
  let height := max left.value.natAbs right.value.natAbs
  have leftSize : Nat.size left.value.natAbs ≤ operandBits := by
    simpa [SignMagnitude.bitLength_eq_natSize_natAbs] using leftWidth
  have rightSize : Nat.size right.value.natAbs ≤ operandBits := by
    simpa [SignMagnitude.bitLength_eq_natSize_natAbs] using rightWidth
  have heightSize : Nat.size height ≤ operandBits := by
    apply Nat.size_le.mpr
    exact max_lt (Nat.size_le.mp leftSize) (Nat.size_le.mp rightSize)
  have successorSize := natSize_add_le height 1
  have successorSizeBound : Nat.size (height + 1) ≤ operandBits + 2 := by
    norm_num at successorSize
    omega
  have squareSize := natSize_mul_le (height + 1) (height + 1)
  unfold boundedXGCDCoefficientHeight boundedXGCDCoefficientBitLengthBound
  change Nat.size ((height + 1) ^ 2) ≤ 2 * (operandBits + 2)
  rw [pow_two]
  omega

end Internal

/-- Every per-level reduced Euclidean result has the uniform bit budget. -/
public theorem boundedEuclideanXGCDWithCost_coefficient_bitLength_le
    (left right : SignMagnitude) (operandBits : Nat)
    (leftWidth : left.bitLength ≤ operandBits)
    (rightWidth : right.bitLength ≤ operandBits) :
    (boundedEuclideanXGCDWithCost left right).value.leftCoeff.bitLength ≤
        boundedXGCDCoefficientBitLengthBound operandBits ∧
      (boundedEuclideanXGCDWithCost left right).value.rightCoeff.bitLength ≤
        boundedXGCDCoefficientBitLengthBound operandBits := by
  have magnitudeBound :=
    boundedEuclideanXGCDWithCost_coefficient_natAbs_le left right
  have heightSize := Internal.boundedXGCDCoefficientHeight_size_le
    left right operandBits leftWidth rightWidth
  rw [SignMagnitude.bitLength_eq_natSize_natAbs,
    SignMagnitude.bitLength_eq_natSize_natAbs]
  exact ⟨(Nat.size_le_size magnitudeBound.1).trans heightSize,
    (Nat.size_le_size magnitudeBound.2).trans heightSize⟩

/-- Cost of the second Appendix-reduction half of one Euclidean level. -/
@[expose] public def boundedXGCDReductionCostBound
    (operandBits : Nat) : Nat :=
  let rawBits := boundedXGCDRawCoefficientBitLengthBound operandBits
  1 + divisionCostForBitLengths rawBits operandBits +
    multiplicationCostForBitLengths (rawBits + 1) operandBits +
    additionCostForBitLengths rawBits (rawBits + 1 + operandBits)

namespace Internal

public theorem reduceBezoutWithCost_cost_le
    (left right : SignMagnitude) (raw : XGCDResult)
    (operandBits rawBits : Nat)
    (leftWidth : left.bitLength ≤ operandBits)
    (rightWidth : right.bitLength ≤ operandBits)
    (rawLeftWidth : raw.leftCoeff.bitLength ≤ rawBits)
    (rawRightWidth : raw.rightCoeff.bitLength ≤ rawBits) :
    (reduceBezoutWithCost left right raw).cost ≤
      1 + divisionCostForBitLengths rawBits operandBits +
        multiplicationCostForBitLengths (rawBits + 1) operandBits +
        additionCostForBitLengths rawBits (rawBits + 1 + operandBits) := by
  by_cases main : left ≠ 0 ∧ right.value.natAbs ≤ left.value.natAbs
  · let division := divModWithCost raw.rightCoeff left
    let product := mulWithCost division.value.quotient right
    let adjusted := addWithCost raw.leftCoeff product.value
    have divisionCost :
        division.cost ≤ divisionCostForBitLengths rawBits operandBits := by
      exact (divModWithCost_cost_le raw.rightCoeff left).trans
        (divModBitOperationBound_le_lengths _ _ _ _
          rawRightWidth leftWidth)
    have quotientWidth : division.value.quotient.bitLength ≤ rawBits + 1 := by
      exact (divModWithCost_quotient_bitLength_le raw.rightCoeff left).trans
        (Nat.add_le_add_right rawRightWidth 1)
    have productPrimitiveCost :=
      mulWithCost_cost_le division.value.quotient right
    have productCost :
        product.cost ≤
          multiplicationCostForBitLengths (rawBits + 1) operandBits := by
      simpa only [product] using productPrimitiveCost.trans
        (mulBitOperationBound_le_lengths _ _ _ _ quotientWidth rightWidth)
    have productWidth :
        product.value.bitLength ≤ rawBits + 1 + operandBits := by
      simpa only [product] using
        (mulWithCost_value_bitLength_le division.value.quotient right).trans
          (Nat.add_le_add quotientWidth rightWidth)
    have adjustedPrimitiveCost :=
      addWithCost_cost_le raw.leftCoeff product.value
    have adjustedCost :
        adjusted.cost ≤
          additionCostForBitLengths rawBits (rawBits + 1 + operandBits) := by
      simpa only [adjusted] using adjustedPrimitiveCost.trans
        (addBitOperationBound_le_lengths _ _ _ _ rawLeftWidth productWidth)
    simp only [reduceBezoutWithCost, dif_pos main]
    change 1 + division.cost + product.cost + adjusted.cost ≤ _
    omega
  · by_cases rightNonzero : right ≠ 0
    · let division := divModWithCost raw.leftCoeff right
      let product := mulWithCost division.value.quotient left
      let adjusted := addWithCost raw.rightCoeff product.value
      have divisionCost :
          division.cost ≤ divisionCostForBitLengths rawBits operandBits := by
        exact (divModWithCost_cost_le raw.leftCoeff right).trans
          (divModBitOperationBound_le_lengths _ _ _ _
            rawLeftWidth rightWidth)
      have quotientWidth : division.value.quotient.bitLength ≤ rawBits + 1 := by
        exact (divModWithCost_quotient_bitLength_le raw.leftCoeff right).trans
          (Nat.add_le_add_right rawLeftWidth 1)
      have productPrimitiveCost :=
        mulWithCost_cost_le division.value.quotient left
      have productCost :
          product.cost ≤
            multiplicationCostForBitLengths (rawBits + 1) operandBits := by
        simpa only [product] using productPrimitiveCost.trans
          (mulBitOperationBound_le_lengths _ _ _ _ quotientWidth leftWidth)
      have productWidth :
          product.value.bitLength ≤ rawBits + 1 + operandBits := by
        simpa only [product] using
          (mulWithCost_value_bitLength_le division.value.quotient left).trans
            (Nat.add_le_add quotientWidth leftWidth)
      have adjustedPrimitiveCost :=
        addWithCost_cost_le raw.rightCoeff product.value
      have adjustedCost :
          adjusted.cost ≤
            additionCostForBitLengths rawBits (rawBits + 1 + operandBits) := by
        simpa only [adjusted] using adjustedPrimitiveCost.trans
          (addBitOperationBound_le_lengths _ _ _ _ rawRightWidth productWidth)
      simp only [reduceBezoutWithCost, dif_neg main, dif_pos rightNonzero]
      change 1 + division.cost + product.cost + adjusted.cost ≤ _
      omega
    · simp only [reduceBezoutWithCost, dif_neg main, dif_neg rightNonzero]
      omega

end Internal

/-- Cost of the ordinary quotient/coefficient-update half of one level. -/
@[expose] public def boundedXGCDEuclideanUpdateCostBound
    (operandBits : Nat) : Nat :=
  let coefficientBits := boundedXGCDCoefficientBitLengthBound operandBits
  1 + divisionCostForBitLengths operandBits operandBits +
    multiplicationCostForBitLengths (operandBits + 1) coefficientBits +
    additionCostForBitLengths coefficientBits
      (operandBits + 1 + coefficientBits)

/-- Complete division, coefficient update, and Appendix reduction cost. -/
@[expose] public def boundedXGCDStepCostBound (operandBits : Nat) : Nat :=
  boundedXGCDEuclideanUpdateCostBound operandBits +
    boundedXGCDReductionCostBound operandBits

/-- Exact number of nonterminal divisions followed by the costed loop. -/
@[expose] public def boundedEuclideanXGCDDivisions :
    SignMagnitude → SignMagnitude → Nat
  | _, .zero => 0
  | left, right@(.pos _) =>
      1 + boundedEuclideanXGCDDivisions right
        (divModWithCost left right).value.remainder
  | left, right@(.neg _) =>
      1 + boundedEuclideanXGCDDivisions right
        (divModWithCost left right).value.remainder
termination_by _ right => right.value.natAbs
decreasing_by
  all_goals
    subst right
    apply divModWithCost_remainder_measure_lt
    simp

namespace Internal

/-- One ordinary Euclidean update is bounded at uniform operand width. -/
public theorem xgcdStep_cost_le_operandBits
    (left right : SignMagnitude)
    (recursive : WithCost XGCDResult)
    (operandBits recursiveCostBound : Nat)
    (leftWidth : left.bitLength ≤ operandBits)
    (rightWidth : right.bitLength ≤ operandBits)
    (recursiveWidths :
      recursive.value.leftCoeff.bitLength ≤
          boundedXGCDCoefficientBitLengthBound operandBits ∧
        recursive.value.rightCoeff.bitLength ≤
          boundedXGCDCoefficientBitLengthBound operandBits)
    (recursiveCost : recursive.cost ≤ recursiveCostBound) :
    (xgcdStep (divModWithCost left right) recursive).cost ≤
      recursiveCostBound + boundedXGCDEuclideanUpdateCostBound operandBits := by
  let coefficientBits := boundedXGCDCoefficientBitLengthBound operandBits
  let division := divModWithCost left right
  let product := mulWithCost division.value.quotient recursive.value.rightCoeff
  let adjusted := addWithCost recursive.value.leftCoeff (-product.value)
  have divisionCost :
      division.cost ≤ divisionCostForBitLengths operandBits operandBits := by
    exact (divModWithCost_cost_le left right).trans
      (divModBitOperationBound_le_lengths _ _ _ _ leftWidth rightWidth)
  have quotientWidth : division.value.quotient.bitLength ≤ operandBits + 1 := by
    exact (divModWithCost_quotient_bitLength_le left right).trans
      (Nat.add_le_add_right leftWidth 1)
  have productPrimitiveCost :=
    mulWithCost_cost_le division.value.quotient recursive.value.rightCoeff
  have productCost :
      product.cost ≤
        multiplicationCostForBitLengths (operandBits + 1) coefficientBits := by
    simpa only [product, coefficientBits] using productPrimitiveCost.trans
      (mulBitOperationBound_le_lengths _ _ _ _ quotientWidth recursiveWidths.2)
  have productWidth :
      product.value.bitLength ≤ operandBits + 1 + coefficientBits := by
    simpa only [product, coefficientBits] using
      (mulWithCost_value_bitLength_le division.value.quotient
        recursive.value.rightCoeff).trans
        (Nat.add_le_add quotientWidth recursiveWidths.2)
  have adjustedPrimitiveCost :=
    addWithCost_cost_le recursive.value.leftCoeff (-product.value)
  have adjustedCost :
      adjusted.cost ≤
        additionCostForBitLengths coefficientBits
          (operandBits + 1 + coefficientBits) := by
    simpa only [adjusted, coefficientBits] using adjustedPrimitiveCost.trans
      (addBitOperationBound_le_lengths _ _ _ _ recursiveWidths.1
        (by simpa only [SignMagnitude.bitLength_neg] using productWidth))
  change
    1 + division.cost + recursive.cost + product.cost + adjusted.cost ≤
      recursiveCostBound + boundedXGCDEuclideanUpdateCostBound operandBits
  simp only [coefficientBits] at productCost adjustedCost
  simp only [boundedXGCDEuclideanUpdateCostBound]
  omega

/-- The ordinary update's output coefficients fit the raw uniform budget. -/
public theorem xgcdStep_coefficient_bitLength_le_operandBits
    (left right : SignMagnitude)
    (recursive : WithCost XGCDResult) (operandBits : Nat)
    (leftWidth : left.bitLength ≤ operandBits)
    (recursiveWidths :
      recursive.value.leftCoeff.bitLength ≤
          boundedXGCDCoefficientBitLengthBound operandBits ∧
        recursive.value.rightCoeff.bitLength ≤
          boundedXGCDCoefficientBitLengthBound operandBits) :
    (xgcdStep (divModWithCost left right) recursive).value.leftCoeff.bitLength ≤
        boundedXGCDRawCoefficientBitLengthBound operandBits ∧
      (xgcdStep (divModWithCost left right) recursive).value.rightCoeff.bitLength ≤
        boundedXGCDRawCoefficientBitLengthBound operandBits := by
  have quotientWidth :
      (divModWithCost left right).value.quotient.bitLength ≤ operandBits + 1 :=
    (divModWithCost_quotient_bitLength_le left right).trans
      (Nat.add_le_add_right leftWidth 1)
  have rawWidths := xgcdStep_coefficient_bitLength_le
    (divModWithCost left right) recursive
    (boundedXGCDCoefficientBitLengthBound operandBits) recursiveWidths
  unfold boundedXGCDRawCoefficientBitLengthBound
  exact ⟨rawWidths.1.trans (by omega), rawWidths.2.trans (by omega)⟩

end Internal

/--
The exact modeled cost follows the quotient path, with a polynomial charge at
each level.  This theorem is independent of input signs; sign normalization is
used only for the later closed iteration bound.
-/
public theorem boundedEuclideanXGCDWithCost_cost_le
    (left right : SignMagnitude) (operandBits : Nat)
    (leftWidth : left.bitLength ≤ operandBits)
    (rightWidth : right.bitLength ≤ operandBits) :
    (boundedEuclideanXGCDWithCost left right).cost ≤
      1 + boundedEuclideanXGCDDivisions left right *
        boundedXGCDStepCostBound operandBits := by
  induction left, right using boundedEuclideanXGCDWithCost.induct
      generalizing operandBits with
  | case1 left =>
      rw [boundedEuclideanXGCDWithCost, boundedEuclideanXGCDDivisions]
      change 1 ≤ 1 + 0 * boundedXGCDStepCostBound operandBits
      omega
  | case2 left magnitude _division ih =>
      let right : SignMagnitude := .pos magnitude
      let division := divModWithCost left right
      let recursive := boundedEuclideanXGCDWithCost
        right division.value.remainder
      let raw := Internal.xgcdStep division recursive
      let reduced := Internal.reduceBezoutWithCost left right raw.value
      have remainderWidth : division.value.remainder.bitLength ≤ operandBits :=
        (divModWithCost_remainder_bitLength_le left right (by simp [right])).trans
          rightWidth
      have recursiveCost := ih operandBits rightWidth remainderWidth
      have recursiveWidths :=
        boundedEuclideanXGCDWithCost_coefficient_bitLength_le
          right division.value.remainder operandBits rightWidth remainderWidth
      have rawCost :
          raw.cost ≤
            (1 + boundedEuclideanXGCDDivisions right division.value.remainder *
                boundedXGCDStepCostBound operandBits) +
              boundedXGCDEuclideanUpdateCostBound operandBits := by
        simpa only [raw, division, recursive] using
          Internal.xgcdStep_cost_le_operandBits left right recursive
            operandBits _ leftWidth rightWidth recursiveWidths recursiveCost
      have rawWidths :
          raw.value.leftCoeff.bitLength ≤
              boundedXGCDRawCoefficientBitLengthBound operandBits ∧
            raw.value.rightCoeff.bitLength ≤
              boundedXGCDRawCoefficientBitLengthBound operandBits := by
        simpa only [raw, division, recursive] using
          Internal.xgcdStep_coefficient_bitLength_le_operandBits
            left right recursive operandBits leftWidth recursiveWidths
      have reducedCost :
          reduced.cost ≤ boundedXGCDReductionCostBound operandBits := by
        simpa only [reduced, boundedXGCDReductionCostBound] using
          Internal.reduceBezoutWithCost_cost_le left right raw.value
            operandBits (boundedXGCDRawCoefficientBitLengthBound operandBits)
            leftWidth rightWidth rawWidths.1 rawWidths.2
      rw [boundedEuclideanXGCDWithCost, boundedEuclideanXGCDDivisions]
      change raw.cost + reduced.cost ≤ _
      simp only [division, right, boundedXGCDStepCostBound] at rawCost
      simp only [boundedXGCDStepCostBound, Nat.add_mul, Nat.one_mul]
      omega
  | case3 left magnitude _division ih =>
      let right : SignMagnitude := .neg magnitude
      let division := divModWithCost left right
      let recursive := boundedEuclideanXGCDWithCost
        right division.value.remainder
      let raw := Internal.xgcdStep division recursive
      let reduced := Internal.reduceBezoutWithCost left right raw.value
      have remainderWidth : division.value.remainder.bitLength ≤ operandBits :=
        (divModWithCost_remainder_bitLength_le left right (by simp [right])).trans
          rightWidth
      have recursiveCost := ih operandBits rightWidth remainderWidth
      have recursiveWidths :=
        boundedEuclideanXGCDWithCost_coefficient_bitLength_le
          right division.value.remainder operandBits rightWidth remainderWidth
      have rawCost :
          raw.cost ≤
            (1 + boundedEuclideanXGCDDivisions right division.value.remainder *
                boundedXGCDStepCostBound operandBits) +
              boundedXGCDEuclideanUpdateCostBound operandBits := by
        simpa only [raw, division, recursive] using
          Internal.xgcdStep_cost_le_operandBits left right recursive
            operandBits _ leftWidth rightWidth recursiveWidths recursiveCost
      have rawWidths :
          raw.value.leftCoeff.bitLength ≤
              boundedXGCDRawCoefficientBitLengthBound operandBits ∧
            raw.value.rightCoeff.bitLength ≤
              boundedXGCDRawCoefficientBitLengthBound operandBits := by
        simpa only [raw, division, recursive] using
          Internal.xgcdStep_coefficient_bitLength_le_operandBits
            left right recursive operandBits leftWidth recursiveWidths
      have reducedCost :
          reduced.cost ≤ boundedXGCDReductionCostBound operandBits := by
        simpa only [reduced, boundedXGCDReductionCostBound] using
          Internal.reduceBezoutWithCost_cost_le left right raw.value
            operandBits (boundedXGCDRawCoefficientBitLengthBound operandBits)
            leftWidth rightWidth rawWidths.1 rawWidths.2
      rw [boundedEuclideanXGCDWithCost, boundedEuclideanXGCDDivisions]
      change raw.cost + reduced.cost ≤ _
      simp only [division, right, boundedXGCDStepCostBound] at rawCost
      simp only [boundedXGCDStepCostBound, Nat.add_mul, Nat.one_mul]
      omega

namespace Internal

public theorem divModRemainder_value_nonnegative
    (left right : SignMagnitude) (rightNonzero : right ≠ 0) :
    0 ≤ (divModWithCost left right).value.remainder.value := by
  rw [divModWithCost_remainder_value]
  have rightValueNonzero : right.value ≠ 0 := by
    intro valueZero
    apply rightNonzero
    rw [← SignMagnitude.ofInt_value right, valueZero]
    rfl
  exact Int.emod_nonneg left.value rightValueNonzero

public theorem divModRemainder_natAbs_eq_mod
    (left right : SignMagnitude)
    (leftNonnegative : 0 ≤ left.value)
    (rightNonnegative : 0 ≤ right.value)
    (rightNonzero : right ≠ 0) :
    (divModWithCost left right).value.remainder.value.natAbs =
      left.value.natAbs % right.value.natAbs := by
  have remainderNonnegative :=
    divModRemainder_value_nonnegative left right rightNonzero
  have leftEquation := Int.eq_natAbs_of_nonneg leftNonnegative
  have rightEquation := Int.eq_natAbs_of_nonneg rightNonnegative
  apply Int.natCast_inj.mp
  rw [Int.natCast_natAbs, abs_of_nonneg remainderNonnegative,
    divModWithCost_remainder_value, leftEquation, rightEquation,
    ← Int.natCast_emod]
  simp only [Int.natAbs_natCast]

end Internal

/-- On nonnegative operands the costed quotient path is the natural path. -/
public theorem boundedEuclideanXGCDDivisions_eq_euclideanIterations
    (left right : SignMagnitude)
    (leftNonnegative : 0 ≤ left.value)
    (rightNonnegative : 0 ≤ right.value) :
    boundedEuclideanXGCDDivisions left right =
      euclideanIterations left.value.natAbs right.value.natAbs := by
  induction left, right using boundedEuclideanXGCDDivisions.induct with
  | case1 left =>
      rw [boundedEuclideanXGCDDivisions]
      change 0 = euclideanIterations left.value.natAbs 0
      rw [euclideanIterations_zero]
  | case2 left magnitude ih =>
      let right : SignMagnitude := .pos magnitude
      let remainder := (divModWithCost left right).value.remainder
      have rightValueNonzero : right.value ≠ 0 := by
        change (magnitude : Int) ≠ 0
        exact ne_of_gt (PosNum.cast_pos magnitude)
      have rightPositive : 0 < right.value.natAbs := by
        exact Int.natAbs_pos.mpr rightValueNonzero
      have remainderNonnegative : 0 ≤ remainder.value :=
        Internal.divModRemainder_value_nonnegative left right (by simp [right])
      have remainderNatAbs :
          remainder.value.natAbs =
            left.value.natAbs % right.value.natAbs :=
        Internal.divModRemainder_natAbs_eq_mod left right
          leftNonnegative rightNonnegative (by simp [right])
      have recursive := ih rightNonnegative remainderNonnegative
      rw [boundedEuclideanXGCDDivisions,
        euclideanIterations_of_pos _ _ rightPositive]
      simpa only [right, remainder, remainderNatAbs,
        Nat.succ_eq_add_one, Nat.add_comm] using
        congrArg Nat.succ recursive
  | case3 left magnitude ih =>
      have impossible : ¬(0 ≤ (SignMagnitude.value (.neg magnitude))) := by
        change ¬(0 ≤ -(magnitude : Int))
        have positive : (0 : Int) < (magnitude : Int) := PosNum.cast_pos magnitude
        omega
      exact (impossible rightNonnegative).elim

/-- Closed polynomial bound for the sign-normalized bounded XGCD primitive. -/
@[expose] public def boundedXGCDPolynomialBitOperationBound
    (leftBits rightBits : Nat) : Nat :=
  let operandBits := max leftBits rightBits
  3 + (leftBits + rightBits + 1) *
    boundedXGCDStepCostBound operandBits

/-- The exact sign-magnitude implementation has the closed polynomial cost. -/
public theorem boundedXGCDWithCost_cost_le
    (left right : SignMagnitude) :
    (boundedXGCDWithCost left right).cost ≤
      boundedXGCDPolynomialBitOperationBound
        left.bitLength right.bitLength := by
  let operandBits := max left.bitLength right.bitLength
  let normalizedLeft := left.nonnegative
  let normalizedRight := right.nonnegative
  have leftWidth : normalizedLeft.bitLength ≤ operandBits := by
    simp only [normalizedLeft, SignMagnitude.nonnegative_bitLength, operandBits]
    exact le_max_left _ _
  have rightWidth : normalizedRight.bitLength ≤ operandBits := by
    simp only [normalizedRight, SignMagnitude.nonnegative_bitLength, operandBits]
    exact le_max_right _ _
  have rawCost := boundedEuclideanXGCDWithCost_cost_le
    normalizedLeft normalizedRight operandBits leftWidth rightWidth
  have divisionEquation :=
    boundedEuclideanXGCDDivisions_eq_euclideanIterations
      normalizedLeft normalizedRight
      (by simp [normalizedLeft]) (by simp [normalizedRight])
  have iterations := euclideanIterations_le_bitLengths
    normalizedLeft.value.natAbs normalizedRight.value.natAbs
  have divisionBound :
      boundedEuclideanXGCDDivisions normalizedLeft normalizedRight ≤
        left.bitLength + right.bitLength + 1 := by
    rw [divisionEquation]
    simpa only [normalizedLeft, normalizedRight,
      SignMagnitude.nonnegative_value_natAbs,
      ← SignMagnitude.bitLength_eq_natSize_natAbs] using iterations
  have multiplied := Nat.mul_le_mul_right
    (boundedXGCDStepCostBound operandBits) divisionBound
  change
    2 + (boundedEuclideanXGCDWithCost normalizedLeft normalizedRight).cost ≤ _
  simp only [boundedXGCDPolynomialBitOperationBound]
  change
    2 + (boundedEuclideanXGCDWithCost normalizedLeft normalizedRight).cost ≤
      3 + (left.bitLength + right.bitLength + 1) *
        boundedXGCDStepCostBound operandBits
  omega

/-- A uniform-width form suitable for charging many bounded XGCD calls. -/
public theorem boundedXGCDWithCost_cost_le_uniform
    (left right : SignMagnitude) (operandBits : Nat)
    (leftWidth : left.bitLength ≤ operandBits)
    (rightWidth : right.bitLength ≤ operandBits) :
    (boundedXGCDWithCost left right).cost ≤
      3 + (2 * operandBits + 1) *
        boundedXGCDStepCostBound operandBits := by
  let normalizedLeft := left.nonnegative
  let normalizedRight := right.nonnegative
  have normalizedLeftWidth : normalizedLeft.bitLength ≤ operandBits := by
    simpa only [normalizedLeft, SignMagnitude.nonnegative_bitLength] using
      leftWidth
  have normalizedRightWidth : normalizedRight.bitLength ≤ operandBits := by
    simpa only [normalizedRight, SignMagnitude.nonnegative_bitLength] using
      rightWidth
  have rawCost := boundedEuclideanXGCDWithCost_cost_le
    normalizedLeft normalizedRight operandBits
      normalizedLeftWidth normalizedRightWidth
  have divisionEquation :=
    boundedEuclideanXGCDDivisions_eq_euclideanIterations
      normalizedLeft normalizedRight
      (by simp [normalizedLeft]) (by simp [normalizedRight])
  have iterations := euclideanIterations_le_bitLengths
    normalizedLeft.value.natAbs normalizedRight.value.natAbs
  have divisionBound :
      boundedEuclideanXGCDDivisions normalizedLeft normalizedRight ≤
        2 * operandBits + 1 := by
    rw [divisionEquation]
    have pathBound :
        boundedEuclideanXGCDDivisions normalizedLeft normalizedRight ≤
          left.bitLength + right.bitLength + 1 := by
      rw [divisionEquation]
      simpa only [normalizedLeft, normalizedRight,
        SignMagnitude.nonnegative_value_natAbs,
        ← SignMagnitude.bitLength_eq_natSize_natAbs] using iterations
    omega
  have multiplied := Nat.mul_le_mul_right
    (boundedXGCDStepCostBound operandBits) divisionBound
  change
    2 + (boundedEuclideanXGCDWithCost normalizedLeft normalizedRight).cost ≤ _
  omega

end NormalForms.Research.BitCost
