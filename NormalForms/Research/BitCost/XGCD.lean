/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.Division

/-!
# Costed Extended Euclidean Algorithm

The loop in this module is the textbook Euclidean recurrence. Each iteration
uses the shared costed quotient/remainder operation, recursively solves the
smaller pair, and updates the second Bézout coefficient with the costed
schoolbook multiplication and addition primitives.
-/

public section

namespace NormalForms.Research.BitCost

namespace Internal

/-- Normalized terminal gcd and its unit coefficient. -/
@[expose] public def xgcdBase : SignMagnitude → XGCDResult
  | .zero =>
      { gcd := 0, leftCoeff := 1, rightCoeff := 0 }
  | .pos magnitude =>
      { gcd := .pos magnitude, leftCoeff := 1, rightCoeff := 0 }
  | .neg magnitude =>
      { gcd := .pos magnitude, leftCoeff := -1, rightCoeff := 0 }

/-- One extended-Euclidean coefficient update. -/
@[expose] public def xgcdStep
    (division : WithCost DivModResult)
    (recursive : WithCost XGCDResult) :
    WithCost XGCDResult :=
  let product :=
    mulWithCost division.value.quotient
      recursive.value.rightCoeff
  let adjusted :=
    addWithCost recursive.value.leftCoeff (-product.value)
  { value :=
      { gcd := recursive.value.gcd
        leftCoeff := recursive.value.rightCoeff
        rightCoeff := adjusted.value }
    cost :=
      1 + division.cost + recursive.cost +
        product.cost + adjusted.cost }

end Internal

/-- Kernel-checkable mathematical specification of an extended-gcd result. -/
public structure XGCDSpecification
    (left right : SignMagnitude) (result : XGCDResult) : Prop where
  gcd_value :
    result.gcd.value = (left.value.gcd right.value : Nat)
  bezout :
    result.leftCoeff.value * left.value +
        result.rightCoeff.value * right.value =
      result.gcd.value

namespace Internal

/-- The terminal branch has the normalized gcd and a valid unit coefficient. -/
public theorem xgcdBase_spec (left : SignMagnitude) :
    XGCDSpecification left 0 (xgcdBase left) := by
  constructor
  · cases left with
    | zero => rfl
    | pos magnitude =>
        change (ZNum.pos magnitude : Int) =
          (((ZNum.pos magnitude : Int).gcd 0 : Nat) : Int)
        rw [Int.gcd_zero_right]
        have magnitudeAbs :
            (magnitude : Nat) =
              (ZNum.pos magnitude : Int).natAbs := by
          simpa [ZNum.abs] using
            ZNum.abs_to_nat (ZNum.pos magnitude)
        calc
          (ZNum.pos magnitude : Int) =
              ((magnitude : Nat) : Int) := by
            rw [ZNum.cast_pos, PosNum.to_nat_to_int]
          _ = ((ZNum.pos magnitude : Int).natAbs : Int) :=
            congrArg Int.ofNat magnitudeAbs
    | neg magnitude =>
        change (ZNum.pos magnitude : Int) =
          (((ZNum.neg magnitude : Int).gcd 0 : Nat) : Int)
        rw [Int.gcd_zero_right]
        have magnitudeAbs :
            (magnitude : Nat) =
              (ZNum.neg magnitude : Int).natAbs := by
          simpa [ZNum.abs] using
            ZNum.abs_to_nat (ZNum.neg magnitude)
        calc
          (ZNum.pos magnitude : Int) =
              ((magnitude : Nat) : Int) := by
            rw [ZNum.cast_pos, PosNum.to_nat_to_int]
          _ = ((ZNum.neg magnitude : Int).natAbs : Int) :=
            congrArg Int.ofNat magnitudeAbs
  · cases left <;>
      simp [xgcdBase, SignMagnitude.value]

/-- One Euclidean update transports both gcd and Bézout correctness. -/
public theorem xgcdStep_spec
    (left right : SignMagnitude)
    (recursive : WithCost XGCDResult)
    (recursive_spec :
      XGCDSpecification right
        (divModWithCost left right).value.remainder recursive.value) :
    XGCDSpecification left right
      (xgcdStep (divModWithCost left right) recursive).value := by
  let division := divModWithCost left right
  let product :=
    mulWithCost division.value.quotient recursive.value.rightCoeff
  let adjusted :=
    addWithCost recursive.value.leftCoeff (-product.value)
  have remainderValue := divModWithCost_remainder_value left right
  have quotientValue := divModWithCost_quotient_value left right
  constructor
  · change recursive.value.gcd.value =
      (left.value.gcd right.value : Nat)
    rw [recursive_spec.gcd_value]
    congr 1
    rw [remainderValue]
    calc
      right.value.gcd (left.value % right.value) =
          (left.value % right.value).gcd right.value :=
        Int.gcd_comm _ _
      _ = left.value.gcd right.value :=
        Int.gcd_emod _ _
  · change recursive.value.rightCoeff.value * left.value +
        adjusted.value.value * right.value =
      recursive.value.gcd.value
    rw [addWithCost_value, SignMagnitude.value_neg,
      mulWithCost_value]
    have divisionEquation :
        division.value.quotient.value * right.value +
            division.value.remainder.value = left.value := by
      rw [quotientValue, remainderValue]
      exact Int.ediv_mul_add_emod left.value right.value
    calc
      recursive.value.rightCoeff.value * left.value +
          (recursive.value.leftCoeff.value -
            division.value.quotient.value *
              recursive.value.rightCoeff.value) * right.value =
        recursive.value.leftCoeff.value * right.value +
          recursive.value.rightCoeff.value *
            division.value.remainder.value := by
              rw [← divisionEquation]
              ring
      _ = recursive.value.gcd.value := recursive_spec.bezout

end Internal

/--
Binary extended gcd with exact accumulated primitive cost.

The returned gcd is nonnegative. The two coefficients satisfy the Bézout
equation over the original signed inputs.
-/
@[expose] public def xgcdWithCost :
    SignMagnitude → SignMagnitude → WithCost XGCDResult
  | left, .zero =>
      { value := Internal.xgcdBase left
        cost := 1 }
  | left, right@(.pos _) =>
      let division := divModWithCost left right
      let recursive :=
        xgcdWithCost right division.value.remainder
      Internal.xgcdStep division recursive
  | left, right@(.neg _) =>
      let division := divModWithCost left right
      let recursive :=
        xgcdWithCost right division.value.remainder
      Internal.xgcdStep division recursive
termination_by _ right => right.value.natAbs
decreasing_by
  all_goals
    subst right
    apply divModWithCost_remainder_measure_lt
    simp

/--
Path-sensitive coefficient-width budget for the extended-Euclidean recurrence.
It depends only on the Euclidean quotient sequence of the two inputs, not on
the computed Bézout coefficients.
-/
@[expose] public def xgcdCoefficientBitBound :
    SignMagnitude → SignMagnitude → Nat
  | _, .zero => 1
  | left, right@(.pos _) =>
      let division := divModWithCost left right
      division.value.quotient.bitLength +
        2 * xgcdCoefficientBitBound
          right division.value.remainder + 1
  | left, right@(.neg _) =>
      let division := divModWithCost left right
      division.value.quotient.bitLength +
        2 * xgcdCoefficientBitBound
          right division.value.remainder + 1
termination_by _ right => right.value.natAbs
decreasing_by
  all_goals
    subst right
    apply divModWithCost_remainder_measure_lt
    simp

namespace Internal

/-- One coefficient update preserves the recursive width budget. -/
public theorem xgcdStep_coefficient_bitLength_le
    (division : WithCost DivModResult)
    (recursive : WithCost XGCDResult)
    (recursiveBound : Nat)
    (recursiveWidths :
      recursive.value.leftCoeff.bitLength ≤ recursiveBound ∧
        recursive.value.rightCoeff.bitLength ≤ recursiveBound) :
    (xgcdStep division recursive).value.leftCoeff.bitLength ≤
        division.value.quotient.bitLength +
          2 * recursiveBound + 1 ∧
      (xgcdStep division recursive).value.rightCoeff.bitLength ≤
        division.value.quotient.bitLength +
          2 * recursiveBound + 1 := by
  let product :=
    mulWithCost division.value.quotient
      recursive.value.rightCoeff
  let adjusted :=
    addWithCost recursive.value.leftCoeff (-product.value)
  constructor
  · change recursive.value.rightCoeff.bitLength ≤
      division.value.quotient.bitLength +
        2 * recursiveBound + 1
    omega
  · change adjusted.value.bitLength ≤
      division.value.quotient.bitLength +
        2 * recursiveBound + 1
    have productWidth :
        product.value.bitLength ≤
          division.value.quotient.bitLength +
            recursive.value.rightCoeff.bitLength := by
      simpa only [product] using
        mulWithCost_value_bitLength_le
          division.value.quotient recursive.value.rightCoeff
    have adjustedWidth :
        adjusted.value.bitLength ≤
          recursive.value.leftCoeff.bitLength +
            product.value.bitLength + 1 := by
      simpa only [adjusted, SignMagnitude.bitLength_neg] using
        addWithCost_value_bitLength_le
          recursive.value.leftCoeff (-product.value)
    omega

end Internal

/-- The costed loop returns the normalized integer gcd and Bézout witnesses. -/
public theorem xgcdWithCost_spec
    (left right : SignMagnitude) :
    XGCDSpecification left right
      (xgcdWithCost left right).value := by
  induction left, right using xgcdWithCost.induct with
  | case1 left =>
      rw [xgcdWithCost]
      exact Internal.xgcdBase_spec left
  | case2 left magnitude _division ih =>
      rw [xgcdWithCost]
      exact Internal.xgcdStep_spec left (.pos magnitude) _ ih
  | case3 left magnitude _division ih =>
      rw [xgcdWithCost]
      exact Internal.xgcdStep_spec left (.neg magnitude) _ ih

/-- The returned gcd is the standard nonnegative integer gcd. -/
public theorem xgcdWithCost_gcd_value
    (left right : SignMagnitude) :
    (xgcdWithCost left right).value.gcd.value =
      (left.value.gcd right.value : Nat) :=
  (xgcdWithCost_spec left right).gcd_value

/-- The returned coefficients satisfy the Bézout identity. -/
public theorem xgcdWithCost_bezout
    (left right : SignMagnitude) :
    (xgcdWithCost left right).value.leftCoeff.value * left.value +
        (xgcdWithCost left right).value.rightCoeff.value * right.value =
      (xgcdWithCost left right).value.gcd.value :=
  (xgcdWithCost_spec left right).bezout

/-- The normalized gcd is nonnegative. -/
public theorem xgcdWithCost_gcd_nonnegative
    (left right : SignMagnitude) :
    0 ≤ (xgcdWithCost left right).value.gcd.value := by
  rw [xgcdWithCost_gcd_value]
  exact Int.natCast_nonneg _

/-- Both Bézout coefficients satisfy the path-sensitive bit-length budget. -/
public theorem xgcdWithCost_coefficient_bitLength_le
    (left right : SignMagnitude) :
    (xgcdWithCost left right).value.leftCoeff.bitLength ≤
        xgcdCoefficientBitBound left right ∧
      (xgcdWithCost left right).value.rightCoeff.bitLength ≤
        xgcdCoefficientBitBound left right := by
  induction left, right using xgcdWithCost.induct with
  | case1 left =>
      rw [xgcdWithCost, xgcdCoefficientBitBound]
      cases left with
      | zero | pos _ =>
          change
            (1 : SignMagnitude).bitLength ≤ 1 ∧
              (0 : SignMagnitude).bitLength ≤ 1
          exact ⟨by rfl, by decide⟩
      | neg _ =>
          change
            (-1 : SignMagnitude).bitLength ≤ 1 ∧
              (0 : SignMagnitude).bitLength ≤ 1
          exact ⟨by decide, by decide⟩
  | case2 left magnitude _division ih =>
      rw [xgcdWithCost, xgcdCoefficientBitBound]
      exact Internal.xgcdStep_coefficient_bitLength_le _ _
        (xgcdCoefficientBitBound (.pos magnitude)
          (divModWithCost left (.pos magnitude)).value.remainder) ih
  | case3 left magnitude _division ih =>
      rw [xgcdWithCost, xgcdCoefficientBitBound]
      exact Internal.xgcdStep_coefficient_bitLength_le _ _
        (xgcdCoefficientBitBound (.neg magnitude)
          (divModWithCost left (.neg magnitude)).value.remainder) ih

/-- Addition budget expressed only in operand bit lengths. -/
@[expose] public def additionCostForBitLengths
    (leftBits rightBits : Nat) : Nat :=
  1 + 2 * (leftBits + rightBits + 1) ^ 2

/-- Schoolbook multiplication budget expressed only in operand bit lengths. -/
@[expose] public def multiplicationCostForBitLengths
    (leftBits rightBits : Nat) : Nat :=
  1 + rightBits *
    (1 + (2 * leftBits + rightBits + 2) ^ 2)

namespace Internal

/-- The concrete addition budget is monotone in both bit lengths. -/
public theorem addBitOperationBound_le_lengths
    (left right : SignMagnitude) (leftBits rightBits : Nat)
    (leftWidth : left.bitLength ≤ leftBits)
    (rightWidth : right.bitLength ≤ rightBits) :
    addBitOperationBound left right ≤
      additionCostForBitLengths leftBits rightBits := by
  have baseWidth :
      left.bitLength + right.bitLength + 1 ≤
        leftBits + rightBits + 1 := by
    omega
  have squareWidth := Nat.pow_le_pow_left baseWidth 2
  simp only [addBitOperationBound, additionCostForBitLengths]
  omega

/-- The concrete multiplication budget is monotone in both bit lengths. -/
public theorem mulBitOperationBound_le_lengths
    (left right : SignMagnitude) (leftBits rightBits : Nat)
    (leftWidth : left.bitLength ≤ leftBits)
    (rightWidth : right.bitLength ≤ rightBits) :
    mulBitOperationBound left right ≤
      multiplicationCostForBitLengths leftBits rightBits := by
  have baseWidth :
      2 * left.bitLength + right.bitLength + 2 ≤
        2 * leftBits + rightBits + 2 := by
    omega
  have squareWidth := Nat.pow_le_pow_left baseWidth 2
  have factorWidth :
      1 + (2 * left.bitLength + right.bitLength + 2) ^ 2 ≤
        1 + (2 * leftBits + rightBits + 2) ^ 2 :=
    Nat.add_le_add_left squareWidth 1
  simp only [mulBitOperationBound,
    multiplicationCostForBitLengths]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul rightWidth factorWidth) 1

end Internal

/--
Input-path bit-operation budget for extended gcd.

The function follows only the Euclidean quotient sequence. Primitive budgets
are instantiated from quotient length and the independently proved recursive
coefficient-width bound; it does not inspect the computed Bézout coefficients.
-/
@[expose] public def xgcdBitOperationBound :
    SignMagnitude → SignMagnitude → Nat
  | _, .zero => 1
  | left, right@(.pos _) =>
      let division := divModWithCost left right
      let recursiveCoefficientBound :=
        xgcdCoefficientBitBound right division.value.remainder
      1 + divModBitOperationBound left right +
        xgcdBitOperationBound right division.value.remainder +
        multiplicationCostForBitLengths
          division.value.quotient.bitLength recursiveCoefficientBound +
        additionCostForBitLengths recursiveCoefficientBound
          (division.value.quotient.bitLength +
            recursiveCoefficientBound)
  | left, right@(.neg _) =>
      let division := divModWithCost left right
      let recursiveCoefficientBound :=
        xgcdCoefficientBitBound right division.value.remainder
      1 + divModBitOperationBound left right +
        xgcdBitOperationBound right division.value.remainder +
        multiplicationCostForBitLengths
          division.value.quotient.bitLength recursiveCoefficientBound +
        additionCostForBitLengths recursiveCoefficientBound
          (division.value.quotient.bitLength +
            recursiveCoefficientBound)
termination_by _ right => right.value.natAbs
decreasing_by
  all_goals
    subst right
    apply divModWithCost_remainder_measure_lt
    simp

namespace Internal

/-- One extended-Euclidean update respects its composed primitive budget. -/
public theorem xgcdStep_cost_le
    (left right : SignMagnitude)
    (recursive : WithCost XGCDResult)
    (recursiveCoefficientBound recursiveCostBound : Nat)
    (recursiveWidths :
      recursive.value.leftCoeff.bitLength ≤
          recursiveCoefficientBound ∧
        recursive.value.rightCoeff.bitLength ≤
          recursiveCoefficientBound)
    (recursiveCost : recursive.cost ≤ recursiveCostBound) :
    (xgcdStep (divModWithCost left right) recursive).cost ≤
      1 + divModBitOperationBound left right +
        recursiveCostBound +
        multiplicationCostForBitLengths
          (divModWithCost left right).value.quotient.bitLength
          recursiveCoefficientBound +
        additionCostForBitLengths recursiveCoefficientBound
          ((divModWithCost left right).value.quotient.bitLength +
            recursiveCoefficientBound) := by
  let division := divModWithCost left right
  let product :=
    mulWithCost division.value.quotient
      recursive.value.rightCoeff
  let adjusted :=
    addWithCost recursive.value.leftCoeff (-product.value)
  have divisionCost :
      division.cost ≤ divModBitOperationBound left right := by
    simpa only [division] using
      divModWithCost_cost_le left right
  have productPrimitiveCost :=
    mulWithCost_cost_le division.value.quotient
      recursive.value.rightCoeff
  have productCost :
      product.cost ≤
        multiplicationCostForBitLengths
          division.value.quotient.bitLength
          recursiveCoefficientBound := by
    exact (by
      simpa only [product] using productPrimitiveCost.trans
        (mulBitOperationBound_le_lengths
          division.value.quotient recursive.value.rightCoeff
          division.value.quotient.bitLength
          recursiveCoefficientBound (by rfl) recursiveWidths.2))
  have productWidth :=
    mulWithCost_value_bitLength_le division.value.quotient
      recursive.value.rightCoeff
  have productWidth' :
      product.value.bitLength ≤
        division.value.quotient.bitLength +
          recursiveCoefficientBound := by
    simpa only [product] using
      productWidth.trans
        (Nat.add_le_add_left recursiveWidths.2
          division.value.quotient.bitLength)
  have adjustedPrimitiveCost :=
    addWithCost_cost_le recursive.value.leftCoeff (-product.value)
  have adjustedCost :
      adjusted.cost ≤
        additionCostForBitLengths recursiveCoefficientBound
          (division.value.quotient.bitLength +
            recursiveCoefficientBound) := by
    have bound :=
      addBitOperationBound_le_lengths
        recursive.value.leftCoeff (-product.value)
        recursiveCoefficientBound
        (division.value.quotient.bitLength +
          recursiveCoefficientBound)
        recursiveWidths.1
        (by simpa only [SignMagnitude.bitLength_neg] using productWidth')
    simpa only [adjusted] using adjustedPrimitiveCost.trans bound
  change
    1 + division.cost + recursive.cost +
        product.cost + adjusted.cost ≤
      1 + divModBitOperationBound left right +
        recursiveCostBound +
        multiplicationCostForBitLengths
          division.value.quotient.bitLength
          recursiveCoefficientBound +
        additionCostForBitLengths recursiveCoefficientBound
          (division.value.quotient.bitLength +
            recursiveCoefficientBound)
  omega

end Internal

/-- The exact accumulated extended-gcd cost is bounded in bit operations. -/
public theorem xgcdWithCost_cost_le
    (left right : SignMagnitude) :
    (xgcdWithCost left right).cost ≤
      xgcdBitOperationBound left right := by
  induction left, right using xgcdWithCost.induct with
  | case1 left =>
      rw [xgcdWithCost, xgcdBitOperationBound]
  | case2 left magnitude _division ih =>
      rw [xgcdWithCost, xgcdBitOperationBound]
      apply Internal.xgcdStep_cost_le
      · exact xgcdWithCost_coefficient_bitLength_le
          (.pos magnitude)
          (divModWithCost left (.pos magnitude)).value.remainder
      · exact ih
  | case3 left magnitude _division ih =>
      rw [xgcdWithCost, xgcdBitOperationBound]
      apply Internal.xgcdStep_cost_le
      · exact xgcdWithCost_coefficient_bitLength_le
          (.neg magnitude)
          (divModWithCost left (.neg magnitude)).value.remainder
      · exact ih

end NormalForms.Research.BitCost
