/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.Comparison
public import NormalForms.Research.BitCost.EuclideanIterations

/-!
# Costed Extended GCD with Bounded Intermediate Coefficients

After every Euclidean coefficient update, this reference implementation
reduces one Bezout coefficient modulo the larger nonzero input and adjusts the
other coefficient to preserve the identity.  This is the Appendix reduction
used by Kannan--Bachem, applied at every recursive level so that intermediate
as well as final coefficients remain size-controlled.
-/

public section

namespace NormalForms.Research.BitCost

/-- Closed magnitude envelope for a reduced pair of Bezout coefficients. -/
@[expose] public def boundedXGCDCoefficientHeight
    (left right : SignMagnitude) : Nat :=
  (max left.value.natAbs right.value.natAbs + 1) ^ 2

namespace Internal

/-- The Appendix reduction value, separated from its costed control flow. -/
@[expose] public def reduceBezoutValue
    (left right : SignMagnitude) (raw : XGCDResult) : XGCDResult :=
  if _main : left ≠ 0 ∧ right.value.natAbs ≤ left.value.natAbs then
    let division := divModWithCost raw.rightCoeff left
    let product := mulWithCost division.value.quotient right
    let adjusted := addWithCost raw.leftCoeff product.value
    { gcd := raw.gcd
      leftCoeff := adjusted.value
      rightCoeff := division.value.remainder }
  else if _rightNonzero : right ≠ 0 then
    let division := divModWithCost raw.leftCoeff right
    let product := mulWithCost division.value.quotient left
    let adjusted := addWithCost raw.rightCoeff product.value
    { gcd := raw.gcd
      leftCoeff := division.value.remainder
      rightCoeff := adjusted.value }
  else
    { gcd := raw.gcd
      leftCoeff := 1
      rightCoeff := 0 }

/-- One costed Appendix reduction of an already valid Bezout result. -/
@[expose] public def reduceBezoutWithCost
    (left right : SignMagnitude) (raw : XGCDResult) :
    WithCost XGCDResult :=
  let leftZero := isZeroWithCost left
  if leftZero.value then
    let rightZero := isZeroWithCost right
    if rightZero.value then
      { value :=
          { gcd := raw.gcd
            leftCoeff := 1
            rightCoeff := 0 }
        cost := leftZero.cost + rightZero.cost }
    else
      let division := divModWithCost raw.leftCoeff right
      let product := mulWithCost division.value.quotient left
      let adjusted := addWithCost raw.rightCoeff product.value
      { value :=
          { gcd := raw.gcd
            leftCoeff := division.value.remainder
            rightCoeff := adjusted.value }
        cost := leftZero.cost + rightZero.cost +
          division.cost + product.cost + adjusted.cost }
  else
    let comparison := magnitudeLeWithCost right left
    if comparison.value then
      let division := divModWithCost raw.rightCoeff left
      let product := mulWithCost division.value.quotient right
      let adjusted := addWithCost raw.leftCoeff product.value
      { value :=
          { gcd := raw.gcd
            leftCoeff := adjusted.value
            rightCoeff := division.value.remainder }
        cost := leftZero.cost + comparison.cost +
          division.cost + product.cost + adjusted.cost }
    else
      let division := divModWithCost raw.leftCoeff right
      let product := mulWithCost division.value.quotient left
      let adjusted := addWithCost raw.rightCoeff product.value
      { value :=
          { gcd := raw.gcd
            leftCoeff := division.value.remainder
            rightCoeff := adjusted.value }
        cost := leftZero.cost + comparison.cost +
          division.cost + product.cost + adjusted.cost }

@[simp] public theorem reduceBezoutWithCost_value
    (left right : SignMagnitude) (raw : XGCDResult) :
    (reduceBezoutWithCost left right raw).value =
      reduceBezoutValue left right raw := by
  by_cases leftZero : left = 0
  · subst left
    by_cases rightZero : right = 0
    · subst right
      simp [reduceBezoutWithCost, reduceBezoutValue]
    · have rightValueNonzero : right.value ≠ 0 := by
        intro valueZero
        apply rightZero
        rw [← SignMagnitude.ofInt_value right, valueZero]
        rfl
      simp [reduceBezoutWithCost, reduceBezoutValue, rightZero,
        rightValueNonzero]
  · have leftValueNonzero : left.value ≠ 0 := by
      intro valueZero
      apply leftZero
      rw [← SignMagnitude.ofInt_value left, valueZero]
      rfl
    by_cases magnitudeLe : right.value.natAbs ≤ left.value.natAbs
    · simp [reduceBezoutWithCost, reduceBezoutValue, leftZero,
        leftValueNonzero, magnitudeLe]
    · have rightNonzero : right ≠ 0 := by
        intro equality
        subst right
        simp at magnitudeLe
      simp [reduceBezoutWithCost, reduceBezoutValue, leftZero,
        leftValueNonzero, magnitudeLe, rightNonzero]

/-- Appendix reduction preserves both gcd and the Bezout equation. -/
public theorem reduceBezoutWithCost_spec
    (left right : SignMagnitude) (raw : XGCDResult)
    (rawSpec : XGCDSpecification left right raw) :
    XGCDSpecification left right
      (reduceBezoutWithCost left right raw).value := by
  constructor
  · rw [reduceBezoutWithCost_value]
    simp only [reduceBezoutValue]
    split
    · exact rawSpec.gcd_value
    · split <;> exact rawSpec.gcd_value
  · by_cases main : left ≠ 0 ∧ right.value.natAbs ≤ left.value.natAbs
    · let division := divModWithCost raw.rightCoeff left
      have divisionEquation :
          division.value.quotient.value * left.value +
              division.value.remainder.value = raw.rightCoeff.value := by
        rw [divModWithCost_quotient_value,
          divModWithCost_remainder_value]
        exact Int.ediv_mul_add_emod raw.rightCoeff.value left.value
      simp only [reduceBezoutWithCost_value, reduceBezoutValue, dif_pos main,
        addWithCost_value, mulWithCost_value]
      change
        (raw.leftCoeff.value +
            division.value.quotient.value * right.value) * left.value +
            division.value.remainder.value * right.value = raw.gcd.value
      calc
        (raw.leftCoeff.value +
              division.value.quotient.value * right.value) * left.value +
              division.value.remainder.value * right.value =
            raw.leftCoeff.value * left.value +
              (division.value.quotient.value * left.value +
                division.value.remainder.value) * right.value := by ring
        _ = raw.leftCoeff.value * left.value +
              raw.rightCoeff.value * right.value := by rw [divisionEquation]
        _ = raw.gcd.value := rawSpec.bezout
    · by_cases rightNonzero : right ≠ 0
      · let division := divModWithCost raw.leftCoeff right
        have divisionEquation :
            division.value.quotient.value * right.value +
                division.value.remainder.value = raw.leftCoeff.value := by
          rw [divModWithCost_quotient_value,
            divModWithCost_remainder_value]
          exact Int.ediv_mul_add_emod raw.leftCoeff.value right.value
        simp only [reduceBezoutWithCost_value, reduceBezoutValue, dif_neg main,
          dif_pos rightNonzero, addWithCost_value, mulWithCost_value]
        change
          division.value.remainder.value * left.value +
              (raw.rightCoeff.value +
                division.value.quotient.value * left.value) * right.value =
            raw.gcd.value
        calc
          division.value.remainder.value * left.value +
                (raw.rightCoeff.value +
                  division.value.quotient.value * left.value) * right.value =
              (division.value.quotient.value * right.value +
                  division.value.remainder.value) * left.value +
                raw.rightCoeff.value * right.value := by ring
          _ = raw.leftCoeff.value * left.value +
                raw.rightCoeff.value * right.value := by rw [divisionEquation]
          _ = raw.gcd.value := rawSpec.bezout
      · have rightZero : right = 0 := not_ne_iff.mp rightNonzero
        have leftZero : left = 0 := by
          by_contra leftNonzero
          exact main ⟨leftNonzero, by simp [rightZero]⟩
        subst left
        subst right
        have gcdZero : raw.gcd.value = 0 := by
          simpa using rawSpec.gcd_value
        simp [reduceBezoutWithCost_value, reduceBezoutValue, gcdZero]

theorem natAbs_le_natAbs_mul_of_ne_zero
    (left right : Int) (leftNonzero : left ≠ 0) :
    right.natAbs ≤ (left * right).natAbs := by
  rw [Int.natAbs_mul]
  exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr leftNonzero)

/-- Both output coefficients satisfy the Appendix magnitude envelope. -/
public theorem reduceBezoutWithCost_coefficient_natAbs_le
    (left right : SignMagnitude) (raw : XGCDResult)
    (rawSpec : XGCDSpecification left right raw) :
    (reduceBezoutWithCost left right raw).value.leftCoeff.value.natAbs ≤
        boundedXGCDCoefficientHeight left right ∧
      (reduceBezoutWithCost left right raw).value.rightCoeff.value.natAbs ≤
        boundedXGCDCoefficientHeight left right := by
  let height := max left.value.natAbs right.value.natAbs
  have leftHeight : left.value.natAbs ≤ height := le_max_left _ _
  have rightHeight : right.value.natAbs ≤ height := le_max_right _ _
  have bezout := (reduceBezoutWithCost_spec left right raw rawSpec).bezout
  by_cases main : left ≠ 0 ∧ right.value.natAbs ≤ left.value.natAbs
  · let reduced := reduceBezoutWithCost left right raw
    let newLeft := reduced.value.leftCoeff.value
    let newRight := reduced.value.rightCoeff.value
    have leftValueNonzero : left.value ≠ 0 := by
      intro valueZero
      apply main.1
      rw [← SignMagnitude.ofInt_value left, valueZero]
      rfl
    have rightEquation :
        newRight = raw.rightCoeff.value % left.value := by
      simp [newRight, reduced, reduceBezoutWithCost_value,
        reduceBezoutValue, main,
        divModWithCost_remainder_value]
    have rightLt : newRight.natAbs < left.value.natAbs := by
      rw [rightEquation]
      apply Int.ofNat_lt.mp
      rw [Int.natCast_natAbs, Int.natCast_natAbs,
        abs_of_nonneg (Int.emod_nonneg _ leftValueNonzero)]
      exact Int.emod_lt_abs raw.rightCoeff.value leftValueNonzero
    have reducedBezout :
        newLeft * left.value + newRight * right.value = raw.gcd.value := by
      have gcdEquation : reduced.value.gcd.value = raw.gcd.value := by
        simp [reduced, reduceBezoutWithCost_value, reduceBezoutValue, main]
      rw [gcdEquation] at bezout
      simpa [reduced, newLeft, newRight] using bezout
    have productEquation :
        left.value * newLeft = raw.gcd.value - right.value * newRight := by
      nlinarith
    have gcdLe : (left.value.gcd right.value) ≤ left.value.natAbs :=
      Int.gcd_le_natAbs_left right.value leftValueNonzero
    have gcdAbs : raw.gcd.value.natAbs = left.value.gcd right.value := by
      rw [rawSpec.gcd_value, Int.natAbs_natCast]
    have productBound : (left.value * newLeft).natAbs ≤
        height + height * height := by
      rw [productEquation]
      exact (Int.natAbs_sub_le _ _).trans <| by
        rw [Int.natAbs_mul, gcdAbs]
        exact Nat.add_le_add (gcdLe.trans leftHeight) <|
          Nat.mul_le_mul rightHeight (rightLt.le.trans leftHeight)
    have newLeftBound : newLeft.natAbs ≤ (height + 1) ^ 2 :=
      (natAbs_le_natAbs_mul_of_ne_zero left.value newLeft
        leftValueNonzero).trans <| by
          calc
            (left.value * newLeft).natAbs ≤
                height + height * height := productBound
            _ ≤ (height + 1) ^ 2 := by nlinarith
    have newRightBound : newRight.natAbs ≤ (height + 1) ^ 2 :=
      (rightLt.le.trans leftHeight).trans (by nlinarith)
    simpa only [boundedXGCDCoefficientHeight, height, reduced,
      newLeft, newRight] using And.intro newLeftBound newRightBound
  · by_cases rightNonzero : right ≠ 0
    · let reduced := reduceBezoutWithCost left right raw
      let newLeft := reduced.value.leftCoeff.value
      let newRight := reduced.value.rightCoeff.value
      have rightValueNonzero : right.value ≠ 0 := by
        intro valueZero
        apply rightNonzero
        rw [← SignMagnitude.ofInt_value right, valueZero]
        rfl
      have leftEquation :
          newLeft = raw.leftCoeff.value % right.value := by
        simp [newLeft, reduced, reduceBezoutWithCost_value,
          reduceBezoutValue, main, rightNonzero,
          divModWithCost_remainder_value]
      have leftLt : newLeft.natAbs < right.value.natAbs := by
        rw [leftEquation]
        apply Int.ofNat_lt.mp
        rw [Int.natCast_natAbs, Int.natCast_natAbs,
          abs_of_nonneg (Int.emod_nonneg _ rightValueNonzero)]
        exact Int.emod_lt_abs raw.leftCoeff.value rightValueNonzero
      have reducedBezout :
          newLeft * left.value + newRight * right.value = raw.gcd.value := by
        have gcdEquation : reduced.value.gcd.value = raw.gcd.value := by
          simp [reduced, reduceBezoutWithCost_value,
            reduceBezoutValue, main, rightNonzero]
        rw [gcdEquation] at bezout
        simpa [reduced, newLeft, newRight] using bezout
      have productEquation :
          right.value * newRight = raw.gcd.value - left.value * newLeft := by
        nlinarith
      have gcdLe : (left.value.gcd right.value) ≤ right.value.natAbs :=
        Int.gcd_le_natAbs_right left.value rightValueNonzero
      have gcdAbs : raw.gcd.value.natAbs = left.value.gcd right.value := by
        rw [rawSpec.gcd_value, Int.natAbs_natCast]
      have productBound : (right.value * newRight).natAbs ≤
          height + height * height := by
        rw [productEquation]
        exact (Int.natAbs_sub_le _ _).trans <| by
          rw [Int.natAbs_mul, gcdAbs]
          exact Nat.add_le_add (gcdLe.trans rightHeight) <|
            Nat.mul_le_mul leftHeight (leftLt.le.trans rightHeight)
      have newRightBound : newRight.natAbs ≤ (height + 1) ^ 2 :=
        (natAbs_le_natAbs_mul_of_ne_zero right.value newRight
          rightValueNonzero).trans <| by
            calc
              (right.value * newRight).natAbs ≤
                  height + height * height := productBound
              _ ≤ (height + 1) ^ 2 := by nlinarith
      have newLeftBound : newLeft.natAbs ≤ (height + 1) ^ 2 :=
        (leftLt.le.trans rightHeight).trans (by nlinarith)
      simpa only [boundedXGCDCoefficientHeight, height, reduced,
        newLeft, newRight] using And.intro newLeftBound newRightBound
    · have rightZero : right = 0 := not_ne_iff.mp rightNonzero
      have leftZero : left = 0 := by
        by_contra leftNonzero
        exact main ⟨leftNonzero, by simp [rightZero]⟩
      subst left
      subst right
      norm_num [reduceBezoutWithCost_value, reduceBezoutValue,
        boundedXGCDCoefficientHeight,
        SignMagnitude.value]

end Internal

/--
Extended Euclid with Appendix reduction after every nonterminal coefficient
update.  The returned cost is the exact sum of all reference primitive costs.
-/
@[expose] public def boundedEuclideanXGCDWithCost :
    SignMagnitude → SignMagnitude → WithCost XGCDResult
  | left, .zero =>
      { value := Internal.xgcdBase left, cost := 1 }
  | left, right@(.pos _) =>
      let division := divModWithCost left right
      let recursive :=
        boundedEuclideanXGCDWithCost right division.value.remainder
      let raw := Internal.xgcdStep division recursive
      let reduced := Internal.reduceBezoutWithCost left right raw.value
      { value := reduced.value, cost := raw.cost + reduced.cost }
  | left, right@(.neg _) =>
      let division := divModWithCost left right
      let recursive :=
        boundedEuclideanXGCDWithCost right division.value.remainder
      let raw := Internal.xgcdStep division recursive
      let reduced := Internal.reduceBezoutWithCost left right raw.value
      { value := reduced.value, cost := raw.cost + reduced.cost }
termination_by _ right => right.value.natAbs
decreasing_by
  all_goals
    subst right
    apply divModWithCost_remainder_measure_lt
    simp

/-- The per-level reduced Euclidean loop satisfies the standard specification. -/
public theorem boundedEuclideanXGCDWithCost_spec
    (left right : SignMagnitude) :
    XGCDSpecification left right
      (boundedEuclideanXGCDWithCost left right).value := by
  induction left, right using boundedEuclideanXGCDWithCost.induct with
  | case1 left =>
      rw [boundedEuclideanXGCDWithCost]
      exact Internal.xgcdBase_spec left
  | case2 left magnitude _division ih =>
      rw [boundedEuclideanXGCDWithCost]
      apply Internal.reduceBezoutWithCost_spec
      exact Internal.xgcdStep_spec left (.pos magnitude) _ ih
  | case3 left magnitude _division ih =>
      rw [boundedEuclideanXGCDWithCost]
      apply Internal.reduceBezoutWithCost_spec
      exact Internal.xgcdStep_spec left (.neg magnitude) _ ih

/-- Every returned pair, including every recursive pair, is reduced. -/
public theorem boundedEuclideanXGCDWithCost_coefficient_natAbs_le
    (left right : SignMagnitude) :
    (boundedEuclideanXGCDWithCost left right).value.leftCoeff.value.natAbs ≤
        boundedXGCDCoefficientHeight left right ∧
      (boundedEuclideanXGCDWithCost left right).value.rightCoeff.value.natAbs ≤
        boundedXGCDCoefficientHeight left right := by
  cases right with
  | zero =>
      cases left with
      | zero =>
          norm_num [boundedEuclideanXGCDWithCost, Internal.xgcdBase,
            boundedXGCDCoefficientHeight, SignMagnitude.value]
      | pos magnitude =>
          rw [boundedEuclideanXGCDWithCost]
          change
            1 ≤ (max (magnitude : Int).natAbs 0 + 1) ^ 2 ∧
              0 ≤ (max (magnitude : Int).natAbs 0 + 1) ^ 2
          exact ⟨Nat.one_le_pow 2 _ (Nat.succ_pos _), Nat.zero_le _⟩
      | neg magnitude =>
          rw [boundedEuclideanXGCDWithCost]
          change
            1 ≤ (max (-(magnitude : Int)).natAbs 0 + 1) ^ 2 ∧
              0 ≤ (max (-(magnitude : Int)).natAbs 0 + 1) ^ 2
          exact ⟨Nat.one_le_pow 2 _ (Nat.succ_pos _), Nat.zero_le _⟩
  | pos magnitude =>
      rw [boundedEuclideanXGCDWithCost]
      apply Internal.reduceBezoutWithCost_coefficient_natAbs_le
      exact Internal.xgcdStep_spec _ _ _
        (boundedEuclideanXGCDWithCost_spec _ _)
  | neg magnitude =>
      rw [boundedEuclideanXGCDWithCost]
      apply Internal.reduceBezoutWithCost_coefficient_natAbs_le
      exact Internal.xgcdStep_spec _ _ _
        (boundedEuclideanXGCDWithCost_spec _ _)

/-- Sign-normalized, per-level reduced extended gcd for arbitrary integers. -/
@[expose] public def boundedXGCDWithCost
    (left right : SignMagnitude) : WithCost XGCDResult :=
  let raw := boundedEuclideanXGCDWithCost
    left.nonnegative right.nonnegative
  { value :=
      { gcd := raw.value.gcd
        leftCoeff := left.restoreCoefficientSign raw.value.leftCoeff
        rightCoeff := right.restoreCoefficientSign raw.value.rightCoeff }
    cost := 2 + raw.cost }

/-- The bounded signed wrapper returns the standard gcd and Bezout witnesses. -/
public theorem boundedXGCDWithCost_spec
    (left right : SignMagnitude) :
    XGCDSpecification left right
      (boundedXGCDWithCost left right).value := by
  let raw := boundedEuclideanXGCDWithCost
    left.nonnegative right.nonnegative
  have rawSpec := boundedEuclideanXGCDWithCost_spec
    left.nonnegative right.nonnegative
  constructor
  · change raw.value.gcd.value = (left.value.gcd right.value : Nat)
    rw [rawSpec.gcd_value]
    simp only [Int.gcd_def, SignMagnitude.nonnegative_value,
      Int.natAbs_natCast]
  · change
      (left.restoreCoefficientSign raw.value.leftCoeff).value * left.value +
          (right.restoreCoefficientSign raw.value.rightCoeff).value * right.value =
        raw.value.gcd.value
    rw [SignMagnitude.restoreCoefficientSign_mul_value,
      SignMagnitude.restoreCoefficientSign_mul_value]
    exact rawSpec.bezout

/-- The final signed coefficients inherit the same polynomial magnitude bound. -/
public theorem boundedXGCDWithCost_coefficient_natAbs_le
    (left right : SignMagnitude) :
    (boundedXGCDWithCost left right).value.leftCoeff.value.natAbs ≤
        boundedXGCDCoefficientHeight left right ∧
      (boundedXGCDWithCost left right).value.rightCoeff.value.natAbs ≤
        boundedXGCDCoefficientHeight left right := by
  have rawBound := boundedEuclideanXGCDWithCost_coefficient_natAbs_le
    left.nonnegative right.nonnegative
  have heightEquation :
      boundedXGCDCoefficientHeight left.nonnegative right.nonnegative =
        boundedXGCDCoefficientHeight left right := by
    unfold boundedXGCDCoefficientHeight
    rw [SignMagnitude.nonnegative_value_natAbs,
      SignMagnitude.nonnegative_value_natAbs]
  rw [heightEquation] at rawBound
  simpa only [boundedXGCDWithCost,
    SignMagnitude.restoreCoefficientSign_value_natAbs] using rawBound

end NormalForms.Research.BitCost
