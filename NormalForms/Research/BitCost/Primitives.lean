/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.BoundedXGCDCost
public import NormalForms.Matrix.Certificates.Basic
public import NormalForms.Matrix.Constructive
public import NormalForms.Euclidean.ComputableOps
public import NormalForms.Euclidean.Int

/-!
# Value-producing Binary Arithmetic Primitives

These combinators expose the values that drive the instrumented
Kannan--Bachem execution.  Costs are accumulated only from the underlying
binary primitives; quotient, exact division, divisibility, and the bounded
Bézout block do not add aggregate parent charges.
-/

public section

namespace NormalForms.Research.BitCost

open scoped Matrix
open NormalForms.Matrix.Certificates

/-- Total quotient projected from one shared quotient/remainder execution. -/
@[expose] public def quotientWithCost
    (numerator divisor : SignMagnitude) : WithCost SignMagnitude :=
  let run := divModWithCost numerator divisor
  { value := run.value.quotient, cost := run.cost }

@[simp] public theorem quotientWithCost_value
    (numerator divisor : SignMagnitude) :
    (quotientWithCost numerator divisor).value.value =
      numerator.value / divisor.value :=
  divModWithCost_quotient_value numerator divisor

/--
Exact quotient projected from a shared long-division run.  The hypotheses are
contracts for callers; the combinator owns no extra cost.
-/
@[expose] public def exactDivWithCost
    (numerator divisor : SignMagnitude)
    (_divisor_ne_zero : divisor.value ≠ 0)
    (_divides : divisor.value ∣ numerator.value) :
    WithCost SignMagnitude :=
  quotientWithCost numerator divisor

@[simp] public theorem exactDivWithCost_value
    (numerator divisor : SignMagnitude)
    (divisor_ne_zero : divisor.value ≠ 0)
    (divides : divisor.value ∣ numerator.value) :
    (exactDivWithCost numerator divisor divisor_ne_zero divides).value.value =
      numerator.value / divisor.value :=
  quotientWithCost_value numerator divisor

set_option linter.unusedVariables false in
public theorem exactDivWithCost_remainder_eq_zero
    (numerator divisor : SignMagnitude)
    (divisor_ne_zero : divisor.value ≠ 0)
    (divides : divisor.value ∣ numerator.value) :
    (divModWithCost numerator divisor).value.remainder.value = 0 := by
  rw [divModWithCost_remainder_value]
  exact Int.emod_eq_zero_of_dvd divides

/--
Costed divisibility.  A nonzero divisor performs exactly one long division;
the zero-divisor branch performs only the two required zero inspections.
-/
@[expose] public def dvdWithCost
    (divisor dividend : SignMagnitude) : WithCost Bool :=
  let divisorZero := isZeroWithCost divisor
  if divisorZero.value then
    let dividendZero := isZeroWithCost dividend
    { value := dividendZero.value
      cost := divisorZero.cost + dividendZero.cost }
  else
    let division := divModWithCost dividend divisor
    let remainderZero := isZeroWithCost division.value.remainder
    { value := remainderZero.value
      cost := divisorZero.cost + division.cost + remainderZero.cost }

@[simp] public theorem dvdWithCost_value
    (divisor dividend : SignMagnitude) :
    (dvdWithCost divisor dividend).value =
      decide (divisor.value ∣ dividend.value) := by
  by_cases divisorZero : divisor.value = 0
  · have zeroRun : (isZeroWithCost divisor).value = true := by
      simp [divisorZero]
    rw [dvdWithCost, if_pos zeroRun]
    simp [divisorZero]
  · have nonzeroRun : (isZeroWithCost divisor).value = false := by
      simp [divisorZero]
    rw [dvdWithCost, if_neg (by simpa using nonzeroRun)]
    rw [isZeroWithCost_value, divModWithCost_remainder_value]
    simp only [decide_eq_decide]
    exact Int.dvd_iff_emod_eq_zero.symm

/-- Costed production of the canonical integer normalization unit. -/
@[expose] public def normalizationUnitWithCost
    (value : SignMagnitude) : WithCost Intˣ :=
  { value := ComputableEuclideanOps.normUnitUnit value.value, cost := 1 }

@[simp] public theorem normalizationUnitWithCost_cost
    (value : SignMagnitude) :
    (normalizationUnitWithCost value).cost = 1 :=
  rfl

/-- Compatibility projection returning the normalized integer value. -/
@[expose] public def normalizeWithCost
    (value : SignMagnitude) : WithCost SignMagnitude :=
  { value := SignMagnitude.ofInt (_root_.normalize value.value), cost := 1 }

@[simp] public theorem normalizeWithCost_value (value : SignMagnitude) :
    (normalizeWithCost value).value.value = _root_.normalize value.value := by
  simp [normalizeWithCost]

/-- The shared value returned by one bounded Bézout block execution. -/
public structure BoundedBezoutBlock where
  gcd : SignMagnitude
  leftCoeff : SignMagnitude
  rightCoeff : SignMagnitude
  leftQuotient : SignMagnitude
  rightQuotient : SignMagnitude
  forward : Matrix (Fin 2) (Fin 2) Int
  inverse : Matrix (Fin 2) (Fin 2) Int
  left_inv : inverse * forward = 1
  right_inv : forward * inverse = 1

/--
Run bounded XGCD once, inspect its gcd once, and, in the nonzero branch,
perform the two external exact divisions used by the forward and inverse
two-row blocks.
-/
@[expose] public def boundedBezoutBlockWithCost
    (left right : SignMagnitude) : WithCost BoundedBezoutBlock := by
  let xgcdRun := boundedXGCDWithCost left right
  let gcdZero := isZeroWithCost xgcdRun.value.gcd
  let gcd := xgcdRun.value.gcd
  let leftCoeff := xgcdRun.value.leftCoeff
  let rightCoeff := xgcdRun.value.rightCoeff
  have specification := boundedXGCDWithCost_spec left right
  if hg : gcdZero.value then
    let identity : Matrix (Fin 2) (Fin 2) Int := 1
    exact
      { value :=
          { gcd
            leftCoeff
            rightCoeff
            leftQuotient := 0
            rightQuotient := 0
            forward := identity
            inverse := identity
            left_inv := by simp [identity]
            right_inv := by simp [identity] }
        cost := xgcdRun.cost + gcdZero.cost }
  else
    have gcd_ne_zero : gcd.value ≠ 0 := by
      intro valueZero
      apply hg
      change (isZeroWithCost gcd).value = true
      simp [valueZero]
    have gcd_dvd_left : gcd.value ∣ left.value := by
      rw [specification.gcd_value]
      exact Int.gcd_dvd_left left.value right.value
    have gcd_dvd_right : gcd.value ∣ right.value := by
      rw [specification.gcd_value]
      exact Int.gcd_dvd_right left.value right.value
    let leftDivision := exactDivWithCost left gcd gcd_ne_zero gcd_dvd_left
    let rightDivision := exactDivWithCost right gcd gcd_ne_zero gcd_dvd_right
    let leftQuotient := leftDivision.value
    let rightQuotient := rightDivision.value
    let forward : Matrix (Fin 2) (Fin 2) Int :=
      !![leftCoeff.value, rightCoeff.value;
         -rightQuotient.value, leftQuotient.value]
    let inverse : Matrix (Fin 2) (Fin 2) Int :=
      !![leftQuotient.value, -rightCoeff.value;
         rightQuotient.value, leftCoeff.value]
    have leftExact : leftQuotient.value * gcd.value = left.value := by
      rw [show leftQuotient.value = left.value / gcd.value by
        exact exactDivWithCost_value left gcd gcd_ne_zero gcd_dvd_left]
      exact Int.ediv_mul_cancel gcd_dvd_left
    have rightExact : rightQuotient.value * gcd.value = right.value := by
      rw [show rightQuotient.value = right.value / gcd.value by
        exact exactDivWithCost_value right gcd gcd_ne_zero gcd_dvd_right]
      exact Int.ediv_mul_cancel gcd_dvd_right
    have quotientBezout :
        leftCoeff.value * leftQuotient.value +
            rightCoeff.value * rightQuotient.value = 1 := by
      apply mul_right_cancel₀ gcd_ne_zero
      calc
        (leftCoeff.value * leftQuotient.value +
              rightCoeff.value * rightQuotient.value) * gcd.value =
            leftCoeff.value * left.value + rightCoeff.value * right.value := by
              rw [add_mul, mul_assoc, mul_assoc, leftExact, rightExact]
        _ = gcd.value := specification.bezout
        _ = 1 * gcd.value := by ring
    have quotientBezoutLeft :
        leftQuotient.value * leftCoeff.value +
            rightCoeff.value * rightQuotient.value = 1 := by
      calc
        leftQuotient.value * leftCoeff.value +
              rightCoeff.value * rightQuotient.value =
            leftCoeff.value * leftQuotient.value +
              rightCoeff.value * rightQuotient.value := by ring
        _ = 1 := quotientBezout
    have quotientBezoutRight :
        rightQuotient.value * rightCoeff.value +
            leftCoeff.value * leftQuotient.value = 1 := by
      calc
        rightQuotient.value * rightCoeff.value +
              leftCoeff.value * leftQuotient.value =
            leftCoeff.value * leftQuotient.value +
              rightCoeff.value * rightQuotient.value := by ring
        _ = 1 := quotientBezout
    have quotientBezoutBoth :
        rightQuotient.value * rightCoeff.value +
            leftQuotient.value * leftCoeff.value = 1 := by
      calc
        rightQuotient.value * rightCoeff.value +
              leftQuotient.value * leftCoeff.value =
            leftCoeff.value * leftQuotient.value +
              rightCoeff.value * rightQuotient.value := by ring
        _ = 1 := quotientBezout
    have inverseForward : inverse * forward = 1 := by
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [inverse, forward, Matrix.mul_apply,
          quotientBezoutLeft, quotientBezoutRight] <;>
        ring
    have forwardInverse : forward * inverse = 1 := by
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [inverse, forward, Matrix.mul_apply,
          quotientBezout, quotientBezoutBoth] <;>
        ring
    exact
      { value :=
          { gcd
            leftCoeff
            rightCoeff
            leftQuotient
            rightQuotient
            forward
            inverse
            left_inv := inverseForward
            right_inv := forwardInverse }
        cost := xgcdRun.cost + gcdZero.cost +
          leftDivision.cost + rightDivision.cost }

public theorem boundedBezoutBlockWithCost_value
    (left right : SignMagnitude) :
    let run := boundedBezoutBlockWithCost left right
    run.value.gcd = (boundedXGCDWithCost left right).value.gcd ∧
      run.value.leftCoeff =
        (boundedXGCDWithCost left right).value.leftCoeff ∧
      run.value.rightCoeff =
        (boundedXGCDWithCost left right).value.rightCoeff := by
  simp only [boundedBezoutBlockWithCost]
  split <;> simp

public theorem boundedBezoutBlockWithCost_forward_inverse
    (left right : SignMagnitude) :
    let block := (boundedBezoutBlockWithCost left right).value
    block.inverse * block.forward = 1 ∧
      block.forward * block.inverse = 1 := by
  exact ⟨(boundedBezoutBlockWithCost left right).value.left_inv,
    (boundedBezoutBlockWithCost left right).value.right_inv⟩

/-- A path-sensitive bound retaining only the four owned primitive costs. -/
@[expose] public def boundedBezoutBlockBitOperationBound
    (left right : SignMagnitude) : Nat :=
  let xgcdRun := boundedXGCDWithCost left right
  xgcdRun.cost + 1 +
    (divModWithCost left xgcdRun.value.gcd).cost +
    (divModWithCost right xgcdRun.value.gcd).cost

public theorem boundedBezoutBlockWithCost_cost_le
    (left right : SignMagnitude) :
    (boundedBezoutBlockWithCost left right).cost ≤
      boundedBezoutBlockBitOperationBound left right := by
  rw [boundedBezoutBlockWithCost]
  split <;> (simp [boundedBezoutBlockBitOperationBound, exactDivWithCost,
    quotientWithCost] <;> omega)

end NormalForms.Research.BitCost
