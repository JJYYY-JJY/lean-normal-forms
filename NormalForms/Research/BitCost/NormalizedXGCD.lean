/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.XGCD

/-!
# Sign-Normalized Costed Extended GCD

The low-level `xgcdWithCost` operation follows signed Euclidean division
literally.  For complexity arguments we instead normalize both inputs to
their nonnegative magnitudes, execute that same verified loop, and restore the
input signs on the two Bezout coefficients.  This keeps the value theorem
unchanged while ensuring that every recursive divisor in the underlying loop
is nonnegative.
-/

public section

namespace NormalForms.Research.BitCost

namespace SignMagnitude

/-- Replace the sign by `+`, preserving the canonical binary magnitude. -/
@[expose] public def nonnegative : SignMagnitude → SignMagnitude
  | .zero => .zero
  | .pos magnitude => .pos magnitude
  | .neg magnitude => .pos magnitude

/-- Restore an input sign on its Bezout coefficient. -/
@[expose] public def restoreCoefficientSign
    (input coefficient : SignMagnitude) : SignMagnitude :=
  match input with
  | .neg _ => -coefficient
  | _ => coefficient

@[simp] public theorem nonnegative_zero :
    nonnegative 0 = 0 :=
  rfl

@[simp] public theorem nonnegative_value (a : SignMagnitude) :
    a.nonnegative.value = (a.value.natAbs : Int) := by
  cases a with
  | zero => rfl
  | pos magnitude =>
      change (magnitude : Int) = Int.natAbs (magnitude : Int)
      rw [Int.natAbs_of_nonneg (PosNum.cast_pos magnitude).le]
  | neg magnitude =>
      change (magnitude : Int) = Int.natAbs (-(magnitude : Int))
      rw [Int.natAbs_neg]
      rw [Int.natAbs_of_nonneg (PosNum.cast_pos magnitude).le]

@[simp] public theorem nonnegative_bitLength (a : SignMagnitude) :
    a.nonnegative.bitLength = a.bitLength := by
  cases a <;> rfl

public theorem nonnegative_eq_self_of_value_nonnegative
    (a : SignMagnitude) (valueNonnegative : 0 ≤ a.value) :
    a.nonnegative = a := by
  cases a with
  | zero | pos _ => rfl
  | neg magnitude =>
      exfalso
      change 0 ≤ -(magnitude : Int) at valueNonnegative
      have positive : (0 : Int) < (magnitude : Int) := PosNum.cast_pos magnitude
      omega

@[simp] public theorem nonnegative_value_natAbs (a : SignMagnitude) :
    a.nonnegative.value.natAbs = a.value.natAbs := by
  rw [nonnegative_value, Int.natAbs_natCast]

@[simp] public theorem restoreCoefficientSign_bitLength
    (input coefficient : SignMagnitude) :
    (restoreCoefficientSign input coefficient).bitLength =
      coefficient.bitLength := by
  cases input <;>
    simp [restoreCoefficientSign]

@[simp] public theorem restoreCoefficientSign_value_natAbs
    (input coefficient : SignMagnitude) :
    (restoreCoefficientSign input coefficient).value.natAbs =
      coefficient.value.natAbs := by
  cases input <;>
    simp [restoreCoefficientSign]

public theorem restoreCoefficientSign_mul_value
    (input coefficient : SignMagnitude) :
    (restoreCoefficientSign input coefficient).value * input.value =
      coefficient.value * input.nonnegative.value := by
  cases input with
  | zero =>
      change coefficient.value * 0 = coefficient.value * 0
      rfl
  | pos magnitude =>
      change coefficient.value * (magnitude : Int) =
        coefficient.value * (magnitude : Int)
      rfl
  | neg magnitude =>
      change (-coefficient).value * (-(magnitude : Int)) =
        coefficient.value * (magnitude : Int)
      rw [value_neg]
      ring

end SignMagnitude

/--
Extended gcd on nonnegative magnitudes, with the original signs restored on
the returned Bezout coefficients.  The two constant cost units account for
the sign inspections; sign restoration itself only changes a constructor.
-/
@[expose] public def normalizedXGCDWithCost
    (left right : SignMagnitude) : WithCost XGCDResult :=
  let raw := xgcdWithCost left.nonnegative right.nonnegative
  { value :=
      { gcd := raw.value.gcd
        leftCoeff := left.restoreCoefficientSign raw.value.leftCoeff
        rightCoeff := right.restoreCoefficientSign raw.value.rightCoeff }
    cost := 2 + raw.cost }

/-- The normalized wrapper retains the standard gcd and Bezout identity. -/
public theorem normalizedXGCDWithCost_spec
    (left right : SignMagnitude) :
    XGCDSpecification left right
      (normalizedXGCDWithCost left right).value := by
  let raw := xgcdWithCost left.nonnegative right.nonnegative
  have rawSpec := xgcdWithCost_spec left.nonnegative right.nonnegative
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

@[simp] public theorem normalizedXGCDWithCost_gcd_value
    (left right : SignMagnitude) :
    (normalizedXGCDWithCost left right).value.gcd.value =
      (left.value.gcd right.value : Nat) :=
  (normalizedXGCDWithCost_spec left right).gcd_value

public theorem normalizedXGCDWithCost_bezout
    (left right : SignMagnitude) :
    (normalizedXGCDWithCost left right).value.leftCoeff.value * left.value +
        (normalizedXGCDWithCost left right).value.rightCoeff.value * right.value =
      (normalizedXGCDWithCost left right).value.gcd.value :=
  (normalizedXGCDWithCost_spec left right).bezout

/-- Exact path-sensitive budget inherited from the nonnegative run. -/
@[expose] public def normalizedXGCDBitOperationBound
    (left right : SignMagnitude) : Nat :=
  2 + xgcdBitOperationBound left.nonnegative right.nonnegative

public theorem normalizedXGCDWithCost_cost_le
    (left right : SignMagnitude) :
    (normalizedXGCDWithCost left right).cost ≤
      normalizedXGCDBitOperationBound left right := by
  exact Nat.add_le_add_left
    (xgcdWithCost_cost_le left.nonnegative right.nonnegative) 2

/-- Sign restoration does not enlarge either coefficient. -/
public theorem normalizedXGCDWithCost_coefficient_bitLength_le
    (left right : SignMagnitude) :
    (normalizedXGCDWithCost left right).value.leftCoeff.bitLength ≤
        xgcdCoefficientBitBound left.nonnegative right.nonnegative ∧
      (normalizedXGCDWithCost left right).value.rightCoeff.bitLength ≤
        xgcdCoefficientBitBound left.nonnegative right.nonnegative := by
  simpa [normalizedXGCDWithCost] using
    xgcdWithCost_coefficient_bitLength_le
      left.nonnegative right.nonnegative

end NormalForms.Research.BitCost
