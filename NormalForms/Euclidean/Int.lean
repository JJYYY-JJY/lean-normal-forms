/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Euclidean.ComputableOps
public import Mathlib.RingTheory.Int.Basic

/-!
# Constructive Euclidean operations for integers
-/

@[expose] public section

namespace NormalForms

/-- Constructive classification of integer units without extracting a witness from `IsUnit`. -/
public theorem intUnit_eq_one_or_negOne (unit : Intˣ) :
    unit = 1 ∨ unit = -1 := by
  have absoluteValue : Int.natAbs (unit : Int) = 1 :=
    Int.units_natAbs unit
  rcases Int.natAbs_eq (unit : Int) with equality | equality
  · apply Or.inl
    apply Units.ext
    exact equality.trans
      (congrArg (fun value : Nat => (value : Int)) absoluteValue)
  · apply Or.inr
    apply Units.ext
    exact equality.trans
      (congrArg (fun value : Nat => -(value : Int)) absoluteValue)

public theorem intNegOneUnit_inv :
    (-1 : Intˣ)⁻¹ = -1 := by
  apply Units.ext
  rfl

/--
The standard sign normalization on integers, with a proof that avoids the
choice-bearing general normalized-GCD instance.
-/
public abbrev constructiveIntNormalizationMonoid :
    NormalizationMonoid Int where
  normUnit value := if 0 ≤ value then 1 else -1
  normUnit_zero := by rfl
  normUnit_one := by rfl
  normUnit_mul_units := by
    intro value unit valueNeZero
    rcases intUnit_eq_one_or_negOne unit with rfl | rfl
    · simp only [Units.val_one, mul_one, inv_one, one_mul]
    · by_cases nonnegative : 0 ≤ value
      · have positive : 0 < value :=
          Int.lt_iff_le_and_ne.mpr
            ⟨nonnegative, Ne.symm valueNeZero⟩
        have negativeNotNonnegative : ¬0 ≤ -value :=
          Int.not_le_of_gt (Int.neg_neg_of_pos positive)
        simp only [Units.val_neg, Units.val_one, mul_neg, mul_one,
          negativeNotNonnegative, reduceIte, intNegOneUnit_inv,
          if_pos nonnegative]
      · have negative : value < 0 := Int.lt_of_not_ge nonnegative
        have negationNonnegative : 0 ≤ -value :=
          Int.neg_nonneg_of_nonpos (Int.le_of_lt negative)
        simp only [Units.val_neg, Units.val_one, mul_neg, mul_one,
          negationNonnegative, reduceIte, intNegOneUnit_inv,
          if_neg nonnegative, neg_neg]

attribute [instance 10000] constructiveIntNormalizationMonoid

public instance instComputableEuclideanOpsInt :
    @ComputableEuclideanOps Int Int.euclideanDomain
      constructiveIntNormalizationMonoid where
  eqb a b := decide (a = b)
  divMod a b := (a / b, a % b)
  normalize a := a.natAbs
  normUnit a := if 0 ≤ a then 1 else -1
  xgcd a b :=
    { gcd := Int.gcd a b
      leftCoeff := Int.gcdA a b
      rightCoeff := Int.gcdB a b }
  measure := Int.natAbs
  normUnitUnit := NormalizationMonoid.normUnit

  eqb_spec := by
    intro a b
    simp
  divMod_spec := by
    intro a b
    rfl
  remainder_measure_lt := by
    intro a b hb
    exact EuclideanDomain.mod_lt a hb
  normalize_spec := show
      ∀ a,
        (a.natAbs : Int) =
          @normalize Int (@Semiring.toMonoidWithZero Int Int.instSemiring)
            constructiveIntNormalizationMonoid a
    from by
      intro a
      change (a.natAbs : Int) =
        a * ((@NormalizationMonoid.normUnit Int
          (@Semiring.toMonoidWithZero Int Int.instSemiring)
          constructiveIntNormalizationMonoid a : Intˣ) : Int)
      have hunit :
          @NormalizationMonoid.normUnit Int
              (@Semiring.toMonoidWithZero Int Int.instSemiring)
              constructiveIntNormalizationMonoid a =
            if 0 ≤ a then (1 : Intˣ) else -1 :=
        rfl
      rw [hunit]
      by_cases h : 0 ≤ a
      · simp [h, Int.natAbs_of_nonneg h]
      · have hneg : a < 0 := Int.lt_of_not_ge h
        have hnonneg : 0 ≤ -a :=
          Int.neg_nonneg_of_nonpos (Int.le_of_lt hneg)
        have hnatAbs : (a.natAbs : Int) = -a := by
          calc
            (a.natAbs : Int) = ((-a).natAbs : Int) := by
              rw [Int.natAbs_neg]
            _ = -a := Int.natAbs_of_nonneg hnonneg
        simp [h, hnatAbs]
  normalize_idem_spec := by
    intro a
    rw [Int.natAbs_of_nonneg]
    exact Int.natCast_nonneg _
  normUnit_spec := by
    intro a
    have hunit :
        @NormalizationMonoid.normUnit Int
            (@Semiring.toMonoidWithZero Int Int.instSemiring)
            constructiveIntNormalizationMonoid a =
          if 0 ≤ a then (1 : Intˣ) else -1 :=
      rfl
    rw [hunit]
    by_cases h : 0 ≤ a <;> simp [h, Units.val_neg, Units.val_one]
  normUnitUnit_coe := by
    intro a
    have hunit :
        @NormalizationMonoid.normUnit Int
            (@Semiring.toMonoidWithZero Int Int.instSemiring)
            constructiveIntNormalizationMonoid a =
          if 0 ≤ a then (1 : Intˣ) else -1 :=
      rfl
    rw [hunit]
    by_cases h : 0 ≤ a <;> simp [h, Units.val_neg, Units.val_one]
  xgcd_normalized := by
    intro a b
    change (Int.gcd a b : Int) =
      (Int.gcd a b : Int) *
        ((@NormalizationMonoid.normUnit Int
          (@Semiring.toMonoidWithZero Int Int.instSemiring)
          constructiveIntNormalizationMonoid (Int.gcd a b : Int) :
            Intˣ) : Int)
    have hunit :
        @NormalizationMonoid.normUnit Int
            (@Semiring.toMonoidWithZero Int Int.instSemiring)
            constructiveIntNormalizationMonoid (Int.gcd a b : Int) =
          if 0 ≤ (Int.gcd a b : Int) then (1 : Intˣ) else -1 :=
      rfl
    rw [hunit]
    have hnonnegative : 0 ≤ (Int.gcd a b : Int) :=
      Int.natCast_nonneg (Int.gcd a b)
    rw [if_pos hnonnegative]
    simp only [Units.val_one, mul_one]
  xgcd_bezout_spec := by
    intro a b
    change a * Int.gcdA a b + b * Int.gcdB a b = (Int.gcd a b : Int)
    exact (Int.gcd_eq_gcd_ab a b).symm
  xgcd_dvd_left := by
    intro a b
    change (Int.gcd a b : Int) ∣ a
    exact Int.gcd_dvd_left a b
  xgcd_dvd_right := by
    intro a b
    change (Int.gcd a b : Int) ∣ b
    exact Int.gcd_dvd_right a b
  dvd_xgcd := by
    intro a b d ha hb
    change d ∣ (Int.gcd a b : Int)
    exact Int.dvd_coe_gcd ha hb
  xgcd_measure_lt := by
    intro a b ha hnot
    change Int.gcd a b < a.natAbs
    apply lt_of_le_of_ne (Int.gcd_le_natAbs_left b ha)
    intro hEq
    apply hnot
    exact Int.gcd_eq_natAbs_left_iff_dvd.mp hEq

end NormalForms
