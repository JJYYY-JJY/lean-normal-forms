/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Basic

/-!
# Constructive Euclidean operations

`ComputableEuclideanOps` is the executable seam used by the normal-form
kernels.  It does not replace the ambient ring or matrix operations.  Instead,
it supplies executable implementations of the Euclidean operations whose
generic mathlib instances may be noncomputable, together with equations back to
the standard semantics.
-/

@[expose] public section

namespace NormalForms

/-- Data returned by the constructive extended Euclidean algorithm. -/
public structure XGCDResult (R : Type _) where
  gcd : R
  leftCoeff : R
  rightCoeff : R

/--
Executable Euclidean operations with laws tying every result to mathlib's
standard structures.

`normUnitUnit` is the constructive unit witness corresponding to the
ring-valued `normUnit` field.  Keeping the witness as data lets matrix
algorithms scale rows and columns without extracting a unit from an existential
proof.
-/
public class ComputableEuclideanOps
    (R : Type _) [EuclideanDomain R] [NormalizationMonoid R] where
  eqb : R → R → Bool
  divMod : R → R → R × R
  normalize : R → R
  normUnit : R → R
  xgcd : R → R → XGCDResult R
  measure : R → Nat
  normUnitUnit : R → Rˣ

  eqb_spec : ∀ a b, eqb a b = true ↔ a = b
  divMod_spec : ∀ a b, divMod a b = (a / b, a % b)
  remainder_measure_lt :
    ∀ a {b}, b ≠ 0 → measure (divMod a b).2 < measure b
  normalize_spec : ∀ a, normalize a = _root_.normalize a
  normalize_idem_spec : ∀ a, normalize (normalize a) = normalize a
  normUnit_spec :
    ∀ a, normUnit a = (↑(NormalizationMonoid.normUnit a) : R)
  normUnitUnit_coe : ∀ a, (↑(normUnitUnit a) : R) = normUnit a
  xgcd_normalized :
    ∀ a b, (xgcd a b).gcd = _root_.normalize (xgcd a b).gcd
  xgcd_bezout_spec :
    ∀ a b, a * (xgcd a b).leftCoeff + b * (xgcd a b).rightCoeff =
      (xgcd a b).gcd
  xgcd_dvd_left : ∀ a b, (xgcd a b).gcd ∣ a
  xgcd_dvd_right : ∀ a b, (xgcd a b).gcd ∣ b
  dvd_xgcd :
    ∀ {a b d}, d ∣ a → d ∣ b → d ∣ (xgcd a b).gcd
  xgcd_measure_lt :
    ∀ {a b}, a ≠ 0 → ¬a ∣ b →
      measure (xgcd a b).gcd < measure (normalize a)

namespace ComputableEuclideanOps

variable {R : Type _} [EuclideanDomain R]
  [NormalizationMonoid R] [ComputableEuclideanOps R]

/-- Decidable equality derived directly from the executable equality test. -/
@[implicit_reducible] public def decidableEq : DecidableEq R := fun a b =>
  if h : ComputableEuclideanOps.eqb a b = true then
    isTrue ((ComputableEuclideanOps.eqb_spec a b).1 h)
  else
    isFalse (fun hab => h ((ComputableEuclideanOps.eqb_spec a b).2 hab))

attribute [instance 10000] decidableEq

/--
The Euclidean cancellation law reconstructed with executable equality.
This avoids the choice-bearing generic instance while preserving the standard
division operation.
-/
public theorem mulDivCancelClass : MulDivCancelClass R where
  mul_div_cancel a b hb := by
    refine (eq_of_sub_eq_zero ?_).symm
    by_contra h
    have hnot := EuclideanDomain.mul_right_not_lt b h
    rw [sub_mul, mul_comm (_ / _),
      sub_eq_iff_eq_add'.2 (EuclideanDomain.div_add_mod (a * b) b).symm] at hnot
    exact hnot (EuclideanDomain.mod_lt _ hb)

attribute [instance 10000] mulDivCancelClass

/-- The executable quotient derived from the paired division operation. -/
@[inline] public def quot (a b : R) : R :=
  (ComputableEuclideanOps.divMod a b).1

/-- The executable remainder derived from the paired division operation. -/
@[inline] public def rem (a b : R) : R :=
  (ComputableEuclideanOps.divMod a b).2

/-- Boolean zero test derived from the exact equality test. -/
@[inline] public def isZeroB (a : R) : Bool :=
  ComputableEuclideanOps.eqb a 0

/-- Boolean divisibility test; `a ∣ b` exactly when the remainder is zero. -/
@[inline] public def dvdB (a b : R) : Bool :=
  isZeroB (rem b a)

@[simp] public theorem eqb_eq_true_iff (a b : R) :
    ComputableEuclideanOps.eqb a b = true ↔ a = b :=
  ComputableEuclideanOps.eqb_spec a b

@[simp] public theorem quot_eq (a b : R) :
    quot a b = a / b := by
  rw [quot, ComputableEuclideanOps.divMod_spec]

@[simp] public theorem rem_eq (a b : R) :
    rem a b = a % b := by
  rw [rem, ComputableEuclideanOps.divMod_spec]

@[simp] public theorem isZeroB_eq_true_iff (a : R) :
    isZeroB a = true ↔ a = 0 := by
  exact ComputableEuclideanOps.eqb_spec a 0

public theorem mod_eq_zero_iff_dvd_constructive (a b : R) :
    a % b = 0 ↔ b ∣ a := by
  constructor
  · intro h
    rw [← EuclideanDomain.div_add_mod a b, h, add_zero]
    exact dvd_mul_right _ _
  · rintro ⟨c, rfl⟩
    rw [← add_left_cancel_iff, EuclideanDomain.div_add_mod, add_zero]
    by_cases hb : b = 0
    · simp only [hb, zero_mul]
    · rw [mul_div_cancel_left₀ _ hb]

@[simp] public theorem dvdB_eq_true_iff (a b : R) :
    dvdB a b = true ↔ a ∣ b := by
  rw [dvdB, isZeroB_eq_true_iff, rem_eq]
  exact mod_eq_zero_iff_dvd_constructive b a

public theorem rem_measure_lt (a : R) {b : R} (hb : b ≠ 0) :
    ComputableEuclideanOps.measure (rem a b) <
      ComputableEuclideanOps.measure b := by
  rw [rem]
  exact ComputableEuclideanOps.remainder_measure_lt a hb

@[simp] public theorem normalize_eq_mathlib (a : R) :
    ComputableEuclideanOps.normalize a = _root_.normalize a :=
  ComputableEuclideanOps.normalize_spec a

@[simp] public theorem normalize_idem_exec (a : R) :
    ComputableEuclideanOps.normalize
        (ComputableEuclideanOps.normalize a) =
      ComputableEuclideanOps.normalize a :=
  ComputableEuclideanOps.normalize_idem_spec a

public theorem normalize_idem_constructive (a : R) :
    _root_.normalize (_root_.normalize a) = _root_.normalize a := by
  calc
    _root_.normalize (_root_.normalize a) =
        ComputableEuclideanOps.normalize (_root_.normalize a) :=
      (normalize_eq_mathlib _).symm
    _ = ComputableEuclideanOps.normalize
          (ComputableEuclideanOps.normalize a) := by
      exact congrArg ComputableEuclideanOps.normalize
        (normalize_eq_mathlib a).symm
    _ = ComputableEuclideanOps.normalize a := normalize_idem_exec a
    _ = _root_.normalize a := normalize_eq_mathlib a

@[simp] public theorem normUnit_eq_mathlib (a : R) :
    ComputableEuclideanOps.normUnit a =
      (↑(NormalizationMonoid.normUnit a) : R) :=
  ComputableEuclideanOps.normUnit_spec a

@[simp] public theorem coe_normUnitUnit (a : R) :
    (↑(ComputableEuclideanOps.normUnitUnit a) : R) =
      ComputableEuclideanOps.normUnit a :=
  ComputableEuclideanOps.normUnitUnit_coe a

public theorem normalize_eq_mul_normUnitUnit (a : R) :
    ComputableEuclideanOps.normalize a =
      a * (ComputableEuclideanOps.normUnitUnit a : R) := by
  calc
    ComputableEuclideanOps.normalize a = _root_.normalize a :=
      normalize_eq_mathlib a
    _ = a * (NormalizationMonoid.normUnit a : R) := _root_.normalize_apply a
    _ = a * ComputableEuclideanOps.normUnit a := by
      rw [normUnit_eq_mathlib]
    _ = a * (ComputableEuclideanOps.normUnitUnit a : R) := by
      rw [coe_normUnitUnit]

public theorem xgcd_bezout (a b : R) :
    a * (ComputableEuclideanOps.xgcd a b).leftCoeff +
        b * (ComputableEuclideanOps.xgcd a b).rightCoeff =
      (ComputableEuclideanOps.xgcd a b).gcd :=
  ComputableEuclideanOps.xgcd_bezout_spec a b

public theorem xgcd_gcd_normalized (a b : R) :
    (ComputableEuclideanOps.xgcd a b).gcd =
      _root_.normalize (ComputableEuclideanOps.xgcd a b).gcd :=
  ComputableEuclideanOps.xgcd_normalized a b

public theorem xgcd_gcd_dvd_left (a b : R) :
    (ComputableEuclideanOps.xgcd a b).gcd ∣ a :=
  ComputableEuclideanOps.xgcd_dvd_left a b

public theorem xgcd_gcd_dvd_right (a b : R) :
    (ComputableEuclideanOps.xgcd a b).gcd ∣ b :=
  ComputableEuclideanOps.xgcd_dvd_right a b

public theorem dvd_xgcd_gcd {a b d : R} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ (ComputableEuclideanOps.xgcd a b).gcd :=
  ComputableEuclideanOps.dvd_xgcd ha hb

/-- Cancellation by a nonzero factor without using a generic domain instance. -/
public theorem mul_left_cancel_of_ne_zero {a b c : R} (ha : a ≠ 0)
    (h : a * b = a * c) :
    b = c := by
  calc
    b = a * b / a := (mul_div_cancel_left₀ b ha).symm
    _ = a * c / a := congrArg (fun x => x / a) h
    _ = c := mul_div_cancel_left₀ c ha

/-- Exact division of a known multiple, using the executable cancellation law. -/
public theorem mul_quot_cancel_of_dvd {a b : R} (hb : b ≠ 0) (hab : b ∣ a) :
    b * quot a b = a := by
  rw [quot_eq]
  rcases hab with ⟨c, rfl⟩
  rw [mul_div_cancel_left₀ c hb]

/--
The intrinsic normalized gcd returned by `xgcd` agrees with mathlib's
Euclidean gcd after normalization.  The decidable equality is needed only by
mathlib's generic gcd definition, not by the executable operation itself.
-/
public theorem xgcd_gcd_eq_mathlib [DecidableEq R] (a b : R) :
    (ComputableEuclideanOps.xgcd a b).gcd =
      _root_.normalize (EuclideanDomain.gcd a b) := by
  apply dvd_antisymm_of_normalize_eq
  · exact (xgcd_gcd_normalized a b).symm
  · exact normalize_idem_constructive _
  · rw [dvd_normalize_iff]
    exact EuclideanDomain.dvd_gcd
      (xgcd_gcd_dvd_left a b) (xgcd_gcd_dvd_right a b)
  · rw [normalize_dvd_iff]
    exact dvd_xgcd_gcd
      (EuclideanDomain.gcd_dvd_left a b) (EuclideanDomain.gcd_dvd_right a b)

public theorem xgcd_gcd_eq_zero_iff (a b : R) :
    (ComputableEuclideanOps.xgcd a b).gcd = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro hg
    constructor
    · have hdiv := xgcd_gcd_dvd_left a b
      rw [hg] at hdiv
      exact zero_dvd_iff.mp hdiv
    · have hdiv := xgcd_gcd_dvd_right a b
      rw [hg] at hdiv
      exact zero_dvd_iff.mp hdiv
  · rintro ⟨rfl, rfl⟩
    apply zero_dvd_iff.mp
    exact dvd_xgcd_gcd (dvd_refl 0) (dvd_refl 0)

end ComputableEuclideanOps

end NormalForms
