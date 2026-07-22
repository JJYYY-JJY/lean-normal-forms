/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.CoefficientSize
public import NormalForms.Euclidean.Int
public import NormalForms.Research.BitCost.BoundedXGCDCost
import all NormalForms.Matrix.Hermite.Bezout

/-!
# Bounded Bézout coefficients for the principal-minor kernel

This is the Appendix postprocessing step from Kannan--Bachem: one coefficient
is reduced modulo the larger input, and the other is adjusted so the Bézout
identity is preserved.  The resulting coefficients have polynomial magnitude.
The operation package is kept explicit, so importing this research module does
not replace the core integer `ComputableEuclideanOps` instance.
-/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open NormalForms
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

namespace Principal

/--
Kannan--Bachem's size-controlled integer Bézout data, projected from the exact
costed sign-magnitude reference implementation.
-/
def boundedIntXGCD (a b : Int) : XGCDResult Int :=
  let result :=
    (NormalForms.Research.BitCost.boundedXGCDWithCost
      (NormalForms.Research.BitCost.SignMagnitude.ofInt a)
      (NormalForms.Research.BitCost.SignMagnitude.ofInt b)).value
  { gcd := result.gcd.value
    leftCoeff := result.leftCoeff.value
    rightCoeff := result.rightCoeff.value }

@[simp] theorem boundedIntXGCD_gcd (a b : Int) :
    (boundedIntXGCD a b).gcd = (Int.gcd a b : Int) := by
  have specification :=
    NormalForms.Research.BitCost.boundedXGCDWithCost_spec
      (NormalForms.Research.BitCost.SignMagnitude.ofInt a)
      (NormalForms.Research.BitCost.SignMagnitude.ofInt b)
  simpa only [boundedIntXGCD,
    NormalForms.Research.BitCost.SignMagnitude.value_ofInt] using
    specification.gcd_value

theorem boundedIntXGCD_bezout (a b : Int) :
    a * (boundedIntXGCD a b).leftCoeff +
        b * (boundedIntXGCD a b).rightCoeff =
      (boundedIntXGCD a b).gcd := by
  have specification :=
    NormalForms.Research.BitCost.boundedXGCDWithCost_spec
      (NormalForms.Research.BitCost.SignMagnitude.ofInt a)
      (NormalForms.Research.BitCost.SignMagnitude.ofInt b)
  simpa only [boundedIntXGCD,
    NormalForms.Research.BitCost.SignMagnitude.value_ofInt, mul_comm] using
    specification.bezout

/-- A closed magnitude budget for both modified Bézout coefficients. -/
@[expose] public def boundedIntXGCDCoefficientHeight (a b : Int) : Nat :=
  let height := max a.natAbs b.natAbs
  (height + 1) ^ 2

theorem natAbs_le_natAbs_mul_of_ne_zero (left right : Int)
    (hleft : left ≠ 0) :
    right.natAbs ≤ (left * right).natAbs := by
  rw [Int.natAbs_mul]
  exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hleft)

theorem boundedIntXGCD_coefficient_natAbs_le (a b : Int) :
    (boundedIntXGCD a b).leftCoeff.natAbs ≤
        boundedIntXGCDCoefficientHeight a b ∧
      (boundedIntXGCD a b).rightCoeff.natAbs ≤
        boundedIntXGCDCoefficientHeight a b := by
  have bounds :=
    NormalForms.Research.BitCost.boundedXGCDWithCost_coefficient_natAbs_le
      (NormalForms.Research.BitCost.SignMagnitude.ofInt a)
      (NormalForms.Research.BitCost.SignMagnitude.ofInt b)
  simpa only [boundedIntXGCD, boundedIntXGCDCoefficientHeight,
    NormalForms.Research.BitCost.boundedXGCDCoefficientHeight,
    NormalForms.Research.BitCost.SignMagnitude.value_ofInt] using bounds

/-- Modeled bit operations used by the exact bounded integer XGCD call. -/
@[expose] public def boundedIntXGCDBitOperationCost (a b : Int) : Nat :=
  (NormalForms.Research.BitCost.boundedXGCDWithCost
    (NormalForms.Research.BitCost.SignMagnitude.ofInt a)
    (NormalForms.Research.BitCost.SignMagnitude.ofInt b)).cost

/-- Closed polynomial budget for one bounded integer XGCD call. -/
@[expose] public def boundedIntXGCDBitOperationBound (a b : Int) : Nat :=
  NormalForms.Research.BitCost.boundedXGCDPolynomialBitOperationBound
    (Nat.size a.natAbs) (Nat.size b.natAbs)

/-- The primitive executed by the principal kernel fits its modeled budget. -/
public theorem boundedIntXGCDBitOperationCost_le (a b : Int) :
    boundedIntXGCDBitOperationCost a b ≤
      boundedIntXGCDBitOperationBound a b := by
  simpa only [boundedIntXGCDBitOperationCost,
    boundedIntXGCDBitOperationBound,
    NormalForms.Research.BitCost.SignMagnitude.bitLength_eq_natSize_natAbs,
    NormalForms.Research.BitCost.SignMagnitude.value_ofInt] using
    NormalForms.Research.BitCost.boundedXGCDWithCost_cost_le
      (NormalForms.Research.BitCost.SignMagnitude.ofInt a)
      (NormalForms.Research.BitCost.SignMagnitude.ofInt b)

/-- Uniform primitive budget when both integer inputs fit one bit width. -/
@[expose] public def boundedIntXGCDUniformBitOperationBound
    (operandBits : Nat) : Nat :=
  3 + (2 * operandBits + 1) *
    NormalForms.Research.BitCost.boundedXGCDStepCostBound operandBits

public theorem boundedIntXGCDBitOperationCost_le_uniform
    (a b : Int) (operandBits : Nat)
    (aWidth : Nat.size a.natAbs ≤ operandBits)
    (bWidth : Nat.size b.natAbs ≤ operandBits) :
    boundedIntXGCDBitOperationCost a b ≤
      boundedIntXGCDUniformBitOperationBound operandBits := by
  have aWidth' :
      (NormalForms.Research.BitCost.SignMagnitude.ofInt a).bitLength ≤
        operandBits := by
    simpa only [
      NormalForms.Research.BitCost.SignMagnitude.bitLength_eq_natSize_natAbs,
      NormalForms.Research.BitCost.SignMagnitude.value_ofInt] using aWidth
  have bWidth' :
      (NormalForms.Research.BitCost.SignMagnitude.ofInt b).bitLength ≤
        operandBits := by
    simpa only [
      NormalForms.Research.BitCost.SignMagnitude.bitLength_eq_natSize_natAbs,
      NormalForms.Research.BitCost.SignMagnitude.value_ofInt] using bWidth
  simpa only [boundedIntXGCDBitOperationCost,
    boundedIntXGCDUniformBitOperationBound,
    NormalForms.Research.BitCost.SignMagnitude.bitLength_eq_natSize_natAbs,
    NormalForms.Research.BitCost.SignMagnitude.value_ofInt] using
    NormalForms.Research.BitCost.boundedXGCDWithCost_cost_le_uniform
      (NormalForms.Research.BitCost.SignMagnitude.ofInt a)
      (NormalForms.Research.BitCost.SignMagnitude.ofInt b)
      operandBits aWidth' bWidth'

/-- Explicit operation package used only by the principal-minor backend. -/
@[reducible] def boundedIntEuclideanOps :
    @ComputableEuclideanOps Int Int.euclideanDomain
      constructiveIntNormalizationMonoid :=
  { (inferInstance : @ComputableEuclideanOps Int Int.euclideanDomain
      constructiveIntNormalizationMonoid) with
  xgcd := boundedIntXGCD
  xgcd_normalized := by
    intro a b
    rw [boundedIntXGCD_gcd]
    exact ComputableEuclideanOps.xgcd_gcd_normalized a b
  xgcd_bezout_spec := boundedIntXGCD_bezout
  xgcd_dvd_left := by
    intro a b
    rw [boundedIntXGCD_gcd]
    exact_mod_cast Int.gcd_dvd_left a b
  xgcd_dvd_right := by
    intro a b
    rw [boundedIntXGCD_gcd]
    exact_mod_cast Int.gcd_dvd_right a b
  dvd_xgcd := by
    intro a b d ha hb
    rw [boundedIntXGCD_gcd]
    exact Int.dvd_coe_gcd ha hb
  xgcd_measure_lt := by
    intro a b ha hnot
    rw [boundedIntXGCD_gcd]
    change Int.gcd a b < a.natAbs
    apply lt_of_le_of_ne (Int.gcd_le_natAbs_left b ha)
    intro equality
    apply hnot
    exact Int.gcd_eq_natAbs_left_iff_dvd.mp equality
  }

/--
Size-controlled two-row matrix, without installing another global instance.
The formula is stated directly so executable reduction does not unfold an
entire explicit `ComputableEuclideanOps` record at every matrix entry.
-/
def boundedBezoutReductionMatrix (a b : Int) :
    _root_.Matrix (Fin 2) (Fin 2) Int :=
  let data := boundedIntXGCD a b
  if data.gcd = 0 then
    1
  else
    !![data.leftCoeff, data.rightCoeff;
       -(b / data.gcd), a / data.gcd]

/-- Direct executable inverse of `boundedBezoutReductionMatrix`. -/
def boundedBezoutReductionInverseMatrix (a b : Int) :
    _root_.Matrix (Fin 2) (Fin 2) Int :=
  let data := boundedIntXGCD a b
  if data.gcd = 0 then
    1
  else
    !![a / data.gcd, -data.rightCoeff;
       b / data.gcd, data.leftCoeff]

theorem boundedBezoutReductionMatrix_mulVec (a b : Int) :
    _root_.Matrix.mulVec (boundedBezoutReductionMatrix a b) ![a, b] =
      ![(boundedIntXGCD a b).gcd, 0] := by
  let data := boundedIntXGCD a b
  by_cases hg : data.gcd = 0
  · have bothZero : a = 0 ∧ b = 0 :=
      (@ComputableEuclideanOps.xgcd_gcd_eq_zero_iff Int Int.euclideanDomain
        constructiveIntNormalizationMonoid boundedIntEuclideanOps a b).1 hg
    simp [boundedBezoutReductionMatrix, bothZero.1, bothZero.2]
  · rw [boundedBezoutReductionMatrix, if_neg hg]
    ext index
    fin_cases index
    · rw [_root_.Matrix.mulVec, dotProduct,
        NormalForms.Matrix.Constructive.sum_univ_two]
      simpa [data, mul_comm] using boundedIntXGCD_bezout a b
    · suffices equality :
          -(b / data.gcd) * a + (a / data.gcd) * b = 0 by
        rw [_root_.Matrix.mulVec, dotProduct,
          NormalForms.Matrix.Constructive.sum_univ_two]
        simpa [data] using equality
      have gcdDvdLeft : data.gcd ∣ a :=
        @ComputableEuclideanOps.xgcd_gcd_dvd_left Int Int.euclideanDomain
          constructiveIntNormalizationMonoid boundedIntEuclideanOps a b
      have gcdDvdRight : data.gcd ∣ b :=
        @ComputableEuclideanOps.xgcd_gcd_dvd_right Int Int.euclideanDomain
          constructiveIntNormalizationMonoid boundedIntEuclideanOps a b
      have leftExact : data.gcd * (a / data.gcd) = a := by
        rw [mul_comm]
        exact Int.ediv_mul_cancel gcdDvdLeft
      have rightExact : data.gcd * (b / data.gcd) = b := by
        rw [mul_comm]
        exact Int.ediv_mul_cancel gcdDvdRight
      apply mul_left_cancel₀ hg
      rw [mul_zero]
      calc
        data.gcd * (-(b / data.gcd) * a + (a / data.gcd) * b) =
            -((data.gcd * (b / data.gcd)) * a) +
              (data.gcd * (a / data.gcd)) * b := by ring
        _ = -(b * a) + a * b := by
          rw [rightExact, leftExact]
        _ = 0 := by ring

theorem boundedIntXGCD_gcd_normalized (a b : Int) :
    (boundedIntXGCD a b).gcd =
      _root_.normalize (boundedIntXGCD a b).gcd := by
  exact @ComputableEuclideanOps.xgcd_gcd_normalized Int Int.euclideanDomain
    constructiveIntNormalizationMonoid boundedIntEuclideanOps a b

theorem boundedIntXGCD_gcd_eq_zero_iff (a b : Int) :
    (boundedIntXGCD a b).gcd = 0 ↔ a = 0 ∧ b = 0 := by
  exact @ComputableEuclideanOps.xgcd_gcd_eq_zero_iff Int Int.euclideanDomain
    constructiveIntNormalizationMonoid boundedIntEuclideanOps a b

theorem boundedIntXGCD_leftQuotient_natAbs_le (a b : Int)
    (hg : (boundedIntXGCD a b).gcd ≠ 0) :
    (a / (boundedIntXGCD a b).gcd).natAbs ≤ a.natAbs := by
  have dvd : (boundedIntXGCD a b).gcd ∣ a :=
    @ComputableEuclideanOps.xgcd_gcd_dvd_left Int Int.euclideanDomain
      constructiveIntNormalizationMonoid boundedIntEuclideanOps a b
  have product : (boundedIntXGCD a b).gcd *
      (a / (boundedIntXGCD a b).gcd) = a := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel dvd
  exact (natAbs_le_natAbs_mul_of_ne_zero _ _ hg).trans_eq
    (congrArg Int.natAbs product)

theorem boundedIntXGCD_rightQuotient_natAbs_le (a b : Int)
    (hg : (boundedIntXGCD a b).gcd ≠ 0) :
    (b / (boundedIntXGCD a b).gcd).natAbs ≤ b.natAbs := by
  have dvd : (boundedIntXGCD a b).gcd ∣ b :=
    @ComputableEuclideanOps.xgcd_gcd_dvd_right Int Int.euclideanDomain
      constructiveIntNormalizationMonoid boundedIntEuclideanOps a b
  have product : (boundedIntXGCD a b).gcd *
      (b / (boundedIntXGCD a b).gcd) = b := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel dvd
  exact (natAbs_le_natAbs_mul_of_ne_zero _ _ hg).trans_eq
    (congrArg Int.natAbs product)

theorem boundedBezoutReductionMatrix_entry_natAbs_le (a b : Int)
    (notBothZero : a ≠ 0 ∨ b ≠ 0) (row column : Fin 2) :
    (boundedBezoutReductionMatrix a b row column).natAbs ≤
      boundedIntXGCDCoefficientHeight a b := by
  let data := boundedIntXGCD a b
  have hg : data.gcd ≠ 0 := by
    intro equality
    have bothZero := (boundedIntXGCD_gcd_eq_zero_iff a b).1 equality
    exact notBothZero.elim (· bothZero.1) (· bothZero.2)
  have coefficients := boundedIntXGCD_coefficient_natAbs_le a b
  have leftQuotient := boundedIntXGCD_leftQuotient_natAbs_le a b hg
  have rightQuotient := boundedIntXGCD_rightQuotient_natAbs_le a b hg
  have leftInput : a.natAbs ≤ boundedIntXGCDCoefficientHeight a b := by
    unfold boundedIntXGCDCoefficientHeight
    have : a.natAbs ≤ max a.natAbs b.natAbs := le_max_left _ _
    nlinarith
  have rightInput : b.natAbs ≤ boundedIntXGCDCoefficientHeight a b := by
    unfold boundedIntXGCDCoefficientHeight
    have : b.natAbs ≤ max a.natAbs b.natAbs := le_max_right _ _
    nlinarith
  rw [boundedBezoutReductionMatrix, if_neg hg]
  fin_cases row <;> fin_cases column
  · change data.leftCoeff.natAbs ≤ _
    exact coefficients.1
  · change data.rightCoeff.natAbs ≤ _
    exact coefficients.2
  · change (-(b / (boundedIntXGCD a b).gcd)).natAbs ≤ _
    simpa using rightQuotient.trans rightInput
  · change (a / (boundedIntXGCD a b).gcd).natAbs ≤ _
    exact leftQuotient.trans leftInput

theorem boundedIntXGCD_divIdentity (a b : Int)
    (hg : (boundedIntXGCD a b).gcd ≠ 0) :
    (boundedIntXGCD a b).leftCoeff *
          (a / (boundedIntXGCD a b).gcd) +
        (boundedIntXGCD a b).rightCoeff *
          (b / (boundedIntXGCD a b).gcd) = 1 := by
  let data := boundedIntXGCD a b
  have gcdDvdLeft : data.gcd ∣ a :=
    @ComputableEuclideanOps.xgcd_gcd_dvd_left Int Int.euclideanDomain
      constructiveIntNormalizationMonoid boundedIntEuclideanOps a b
  have gcdDvdRight : data.gcd ∣ b :=
    @ComputableEuclideanOps.xgcd_gcd_dvd_right Int Int.euclideanDomain
      constructiveIntNormalizationMonoid boundedIntEuclideanOps a b
  have leftExact : data.gcd * (a / data.gcd) = a := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel gcdDvdLeft
  have rightExact : data.gcd * (b / data.gcd) = b := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel gcdDvdRight
  apply mul_left_cancel₀ hg
  rw [mul_one]
  calc
    data.gcd *
          (data.leftCoeff * (a / data.gcd) +
            data.rightCoeff * (b / data.gcd)) =
        data.leftCoeff * (data.gcd * (a / data.gcd)) +
          data.rightCoeff * (data.gcd * (b / data.gcd)) := by ring
    _ = data.leftCoeff * a + data.rightCoeff * b := by
      rw [leftExact, rightExact]
    _ = data.gcd := by
      simpa [data, mul_comm] using boundedIntXGCD_bezout a b

theorem boundedBezoutReductionInverseMatrix_mul (a b : Int) :
    boundedBezoutReductionInverseMatrix a b *
        boundedBezoutReductionMatrix a b = 1 := by
  let data := boundedIntXGCD a b
  by_cases hg : data.gcd = 0
  · rw [boundedBezoutReductionInverseMatrix,
      boundedBezoutReductionMatrix, if_pos hg, if_pos hg]
    exact NormalForms.Matrix.Constructive.one_mul 1
  · have identity := boundedIntXGCD_divIdentity a b hg
    rw [boundedIntXGCD_gcd] at identity
    rw [boundedBezoutReductionInverseMatrix,
      boundedBezoutReductionMatrix, if_neg hg, if_neg hg]
    ext row column
    fin_cases row <;> fin_cases column <;>
      rw [_root_.Matrix.mul_apply,
        NormalForms.Matrix.Constructive.sum_univ_two] <;>
      simp <;>
      ring_nf at identity ⊢ <;>
      assumption

theorem boundedBezoutReductionMatrix_mul_inverse (a b : Int) :
    boundedBezoutReductionMatrix a b *
        boundedBezoutReductionInverseMatrix a b = 1 := by
  let data := boundedIntXGCD a b
  by_cases hg : data.gcd = 0
  · rw [boundedBezoutReductionInverseMatrix,
      boundedBezoutReductionMatrix, if_pos hg, if_pos hg]
    exact NormalForms.Matrix.Constructive.one_mul 1
  · have identity := boundedIntXGCD_divIdentity a b hg
    rw [boundedIntXGCD_gcd] at identity
    rw [boundedBezoutReductionInverseMatrix,
      boundedBezoutReductionMatrix, if_neg hg, if_neg hg]
    ext row column
    fin_cases row <;> fin_cases column <;>
      rw [_root_.Matrix.mul_apply,
        NormalForms.Matrix.Constructive.sum_univ_two] <;>
      simp <;>
      ring_nf at identity ⊢ <;>
      assumption

def boundedPairBezoutMatrix {n : Nat} (pivot target : Fin n)
    (a b : Int) : _root_.Matrix (Fin n) (Fin n) Int :=
  twoRowLiftMatrix pivot target (boundedBezoutReductionMatrix a b)

def boundedPairBezoutMatrixInverseCertificate {n : Nat}
    (pivot target : Fin n) (hne : pivot ≠ target) (a b : Int) :
    MatrixInverseCertificate (boundedPairBezoutMatrix pivot target a b) := by
  refine
    { inverse := twoRowLiftMatrix pivot target
        (boundedBezoutReductionInverseMatrix a b)
      left_inv := ?_
      right_inv := ?_ }
  · rw [boundedPairBezoutMatrix,
      twoRowLiftMatrix_mul pivot target hne,
      boundedBezoutReductionInverseMatrix_mul,
      twoRowLiftMatrix_one pivot target hne]
  · rw [boundedPairBezoutMatrix,
      twoRowLiftMatrix_mul pivot target hne,
      boundedBezoutReductionMatrix_mul_inverse,
      twoRowLiftMatrix_one pivot target hne]

end Principal

end NormalForms.Research.KannanBachem.Hermite
