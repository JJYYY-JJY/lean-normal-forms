/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.Addition

/-!
# Costed Schoolbook Multiplication

The positive-word counter mirrors `PosNum.mul`: it scans the right operand
from least significant bit to most significant bit, shifts the recursive
partial product, and performs one costed addition for each set bit. Signs are
then handled by the outer `ZNum.mul` constructor cases.
-/

public section

namespace NormalForms.Research.BitCost

namespace Internal

/--
Exact constructor and addition work performed by binary schoolbook
multiplication.
-/
@[expose] public def positiveMulSteps (left : PosNum) : PosNum → Nat
  | .one => 1
  | .bit0 right =>
      1 + positiveMulSteps left right
  | .bit1 right =>
      1 + positiveMulSteps left right +
        positiveAddSteps (.bit0 (left * right)) left

/-- Exact constructor inspections for sign-magnitude multiplication. -/
@[expose] public def signMagnitudeMulSteps :
    SignMagnitude → SignMagnitude → Nat
  | .zero, _ => 1
  | _, .zero => 1
  | .pos left, .pos right => 1 + positiveMulSteps left right
  | .pos left, .neg right => 1 + positiveMulSteps left right
  | .neg left, .pos right => 1 + positiveMulSteps left right
  | .neg left, .neg right => 1 + positiveMulSteps left right

/-- A positive product has no more bits than the sum of input bit lengths. -/
public theorem positiveMul_natSize_le (left right : PosNum) :
    (left * right).natSize ≤ left.natSize + right.natSize := by
  rw [PosNum.natSize_to_nat, PosNum.mul_to_nat,
    PosNum.natSize_to_nat, PosNum.natSize_to_nat]
  rw [Nat.size_le, pow_add]
  exact mul_lt_mul''
    (Nat.lt_size_self (left : Nat))
    (Nat.lt_size_self (right : Nat))
    (Nat.zero_le _)
    (Nat.zero_le _)

/-- Binary length of a natural-number product is bounded by input lengths. -/
public theorem natSize_mul_le (left right : Nat) :
    Nat.size (left * right) ≤
      Nat.size left + Nat.size right := by
  rw [Nat.size_le, pow_add]
  exact mul_lt_mul''
    (Nat.lt_size_self left)
    (Nat.lt_size_self right)
    (Nat.zero_le _)
    (Nat.zero_le _)

/--
The exact schoolbook count is bounded by the number of scanned right-hand
bits times a quadratic budget for each conditional addition.
-/
public theorem positiveMulSteps_le (left right : PosNum) :
    positiveMulSteps left right ≤
      right.natSize *
        (1 + (2 * left.natSize + right.natSize + 2) ^ 2) := by
  induction right with
  | one =>
      simp only [positiveMulSteps, PosNum.natSize]
      nlinarith
  | bit0 right ih =>
      simp only [positiveMulSteps, PosNum.natSize,
        Nat.succ_eq_add_one] at ih ⊢
      let oldFactor :=
        1 + (2 * left.natSize + right.natSize + 2) ^ 2
      let newFactor :=
        1 + (2 * left.natSize + (right.natSize + 1) + 2) ^ 2
      have baseMono :
          2 * left.natSize + right.natSize + 2 ≤
            2 * left.natSize + (right.natSize + 1) + 2 := by
        omega
      have factorMono : oldFactor ≤ newFactor := by
        simp only [oldFactor, newFactor]
        exact Nat.add_le_add_left (Nat.pow_le_pow_left baseMono 2) 1
      have ih' :
          positiveMulSteps left right ≤
            right.natSize * newFactor :=
        ih.trans (Nat.mul_le_mul_left right.natSize factorMono)
      have oneLe : 1 ≤ newFactor := by
        simp only [newFactor]
        omega
      change 1 + positiveMulSteps left right ≤
        (right.natSize + 1) * newFactor
      calc
        1 + positiveMulSteps left right ≤
            newFactor + right.natSize * newFactor :=
          Nat.add_le_add oneLe ih'
        _ = (right.natSize + 1) * newFactor := by ring
  | bit1 right ih =>
      simp only [positiveMulSteps, PosNum.natSize,
        Nat.succ_eq_add_one] at ih ⊢
      let oldFactor :=
        1 + (2 * left.natSize + right.natSize + 2) ^ 2
      let newBase :=
        2 * left.natSize + (right.natSize + 1) + 2
      let newFactor := 1 + newBase ^ 2
      have baseMono :
          2 * left.natSize + right.natSize + 2 ≤ newBase := by
        simp only [newBase]
        omega
      have factorMono : oldFactor ≤ newFactor := by
        simp only [oldFactor, newFactor]
        exact Nat.add_le_add_left (Nat.pow_le_pow_left baseMono 2) 1
      have ih' :
          positiveMulSteps left right ≤
            right.natSize * newFactor :=
        ih.trans (Nat.mul_le_mul_left right.natSize factorMono)
      have productWidth := positiveMul_natSize_le left right
      have addBound :=
        positiveAddSteps_le (.bit0 (left * right)) left
      simp only [PosNum.natSize, Nat.succ_eq_add_one] at addBound
      have addBase :
          (left * right).natSize + 1 + left.natSize + 1 ≤
            newBase := by
        simp only [newBase]
        omega
      have addBound' :
          positiveAddSteps (.bit0 (left * right)) left ≤
            newBase ^ 2 :=
        addBound.trans (Nat.pow_le_pow_left addBase 2)
      have stepCharge :
          1 + positiveAddSteps (.bit0 (left * right)) left ≤
            newFactor := by
        simp only [newFactor]
        exact Nat.add_le_add_left addBound' 1
      change
        1 + positiveMulSteps left right +
            positiveAddSteps (.bit0 (left * right)) left ≤
          (right.natSize + 1) * newFactor
      calc
        1 + positiveMulSteps left right +
              positiveAddSteps (.bit0 (left * right)) left =
            positiveMulSteps left right +
              (1 + positiveAddSteps (.bit0 (left * right)) left) := by
          omega
        _ ≤ right.natSize * newFactor + newFactor :=
          Nat.add_le_add ih' stepCharge
        _ = (right.natSize + 1) * newFactor := by ring

end Internal

/--
Reference binary sign-magnitude multiplication with its exact modeled
schoolbook bit-step count.
-/
@[expose] public def mulWithCost
    (left right : SignMagnitude) : WithCost SignMagnitude :=
  { value := left * right
    cost := Internal.signMagnitudeMulSteps left right }

/-- The reference result agrees with standard integer multiplication. -/
@[simp] public theorem mulWithCost_value
    (left right : SignMagnitude) :
    (mulWithCost left right).value.value =
      left.value * right.value := by
  exact ZNum.mul_to_int left right

/-- Schoolbook multiplication adds the two coefficient bit lengths. -/
public theorem mulWithCost_value_bitLength_le
    (left right : SignMagnitude) :
    (mulWithCost left right).value.bitLength ≤
      left.bitLength + right.bitLength := by
  rw [SignMagnitude.bitLength_eq_natSize_natAbs,
    SignMagnitude.bitLength_eq_natSize_natAbs,
    SignMagnitude.bitLength_eq_natSize_natAbs,
    mulWithCost_value, Int.natAbs_mul]
  exact Internal.natSize_mul_le
    (Int.natAbs left.value) (Int.natAbs right.value)

/-- Explicit worst-case bit-operation budget for schoolbook multiplication. -/
@[expose] public def mulBitOperationBound
    (left right : SignMagnitude) : Nat :=
  1 + right.bitLength *
    (1 + (2 * left.bitLength + right.bitLength + 2) ^ 2)

/--
The exact modeled shift-and-add count is bounded cubically in the operand bit
lengths.
-/
public theorem mulWithCost_cost_le
    (left right : SignMagnitude) :
    (mulWithCost left right).cost ≤
      mulBitOperationBound left right := by
  cases left with
  | zero =>
      cases right <;>
        norm_num [mulWithCost, Internal.signMagnitudeMulSteps,
          mulBitOperationBound, SignMagnitude.bitLength]
  | pos left | neg left =>
      cases right with
      | zero =>
          norm_num [mulWithCost, Internal.signMagnitudeMulSteps,
            mulBitOperationBound, SignMagnitude.bitLength]
      | pos right | neg right =>
          simp only [mulWithCost, Internal.signMagnitudeMulSteps,
            mulBitOperationBound, SignMagnitude.bitLength]
          exact Nat.add_le_add_left
            (Internal.positiveMulSteps_le left right) 1

end NormalForms.Research.BitCost
