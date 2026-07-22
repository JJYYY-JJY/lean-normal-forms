/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.Representation
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic

/-!
# Costed Schoolbook Addition

The step counters in this module mirror the recursive binary definitions of
`PosNum.succ`, `PosNum.pred'`, `PosNum.add`, `PosNum.sub'`, and `ZNum.add`.
One step is charged for each constructor/bit case inspected. Recursive carry
and borrow propagation is charged explicitly.

The public result is intentionally conservative: the exact modeled count is
returned, then bounded by a polynomial in the two input bit lengths.
-/

public section

namespace NormalForms.Research.BitCost

namespace Internal

/-- Bit inspections performed by binary successor. -/
@[expose] public def positiveSuccSteps : PosNum → Nat
  | .one => 1
  | .bit0 _ => 1
  | .bit1 magnitude => 1 + positiveSuccSteps magnitude

/-- Bit inspections performed by binary predecessor. -/
@[expose] public def positivePredSteps : PosNum → Nat
  | .one => 1
  | .bit0 magnitude => 1 + positivePredSteps magnitude
  | .bit1 _ => 1

/--
Exact constructor inspections for `PosNum.add`, including work performed by
carry propagation through `PosNum.succ`.
-/
@[expose] public def positiveAddSteps : PosNum → PosNum → Nat
  | .one, right => 1 + positiveSuccSteps right
  | left, .one => 1 + positiveSuccSteps left
  | .bit0 left, .bit0 right =>
      1 + positiveAddSteps left right
  | .bit1 left, .bit1 right =>
      1 + positiveAddSteps left right +
        positiveSuccSteps (left + right)
  | .bit0 left, .bit1 right =>
      1 + positiveAddSteps left right
  | .bit1 left, .bit0 right =>
      1 + positiveAddSteps left right

/--
Exact constructor inspections for `PosNum.sub'`, including the terminal
borrow propagated by `PosNum.pred'`.
-/
@[expose] public def positiveSubSteps : PosNum → PosNum → Nat
  | left, .one => 1 + positivePredSteps left
  | .one, right => 1 + positivePredSteps right
  | .bit0 left, .bit0 right =>
      1 + positiveSubSteps left right
  | .bit0 left, .bit1 right =>
      1 + positiveSubSteps left right
  | .bit1 left, .bit0 right =>
      1 + positiveSubSteps left right
  | .bit1 left, .bit1 right =>
      1 + positiveSubSteps left right

/-- Exact binary constructor inspections for sign-magnitude addition. -/
@[expose] public def signMagnitudeAddSteps :
    SignMagnitude → SignMagnitude → Nat
  | .zero, _ => 1
  | _, .zero => 1
  | .pos left, .pos right => 1 + positiveAddSteps left right
  | .pos left, .neg right => 1 + positiveSubSteps left right
  | .neg left, .pos right => 1 + positiveSubSteps right left
  | .neg left, .neg right => 1 + positiveAddSteps left right

public theorem positiveSuccSteps_le (magnitude : PosNum) :
    positiveSuccSteps magnitude ≤ magnitude.natSize := by
  induction magnitude with
  | one => rfl
  | bit0 magnitude ih =>
      simp only [positiveSuccSteps, PosNum.natSize]
      omega
  | bit1 magnitude ih =>
      simp only [positiveSuccSteps, PosNum.natSize]
      omega

public theorem positivePredSteps_le (magnitude : PosNum) :
    positivePredSteps magnitude ≤ magnitude.natSize := by
  induction magnitude with
  | one => rfl
  | bit0 magnitude ih =>
      simp only [positivePredSteps, PosNum.natSize]
      omega
  | bit1 magnitude ih =>
      simp only [positivePredSteps, PosNum.natSize]
      omega

/-- Adding positive binary words increases bit length by at most this sum. -/
public theorem positiveAdd_natSize_le (left right : PosNum) :
    (left + right).natSize ≤ left.natSize + right.natSize + 1 := by
  rw [PosNum.natSize_to_nat, PosNum.add_to_nat,
    PosNum.natSize_to_nat, PosNum.natSize_to_nat]
  apply Nat.size_le.mpr
  let width := Nat.size (left : Nat) + Nat.size (right : Nat)
  have leftLt : (left : Nat) < 2 ^ Nat.size (left : Nat) :=
    Nat.lt_size_self _
  have rightLt : (right : Nat) < 2 ^ Nat.size (right : Nat) :=
    Nat.lt_size_self _
  have leftWidth :
      Nat.size (left : Nat) ≤ width := by
    simp [width]
  have rightWidth :
      Nat.size (right : Nat) ≤ width := by
    simp [width]
  have leftLt' : (left : Nat) < 2 ^ width :=
    lt_of_lt_of_le leftLt
      (Nat.pow_le_pow_right (by decide) leftWidth)
  have rightLt' : (right : Nat) < 2 ^ width :=
    lt_of_lt_of_le rightLt
      (Nat.pow_le_pow_right (by decide) rightWidth)
  calc
    (left : Nat) + (right : Nat) <
        2 ^ width + 2 ^ width :=
      Nat.add_lt_add leftLt' rightLt'
    _ = 2 ^ (width + 1) := by
      rw [pow_succ]
      omega

/-- Binary length of a natural-number sum is bounded by input lengths. -/
public theorem natSize_add_le (left right : Nat) :
    Nat.size (left + right) ≤
      Nat.size left + Nat.size right + 1 := by
  apply Nat.size_le.mpr
  let width := Nat.size left + Nat.size right
  have leftLt : left < 2 ^ Nat.size left :=
    Nat.lt_size_self left
  have rightLt : right < 2 ^ Nat.size right :=
    Nat.lt_size_self right
  have leftWidth :
      Nat.size left ≤ width := by
    simp [width]
  have rightWidth :
      Nat.size right ≤ width := by
    simp [width]
  have leftLt' : left < 2 ^ width :=
    lt_of_lt_of_le leftLt
      (Nat.pow_le_pow_right (by decide) leftWidth)
  have rightLt' : right < 2 ^ width :=
    lt_of_lt_of_le rightLt
      (Nat.pow_le_pow_right (by decide) rightWidth)
  calc
    left + right < 2 ^ width + 2 ^ width :=
      Nat.add_lt_add leftLt' rightLt'
    _ = 2 ^ (width + 1) := by
      rw [pow_succ]
      omega

public theorem positiveSubSteps_le (left right : PosNum) :
    positiveSubSteps left right ≤ left.natSize + right.natSize := by
  induction left, right using positiveSubSteps.induct with
  | case1 left =>
      simp only [positiveSubSteps]
      have bound := positivePredSteps_le left
      simp only [PosNum.natSize]
      omega
  | case2 right =>
      simp only [positiveSubSteps]
      have bound := positivePredSteps_le right
      simp only [PosNum.natSize]
      omega
  | case3 left right ih =>
      simp only [positiveSubSteps, PosNum.natSize]
      omega
  | case4 left right ih =>
      simp only [positiveSubSteps, PosNum.natSize]
      omega
  | case5 left right ih =>
      simp only [positiveSubSteps, PosNum.natSize]
      omega
  | case6 left right ih =>
      simp only [positiveSubSteps, PosNum.natSize]
      omega

public theorem positiveAddSteps_le (left right : PosNum) :
    positiveAddSteps left right ≤
      (left.natSize + right.natSize + 1) ^ 2 := by
  induction left, right using positiveAddSteps.induct with
  | case1 right =>
      simp only [positiveAddSteps, PosNum.natSize]
      have bound := positiveSuccSteps_le right
      nlinarith
  | case2 left =>
      simp only [positiveAddSteps, PosNum.natSize]
      have bound := positiveSuccSteps_le left
      nlinarith
  | case3 left right ih | case5 left right ih | case6 left right ih =>
      simp only [positiveAddSteps, PosNum.natSize,
        Nat.succ_eq_add_one] at ih ⊢
      calc
        1 + positiveAddSteps left right ≤
            1 + (left.natSize + right.natSize + 1) ^ 2 :=
          Nat.add_le_add_left ih 1
        _ ≤
            (left.natSize + 1 + (right.natSize + 1) + 1) ^ 2 := by
          let width := left.natSize + right.natSize + 1
          have bound :
              1 + width ^ 2 ≤ (width + 2) ^ 2 := by
            calc
              1 + width ^ 2 ≤
                  width ^ 2 + (4 * width + 4) := by omega
              _ = (width + 2) ^ 2 := by ring
          have rewriteWidth :
              left.natSize + 1 + (right.natSize + 1) + 1 =
                width + 2 := by
            simp only [width]
            omega
          rw [rewriteWidth]
          exact bound
  | case4 left right ih =>
      simp only [positiveAddSteps, PosNum.natSize,
        Nat.succ_eq_add_one] at ih ⊢
      have carry := positiveSuccSteps_le (left + right)
      have width := positiveAdd_natSize_le left right
      calc
        1 + positiveAddSteps left right +
              positiveSuccSteps (left + right) ≤
            1 + (left.natSize + right.natSize + 1) ^ 2 +
              (left.natSize + right.natSize + 1) :=
          Nat.add_le_add (Nat.add_le_add_left ih 1)
            (carry.trans width)
        _ ≤
            (left.natSize + 1 + (right.natSize + 1) + 1) ^ 2 := by
          nlinarith

end Internal

/--
Reference binary sign-magnitude addition with its exact modeled bit-step
count.
-/
@[expose] public def addWithCost
    (left right : SignMagnitude) : WithCost SignMagnitude :=
  { value := left + right
    cost := Internal.signMagnitudeAddSteps left right }

/-- The reference result agrees with standard integer addition. -/
@[simp] public theorem addWithCost_value
    (left right : SignMagnitude) :
    (addWithCost left right).value.value =
      left.value + right.value := by
  exact ZNum.cast_add left right

/-- The sum's coefficient length is controlled by the two input lengths. -/
public theorem addWithCost_value_bitLength_le
    (left right : SignMagnitude) :
    (addWithCost left right).value.bitLength ≤
      left.bitLength + right.bitLength + 1 := by
  rw [SignMagnitude.bitLength_eq_natSize_natAbs,
    SignMagnitude.bitLength_eq_natSize_natAbs,
    SignMagnitude.bitLength_eq_natSize_natAbs,
    addWithCost_value]
  exact (Nat.size_le_size
    (Int.natAbs_add_le left.value right.value)).trans
      (Internal.natSize_add_le
        (Int.natAbs left.value) (Int.natAbs right.value))

/-- Explicit worst-case bit-operation budget for reference addition. -/
@[expose] public def addBitOperationBound
    (left right : SignMagnitude) : Nat :=
  1 + 2 * (left.bitLength + right.bitLength + 1) ^ 2

/--
The exact modeled constructor/bit count is bounded quadratically by the input
bit lengths. The loose square keeps the theorem compositional for later
coefficient-growth arguments.
-/
public theorem addWithCost_cost_le
    (left right : SignMagnitude) :
    (addWithCost left right).cost ≤
      addBitOperationBound left right := by
  cases left with
  | zero =>
      cases right <;>
        norm_num [addWithCost, Internal.signMagnitudeAddSteps,
          addBitOperationBound, SignMagnitude.bitLength]
  | pos left =>
      cases right with
      | zero =>
          norm_num [addWithCost, Internal.signMagnitudeAddSteps,
            addBitOperationBound, SignMagnitude.bitLength]
      | pos right =>
          simp only [addWithCost, Internal.signMagnitudeAddSteps,
            addBitOperationBound, SignMagnitude.bitLength]
          have bound := Internal.positiveAddSteps_le left right
          omega
      | neg right =>
          simp only [addWithCost, Internal.signMagnitudeAddSteps,
            addBitOperationBound, SignMagnitude.bitLength]
          have bound := Internal.positiveSubSteps_le left right
          have growth :
              left.natSize + right.natSize ≤
                2 * (left.natSize + right.natSize + 1) ^ 2 := by
            nlinarith
          omega
  | neg left =>
      cases right with
      | zero =>
          norm_num [addWithCost, Internal.signMagnitudeAddSteps,
            addBitOperationBound, SignMagnitude.bitLength]
      | pos right =>
          simp only [addWithCost, Internal.signMagnitudeAddSteps,
            addBitOperationBound, SignMagnitude.bitLength]
          have bound := Internal.positiveSubSteps_le right left
          have growth :
              right.natSize + left.natSize ≤
                2 * (left.natSize + right.natSize + 1) ^ 2 := by
            nlinarith
          omega
      | neg right =>
          simp only [addWithCost, Internal.signMagnitudeAddSteps,
            addBitOperationBound, SignMagnitude.bitLength]
          have bound := Internal.positiveAddSteps_le left right
          omega

end NormalForms.Research.BitCost
