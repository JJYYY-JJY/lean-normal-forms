/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.NormalizedXGCD

/-!
# Euclidean Iteration Bounds

This file isolates the natural-number Euclidean quotient sequence used by the
sign-normalized extended-gcd wrapper.  Once the operands are ordered, the
product of consecutive positive remainders loses at least one binary digit at
each step.  The resulting iteration bound is linear in the two input bit
lengths.
-/

public section

namespace NormalForms.Research.BitCost

/-- Number of nonterminal divisions in the natural Euclidean algorithm. -/
@[expose] public def euclideanIterations : Nat → Nat → Nat
  | _, 0 => 0
  | left, right + 1 =>
      1 + euclideanIterations (right + 1) (left % (right + 1))
termination_by _ right => right
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

@[simp] public theorem euclideanIterations_zero (left : Nat) :
    euclideanIterations left 0 = 0 := by
  rw [euclideanIterations]

public theorem euclideanIterations_succ (left right : Nat) :
    euclideanIterations left (right + 1) =
      1 + euclideanIterations (right + 1) (left % (right + 1)) := by
  rw [euclideanIterations]

public theorem euclideanIterations_of_pos
    (left right : Nat) (rightPositive : 0 < right) :
    euclideanIterations left right =
      1 + euclideanIterations right (left % right) := by
  cases right with
  | zero => omega
  | succ right => exact euclideanIterations_succ left right

namespace Internal

/-- For positive naturals, binary length is `log2 + 1`. -/
public theorem natSize_eq_log2_add_one {value : Nat} (positive : 0 < value) :
    Nat.size value = value.log2 + 1 := by
  have nonzero : value ≠ 0 := Nat.ne_of_gt positive
  have bounds := (Nat.log2_eq_iff nonzero).1 rfl
  apply Nat.le_antisymm
  · exact Nat.size_le.mpr bounds.2
  · by_contra notLe
    have sizeLe : Nat.size value ≤ value.log2 := by omega
    have below := Nat.size_le.mp sizeLe
    exact (not_lt_of_ge bounds.1) below

/-- Losing a factor of two strictly decreases binary length. -/
public theorem natSize_lt_of_two_mul_le {smaller larger : Nat}
    (smallerPositive : 0 < smaller)
    (halved : 2 * smaller ≤ larger) :
    Nat.size smaller < Nat.size larger := by
  have largerPositive : 0 < larger :=
    lt_of_lt_of_le (Nat.mul_pos (by decide) smallerPositive) halved
  have smallerNonzero : smaller ≠ 0 := Nat.ne_of_gt smallerPositive
  have largerNonzero : larger ≠ 0 := Nat.ne_of_gt largerPositive
  have powerLeSmaller : 2 ^ smaller.log2 ≤ smaller :=
    Nat.log2_self_le smallerNonzero
  have powerLeLarger : 2 ^ (2 * smaller).log2 ≤ larger :=
    (Nat.log2_self_le (Nat.mul_ne_zero (by decide) smallerNonzero)).trans halved
  have logLe : (2 * smaller).log2 ≤ larger.log2 :=
    (Nat.le_log2 largerNonzero).2 powerLeLarger
  rw [Nat.log2_two_mul smallerNonzero] at logLe
  rw [natSize_eq_log2_add_one smallerPositive,
    natSize_eq_log2_add_one largerPositive]
  omega

/-- In an ordered Euclidean state the next consecutive product halves. -/
public theorem two_mul_nextProduct_le
    {left right : Nat} (rightPositive : 0 < right)
    (ordered : right ≤ left) :
    2 * (right * (left % right)) ≤ left * right := by
  let remainder := left % right
  let quotient := left / right
  have quotientPositive : 0 < quotient := Nat.div_pos ordered rightPositive
  have remainderLt : remainder < right := Nat.mod_lt left rightPositive
  have rightLeProduct : right ≤ right * quotient := by
    simpa using Nat.mul_le_mul_left right
      (Nat.succ_le_iff.mpr quotientPositive)
  have rightAddRemainderLe : right + remainder ≤ left := by
    have decomposition : remainder + right * quotient = left :=
      Nat.mod_add_div left right
    omega
  have first : 2 * (right * remainder) ≤ (right + remainder) * right := by
    have productLe : right * remainder ≤ right * right :=
      Nat.mul_le_mul_left right remainderLt.le
    nlinarith
  exact first.trans (Nat.mul_le_mul_right right rightAddRemainderLe)

end Internal

/-- Ordered Euclidean inputs take at most the product's binary length steps. -/
public theorem euclideanIterations_le_productSize
    (left right : Nat) (ordered : right ≤ left) :
    euclideanIterations left right ≤ Nat.size (left * right) := by
  cases right with
  | zero => simp
  | succ right =>
      rw [euclideanIterations_succ]
      let divisor := right + 1
      by_cases remainderZero : left % divisor = 0
      · rw [remainderZero, euclideanIterations_zero, Nat.add_zero]
        have productPositive : 0 < left * divisor :=
          Nat.mul_pos (lt_of_lt_of_le (Nat.succ_pos right) ordered)
            (Nat.succ_pos right)
        exact (Nat.size_pos.mpr productPositive)
      · have remainderPositive : 0 < left % divisor :=
          Nat.pos_of_ne_zero remainderZero
        have remainderLt : left % divisor < divisor :=
          Nat.mod_lt left (Nat.succ_pos right)
        have recursiveBound :=
          euclideanIterations_le_productSize divisor (left % divisor)
            remainderLt.le
        have nextPositive : 0 < divisor * (left % divisor) :=
          Nat.mul_pos (Nat.succ_pos right) remainderPositive
        have halves : 2 * (divisor * (left % divisor)) ≤ left * divisor :=
          Internal.two_mul_nextProduct_le (Nat.succ_pos right) ordered
        have sizeDecrease :
            Nat.size (divisor * (left % divisor)) <
              Nat.size (left * divisor) :=
          Internal.natSize_lt_of_two_mul_le nextPositive halves
        simpa only [divisor, Nat.succ_eq_add_one, Nat.add_comm] using
          Nat.succ_le_iff.mpr
            (lt_of_le_of_lt recursiveBound sizeDecrease)

/-- Arbitrary Euclidean inputs need at most one initial ordering step. -/
public theorem euclideanIterations_le_bitLengths (left right : Nat) :
    euclideanIterations left right ≤
      Nat.size left + Nat.size right + 1 := by
  cases right with
  | zero => simp
  | succ right =>
      let divisor := right + 1
      change euclideanIterations left divisor ≤
        Nat.size left + Nat.size divisor + 1
      by_cases ordered : divisor ≤ left
      · have productBound := euclideanIterations_le_productSize left divisor ordered
        have productSize := Internal.natSize_mul_le left divisor
        omega
      · have leftLt : left < divisor := Nat.lt_of_not_ge ordered
        rw [euclideanIterations_succ, Nat.mod_eq_of_lt leftLt]
        have swapped := euclideanIterations_le_productSize divisor left leftLt.le
        have productSize := Internal.natSize_mul_le divisor left
        simp only [divisor] at swapped productSize ⊢
        omega

end NormalForms.Research.BitCost
