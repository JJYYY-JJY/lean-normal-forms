/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.Representation

/-! # Costed Binary Magnitude Comparison -/

public section

namespace NormalForms.Research.BitCost

namespace Internal

/--
Compare two positive binary words while charging the constructor inspections.
The result and cost are produced by the same structural recursion.
-/
@[expose] public def positiveMagnitudeCompareWithCost :
    PosNum → PosNum → WithCost Ordering
  | .one, .one => { value := .eq, cost := 1 }
  | .one, .bit0 _ => { value := .lt, cost := 1 }
  | .one, .bit1 _ => { value := .lt, cost := 1 }
  | .bit0 _, .one => { value := .gt, cost := 1 }
  | .bit1 _, .one => { value := .gt, cost := 1 }
  | .bit0 left, .bit0 right =>
      let run := positiveMagnitudeCompareWithCost left right
      { value := run.value, cost := run.cost + 1 }
  | .bit1 left, .bit1 right =>
      let run := positiveMagnitudeCompareWithCost left right
      { value := run.value, cost := run.cost + 1 }
  | .bit0 left, .bit1 right =>
      let run := positiveMagnitudeCompareWithCost left right
      { value := if run.value = .eq then .lt else run.value
        cost := run.cost + 1 }
  | .bit1 left, .bit0 right =>
      let run := positiveMagnitudeCompareWithCost left right
      { value := if run.value = .eq then .gt else run.value
        cost := run.cost + 1 }

public theorem positiveMagnitudeCompareWithCost_value
    (left right : PosNum) :
    (positiveMagnitudeCompareWithCost left right).value =
      compare (left : Nat) (right : Nat) := by
  induction left, right using positiveMagnitudeCompareWithCost.induct with
  | case1 => rfl
  | case2 right =>
      rw [positiveMagnitudeCompareWithCost]
      symm
      apply Nat.compare_eq_lt.mpr
      have positive : 0 < (right : Nat) := PosNum.cast_pos right
      change 1 < (right : Nat) + right
      omega
  | case3 right =>
      rw [positiveMagnitudeCompareWithCost]
      symm
      apply Nat.compare_eq_lt.mpr
      have positive : 0 < (right : Nat) := PosNum.cast_pos right
      change 1 < (right : Nat) + right + 1
      omega
  | case4 left =>
      rw [positiveMagnitudeCompareWithCost]
      symm
      apply Nat.compare_eq_gt.mpr
      have positive : 0 < (left : Nat) := PosNum.cast_pos left
      change 1 < (left : Nat) + left
      omega
  | case5 left =>
      rw [positiveMagnitudeCompareWithCost]
      symm
      apply Nat.compare_eq_gt.mpr
      have positive : 0 < (left : Nat) := PosNum.cast_pos left
      change 1 < (left : Nat) + left + 1
      omega
  | case6 left right ih =>
      simp only [positiveMagnitudeCompareWithCost, ih]
      rcases lt_trichotomy (left : Nat) (right : Nat) with h | h | h
      · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr]
        simpa only [PosNum.cast_bit0] using Nat.add_lt_add h h
      · rw [Nat.compare_eq_eq.mpr h, Nat.compare_eq_eq.mpr]
        simpa only [PosNum.cast_bit0] using congrArg (fun n : Nat => n + n) h
      · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr]
        simpa only [PosNum.cast_bit0] using Nat.add_lt_add h h
  | case7 left right ih =>
      simp only [positiveMagnitudeCompareWithCost, ih]
      rcases lt_trichotomy (left : Nat) (right : Nat) with h | h | h
      · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr]
        simpa only [PosNum.cast_bit1] using
          Nat.add_lt_add_right (Nat.add_lt_add h h) 1
      · rw [Nat.compare_eq_eq.mpr h, Nat.compare_eq_eq.mpr]
        simp only [PosNum.cast_bit1, h]
      · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr]
        simpa only [PosNum.cast_bit1] using
          Nat.add_lt_add_right (Nat.add_lt_add h h) 1
  | case8 left right ih =>
      simp only [positiveMagnitudeCompareWithCost, ih]
      rcases lt_trichotomy (left : Nat) (right : Nat) with h | h | h
      · rw [Nat.compare_eq_lt.mpr h, if_neg (by decide), Nat.compare_eq_lt.mpr]
        simp only [PosNum.cast_bit0, PosNum.cast_bit1]
        omega
      · rw [Nat.compare_eq_eq.mpr h, if_pos rfl, Nat.compare_eq_lt.mpr]
        simp only [PosNum.cast_bit0, PosNum.cast_bit1]
        omega
      · rw [Nat.compare_eq_gt.mpr h, if_neg (by decide), Nat.compare_eq_gt.mpr]
        simp only [PosNum.cast_bit0, PosNum.cast_bit1]
        omega
  | case9 left right ih =>
      simp only [positiveMagnitudeCompareWithCost, ih]
      rcases lt_trichotomy (left : Nat) (right : Nat) with h | h | h
      · rw [Nat.compare_eq_lt.mpr h, if_neg (by decide), Nat.compare_eq_lt.mpr]
        simp only [PosNum.cast_bit0, PosNum.cast_bit1]
        omega
      · rw [Nat.compare_eq_eq.mpr h, if_pos rfl, Nat.compare_eq_gt.mpr]
        simp only [PosNum.cast_bit0, PosNum.cast_bit1]
        omega
      · rw [Nat.compare_eq_gt.mpr h, if_neg (by decide), Nat.compare_eq_gt.mpr]
        simp only [PosNum.cast_bit0, PosNum.cast_bit1]
        omega

public theorem positiveMagnitudeCompareWithCost_cost_le
    (left right : PosNum) :
    (positiveMagnitudeCompareWithCost left right).cost ≤
      left.natSize + right.natSize := by
  induction left, right using positiveMagnitudeCompareWithCost.induct with
  | case1 => simp [positiveMagnitudeCompareWithCost, PosNum.natSize]
  | case2 right =>
      simp only [positiveMagnitudeCompareWithCost, PosNum.natSize]
      have positive := PosNum.natSize_pos right
      omega
  | case3 right =>
      simp only [positiveMagnitudeCompareWithCost, PosNum.natSize]
      have positive := PosNum.natSize_pos right
      omega
  | case4 left =>
      simp only [positiveMagnitudeCompareWithCost, PosNum.natSize]
      have positive := PosNum.natSize_pos left
      omega
  | case5 left =>
      simp only [positiveMagnitudeCompareWithCost, PosNum.natSize]
      have positive := PosNum.natSize_pos left
      omega
  | case6 left right ih =>
      simp only [positiveMagnitudeCompareWithCost, PosNum.natSize]
      omega
  | case7 left right ih =>
      simp only [positiveMagnitudeCompareWithCost, PosNum.natSize]
      omega
  | case8 left right ih =>
      simp only [positiveMagnitudeCompareWithCost, PosNum.natSize]
      omega
  | case9 left right ih =>
      simp only [positiveMagnitudeCompareWithCost, PosNum.natSize]
      omega

/-- Structural magnitude comparison on unsigned binary words. -/
@[expose] public def numMagnitudeCompareWithCost : Num → Num → WithCost Ordering
  | .zero, .zero => { value := .eq, cost := 1 }
  | .zero, .pos _ => { value := .lt, cost := 1 }
  | .pos _, .zero => { value := .gt, cost := 1 }
  | .pos left, .pos right =>
      let run := positiveMagnitudeCompareWithCost left right
      { value := run.value, cost := run.cost + 1 }

public theorem numMagnitudeCompareWithCost_value (left right : Num) :
    (numMagnitudeCompareWithCost left right).value =
      compare (left : Nat) (right : Nat) := by
  cases left with
  | zero =>
      cases right with
      | zero => rfl
      | pos right =>
          rw [numMagnitudeCompareWithCost]
          symm
          apply Nat.compare_eq_lt.mpr
          change (0 : Nat) < (right : Nat)
          exact PosNum.cast_pos right
  | pos left =>
      cases right with
      | zero =>
          rw [numMagnitudeCompareWithCost]
          symm
          apply Nat.compare_eq_gt.mpr
          change (0 : Nat) < (left : Nat)
          exact PosNum.cast_pos left
      | pos right =>
          simpa only [numMagnitudeCompareWithCost, Num.cast_pos] using
            positiveMagnitudeCompareWithCost_value left right

public theorem numMagnitudeCompareWithCost_cost_le (left right : Num) :
    (numMagnitudeCompareWithCost left right).cost ≤
      left.natSize + right.natSize + 1 := by
  cases left with
  | zero =>
      cases right <;> simp [numMagnitudeCompareWithCost, Num.natSize]
  | pos left =>
      cases right with
      | zero => simp [numMagnitudeCompareWithCost, Num.natSize]
      | pos right =>
          simp only [numMagnitudeCompareWithCost, Num.natSize]
          exact Nat.add_le_add_right
            (positiveMagnitudeCompareWithCost_cost_le left right) 1

end Internal

/-- Costed inspection of the canonical zero constructor. -/
@[expose] public def isZeroWithCost (value : SignMagnitude) : WithCost Bool :=
  match value with
  | .zero => { value := true, cost := 1 }
  | .pos _ => { value := false, cost := 1 }
  | .neg _ => { value := false, cost := 1 }

@[simp] public theorem isZeroWithCost_value (value : SignMagnitude) :
    (isZeroWithCost value).value = decide (value.value = 0) := by
  cases value with
  | zero => simp [isZeroWithCost, SignMagnitude.value]
  | pos magnitude | neg magnitude =>
      have positive : (0 : Int) < (magnitude : Int) := PosNum.cast_pos magnitude
      simp [isZeroWithCost, SignMagnitude.value, ne_of_gt positive]

@[simp] public theorem isZeroWithCost_cost (value : SignMagnitude) :
    (isZeroWithCost value).cost = 1 := by
  cases value <;> rfl

/-- Costed comparison of two sign-magnitude absolute values. -/
@[expose] public def magnitudeCompareWithCost
    (left right : SignMagnitude) : WithCost Ordering :=
  Internal.numMagnitudeCompareWithCost left.magnitude right.magnitude

public theorem magnitudeCompareWithCost_value
    (left right : SignMagnitude) :
    (magnitudeCompareWithCost left right).value =
      compare left.value.natAbs right.value.natAbs := by
  rw [magnitudeCompareWithCost, Internal.numMagnitudeCompareWithCost_value]
  simp only [SignMagnitude.magnitude_value]

/-- Binary comparison budget used by the execution work envelope. -/
@[expose] public def magnitudeCompareBitOperationBound
    (left right : SignMagnitude) : Nat :=
  left.bitLength + right.bitLength + 1

public theorem magnitudeCompareWithCost_cost_le
    (left right : SignMagnitude) :
    (magnitudeCompareWithCost left right).cost ≤
      magnitudeCompareBitOperationBound left right := by
  simpa only [magnitudeCompareWithCost, magnitudeCompareBitOperationBound,
    SignMagnitude.bitLength_eq_natSize_magnitude] using
    Internal.numMagnitudeCompareWithCost_cost_le left.magnitude right.magnitude

/-- Costed absolute-value comparison as a Boolean relation. -/
@[expose] public def magnitudeLeWithCost
    (left right : SignMagnitude) : WithCost Bool :=
  let run := magnitudeCompareWithCost left right
  { value := run.value.isLE, cost := run.cost }

@[simp] public theorem magnitudeLeWithCost_value
    (left right : SignMagnitude) :
    (magnitudeLeWithCost left right).value =
      decide (left.value.natAbs ≤ right.value.natAbs) := by
  rw [magnitudeLeWithCost, magnitudeCompareWithCost_value]
  rcases lt_trichotomy left.value.natAbs right.value.natAbs with h | h | h
  · rw [Nat.compare_eq_lt.mpr h]
    simp [h.le]
  · rw [Nat.compare_eq_eq.mpr h]
    simp [h]
  · rw [Nat.compare_eq_gt.mpr h]
    simp [Nat.not_le.mpr h]

public theorem magnitudeLeWithCost_cost_le
    (left right : SignMagnitude) :
    (magnitudeLeWithCost left right).cost ≤
      magnitudeCompareBitOperationBound left right :=
  magnitudeCompareWithCost_cost_le left right

end NormalForms.Research.BitCost
