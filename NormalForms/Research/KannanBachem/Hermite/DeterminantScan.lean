/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminantCost

/-!
# Charged First-Nonzero Determinant Scan

This module scans a finite list of labelled square matrices from left to right.
Every determinant is computed by the certified cached Bird evaluator, and the
cost includes both its exact scalar-arithmetic charge and one structural zero
test per inspected candidate.

The scanner is independent of principal preparation so the value projection,
success specification, and uniform cost theorem can be reused by later
certified algorithms.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

open NormalForms.Research.BitCost

namespace DivisionFreeDeterminant

/-- Scan labels from left to right using the exact charged determinant. -/
@[expose] public def scanFirstNonzeroWithCost {ι : Type*} {n : Nat}
    (matrixAt : ι → Matrix (Fin n) (Fin n) Int) :
    List ι → WithCost (Option ι)
  | [] => WithCost.pure none
  | index :: rest =>
      let determinant := evaluateWithCost (matrixAt index)
      if determinant.value = 0 then
        let following := scanFirstNonzeroWithCost matrixAt rest
        { value := following.value
          cost := determinant.cost + 1 + following.cost }
      else
        { value := some index
          cost := determinant.cost + 1 }

public theorem scanFirstNonzeroWithCost_none_iff {ι : Type*} {n : Nat}
    (matrixAt : ι → Matrix (Fin n) (Fin n) Int) (indices : List ι) :
    (scanFirstNonzeroWithCost matrixAt indices).value = none ↔
      ∀ index ∈ indices, (evaluateWithCost (matrixAt index)).value = 0 := by
  induction indices with
  | nil => simp [scanFirstNonzeroWithCost]
  | cons index rest ih =>
      simp only [scanFirstNonzeroWithCost]
      split_ifs with determinantZero
      · simp [ih, determinantZero]
      · simp [determinantZero]

public theorem scanFirstNonzeroWithCost_some_spec {ι : Type*} {n : Nat}
    (matrixAt : ι → Matrix (Fin n) (Fin n) Int) (indices : List ι)
    {found : ι}
    (result : (scanFirstNonzeroWithCost matrixAt indices).value = some found) :
    found ∈ indices ∧ (evaluateWithCost (matrixAt found)).value ≠ 0 := by
  induction indices with
  | nil => simp [scanFirstNonzeroWithCost] at result
  | cons index rest ih =>
      simp only [scanFirstNonzeroWithCost] at result
      split_ifs at result with determinantZero
      · obtain ⟨member, nonzero⟩ := ih result
        exact ⟨by simp [member], nonzero⟩
      · cases result
        exact ⟨by simp, determinantZero⟩

public theorem scanFirstNonzeroWithCost_cost_le {ι : Type*} {n : Nat}
    (matrixAt : ι → Matrix (Fin n) (Fin n) Int) (indices : List ι)
    (inputBits : Nat)
    (width : ∀ index ∈ indices,
      matrixBitLength (matrixAt index) ≤ inputBits) :
    (scanFirstNonzeroWithCost matrixAt indices).cost ≤
      indices.length * (determinantBitOperationBound n inputBits + 1) := by
  induction indices with
  | nil => simp [scanFirstNonzeroWithCost]
  | cons index rest ih =>
      have headWidth := width index (by simp)
      have tailWidth : ∀ next ∈ rest,
          matrixBitLength (matrixAt next) ≤ inputBits := by
        intro next member
        exact width next (by simp [member])
      have determinantCost :
          (evaluateWithCost (matrixAt index)).cost ≤
            determinantBitOperationBound n inputBits :=
        (evaluateWithCost_cost_le (matrixAt index)).trans
          (determinantBitOperationBound_mono_right n headWidth)
      have tailCost := ih tailWidth
      rw [scanFirstNonzeroWithCost]
      split_ifs
      · calc
          (evaluateWithCost (matrixAt index)).cost + 1 +
                (scanFirstNonzeroWithCost matrixAt rest).cost ≤
              determinantBitOperationBound n inputBits + 1 +
                rest.length *
                  (determinantBitOperationBound n inputBits + 1) :=
            Nat.add_le_add
              (Nat.add_le_add_right determinantCost 1) tailCost
          _ = (index :: rest).length *
              (determinantBitOperationBound n inputBits + 1) := by
            simp only [List.length_cons]
            ring
      · simpa only [List.length_cons, Nat.succ_mul] using
          (show (evaluateWithCost (matrixAt index)).cost + 1 ≤
              determinantBitOperationBound n inputBits + 1 from
            Nat.add_le_add_right determinantCost 1).trans (by omega)

end DivisionFreeDeterminant

end NormalForms.Research.KannanBachem.Hermite
