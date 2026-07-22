/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Matrix.Smith.Determinantal

set_option linter.privateModule false

/-!
# Intrinsic Smith-data regressions

These tests cover zero dimensions, rectangular matrices, a rank-deficient
zero tail, and retention of unit invariant factors.
-/

namespace NormalForms.Tests.SmithData

open scoped Matrix
open NormalForms.Matrix.Smith

private def zeroRows : _root_.Matrix (Fin 0) (Fin 3) Int := 0

private theorem zeroRows_isSmith : IsSmithNormalFormFin zeroRows :=
  .emptyRows zeroRows

private noncomputable def zeroRowsData : SmithData 0 3 Int :=
  SmithData.ofSmithMatrix zeroRows zeroRows_isSmith

example : zeroRowsData.rank = 0 := by
  rfl

example : zeroRowsData.signature.factors = 0 := by
  rfl

private def rankDeficient : _root_.Matrix (Fin 2) (Fin 3) Int :=
  !![1, 0, 0;
     0, 0, 0]

private theorem rankDeficient_diag :
    Internal.IsSmithNormalFormDiag rankDeficient := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [rankDeficient] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      norm_num [Internal.diagEntry, rankDeficient]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [Internal.diagEntry, rankDeficient]

private theorem rankDeficient_isSmith :
    IsSmithNormalFormFin rankDeficient :=
  Internal.isSmithNormalFormDiag_toFin rankDeficient_diag

private noncomputable def rankDeficientData : SmithData 2 3 Int :=
  SmithData.ofSmithMatrix rankDeficient rankDeficient_isSmith

private def diagonalZero : Fin (Nat.min 2 3) := ⟨0, by norm_num [Nat.min_def]⟩
private def diagonalOne : Fin (Nat.min 2 3) := ⟨1, by norm_num [Nat.min_def]⟩

example : rankDeficientData.rank = 1 := by
  rfl

example : rankDeficientData.diagonal diagonalZero = 1 := by
  rfl

example : rankDeficientData.diagonal diagonalOne = 0 := by
  rfl

example :
    rankDeficientData.diagonal diagonalZero ∣
      rankDeficientData.diagonal diagonalOne :=
  rankDeficientData.divisibility diagonalZero diagonalOne
    (by norm_num [diagonalZero, diagonalOne])

example :
    rankDeficientData.signature.factors =
      Multiset.ofList [Associates.mk (1 : Int)] := by
  rfl

example : rankDeficientData.signature.rightKernelRank = 2 := by
  rfl

example : rankDeficientData.signature.leftKernelRank = 1 := by
  rfl

example : rankDeficientData.signature.cokernelFreeRank = 1 := by
  rfl

private def rectangularWithUnit : _root_.Matrix (Fin 2) (Fin 3) Int :=
  !![1, 0, 0;
     0, 2, 0]

private theorem rectangularWithUnit_diag :
    Internal.IsSmithNormalFormDiag rectangularWithUnit := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [rectangularWithUnit] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      simp [Internal.diagEntry, rectangularWithUnit, Int.normalize_of_nonneg]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [Internal.diagEntry, rectangularWithUnit]

private theorem rectangularWithUnit_isSmith :
    IsSmithNormalFormFin rectangularWithUnit :=
  Internal.isSmithNormalFormDiag_toFin rectangularWithUnit_diag

private noncomputable def rectangularWithUnitData : SmithData 2 3 Int :=
  SmithData.ofSmithMatrix rectangularWithUnit rectangularWithUnit_isSmith

example : rectangularWithUnitData.rank = 2 := by
  rfl

example : rectangularWithUnitData.diagonal diagonalZero = 1 := by
  rfl

example : rectangularWithUnitData.diagonal diagonalOne = 2 := by
  rfl

example :
    rectangularWithUnitData.diagonal diagonalZero ∣
      rectangularWithUnitData.diagonal diagonalOne :=
  rectangularWithUnitData.divisibility diagonalZero diagonalOne
    (by norm_num [diagonalZero, diagonalOne])

example :
    rectangularWithUnitData.signature.factors =
      Multiset.ofList [Associates.mk (1 : Int), Associates.mk (2 : Int)] := by
  rfl

example :
    ∀ factor ∈ rectangularWithUnitData.signature.factors, factor ≠ 0 :=
  rectangularWithUnitData.signature.nonzero

example : determinantalIdealFin rankDeficient 0 = ⊤ :=
  determinantalIdealFin_zero rankDeficient

example :
    determinantalIdealFin rankDeficient 1 =
      Ideal.span {(1 : Int)} := by
  have hk :
      1 ≤ (SmithData.ofSmithMatrix
        rankDeficient rankDeficient_isSmith).rank := by
    norm_num [SmithData.ofSmithMatrix, smithInvariantFactorsFin,
      Internal.invariantFactors, rankDeficient,
      NormalForms.Matrix.Hermite.lowerRight]
  simpa [SmithData.prefixProduct, SmithData.ofSmithMatrix,
      smithDiagonalFin, rankDeficient] using
    (determinantalIdealFin_eq_span_prefixProduct
      rankDeficient_isSmith 1 hk)

example : determinantalIdealFin rankDeficient 2 = ⊥ := by
  have hrank :
      (SmithData.ofSmithMatrix
        rankDeficient rankDeficient_isSmith).rank < 2 := by
    norm_num [SmithData.ofSmithMatrix, smithInvariantFactorsFin,
      Internal.invariantFactors, rankDeficient,
      NormalForms.Matrix.Hermite.lowerRight]
  exact
    determinantalIdealFin_eq_bot_of_rank_lt
      rankDeficient_isSmith 2 hrank

example : determinantalIdealFin rectangularWithUnit 2 =
    Ideal.span {(2 : Int)} := by
  have hk :
      2 ≤ (SmithData.ofSmithMatrix
        rectangularWithUnit rectangularWithUnit_isSmith).rank := by
    norm_num [SmithData.ofSmithMatrix, smithInvariantFactorsFin,
      Internal.invariantFactors, rectangularWithUnit,
      NormalForms.Matrix.Hermite.lowerRight]
  simpa [SmithData.prefixProduct, SmithData.ofSmithMatrix,
      smithDiagonalFin, rectangularWithUnit] using
    (determinantalIdealFin_eq_span_prefixProduct
      rectangularWithUnit_isSmith 2 hk)

example : determinantalIdealFin rectangularWithUnit 3 = ⊥ :=
  determinantalIdealFin_eq_bot_of_min_lt rectangularWithUnit
    (by norm_num [Nat.min_def])

end NormalForms.Tests.SmithData
