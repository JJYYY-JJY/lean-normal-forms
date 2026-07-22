/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Presentation
import all NormalForms.Applications.AbelianGroups.Basic
import all NormalForms.Matrix.Smith.Algorithm
import all NormalForms.Matrix.Smith.Uniqueness

set_option linter.privateModule false

/-!
# Finite-free presentation regressions

These checks fix the column relation convention, exercise zero and rectangular
matrices, retain a unit Smith factor in theorem-facing data, filter it only in
the display reader, and instantiate both mathlib bridge outputs.
-/

namespace NormalForms.Tests.Presentation

open scoped Matrix
open NormalForms
open NormalForms.Matrix.Smith

private def directionMatrix :
    _root_.Matrix (Fin 2) (Fin 1) Int :=
  !![2; 3]

private def directionPresentation :
    FiniteFreePresentation Int where
  numGenerators := 2
  numRelations := 1
  relationMatrix := directionMatrix

example : directionPresentation.numGenerators = 2 := rfl
example : directionPresentation.numRelations = 1 := rfl

example :
    directionPresentation.relationMap ![4] = ![8, 12] := by
  decide

example :
    directionPresentation.mathlibRelations.relation
      (0 : Fin 1) (0 : Fin 2) = 2 := by
  rfl

example :
    directionPresentation.mathlibRelations.relation
      (0 : Fin 1) (1 : Fin 2) = 3 := by
  rfl

example :
    Nonempty
      (directionPresentation.mathlibRelations.Quotient ≃ₗ[Int]
        directionPresentation.presentedModule) :=
  ⟨directionPresentation.mathlibQuotientEquivPresentedModule⟩

noncomputable example :
    Module.Presentation Int directionPresentation.presentedModule :=
  directionPresentation.mathlibPresentation

private def noRelations :
    FiniteFreePresentation Int where
  numGenerators := 2
  numRelations := 0
  relationMatrix := 0

example : noRelations.relationSubmodule = ⊥ := by
  change LinearMap.range
      ((0 : _root_.Matrix (Fin 2) (Fin 0) Int).mulVecLin) = ⊥
  simp

example :
    determinantalIdealFin noRelations.relationMatrix 0 = ⊤ :=
  determinantalIdealFin_zero noRelations.relationMatrix

example :
    determinantalIdealFin noRelations.relationMatrix 1 = ⊥ :=
  determinantalIdealFin_eq_bot_of_min_lt noRelations.relationMatrix
    (by norm_num [noRelations])

example : noRelations.fittingIdeal 0 = ⊥ :=
  noRelations.fittingIdeal_eq_bot_of_min_lt 0
    (by norm_num [noRelations])

example : noRelations.fittingIdeal 2 = ⊤ :=
  noRelations.fittingIdeal_numGenerators

private def zeroMatrix :
    _root_.Matrix (Fin 2) (Fin 3) Int :=
  0

private def zeroPresentation :
    FiniteFreePresentation Int where
  numGenerators := 2
  numRelations := 3
  relationMatrix := zeroMatrix

example :
    zeroPresentation.relationMap ![3, 4, 5] = ![0, 0] := by
  decide

private theorem zeroMatrix_isSmith :
    IsSmithNormalFormFin zeroMatrix := by
  apply NormalForms.Matrix.Smith.Internal.isSmithNormalFormDiag_toFin
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simp [zeroMatrix]
  · intro k hk
    simp [NormalForms.Matrix.Smith.Internal.diagEntry, zeroMatrix]
  · intro k hk
    simp [NormalForms.Matrix.Smith.Internal.diagEntry, zeroMatrix]

example :
    (smithNormalFormFin zeroMatrix).S = zeroMatrix := by
  let result := smithNormalFormFin zeroMatrix
  exact
    (NormalForms.Matrix.Smith.Internal.isSmithNormalFormFin_unique_of_two_sided_equiv
      zeroMatrix_isSmith result.isSmith
      result.U_cert.unimodular result.V_cert.unimodular
      result.equation).symm

private def rankDeficientMatrix :
    _root_.Matrix (Fin 2) (Fin 3) Int :=
  !![2, 0, 0;
     0, 0, 0]

private def rankDeficient :
    FiniteFreePresentation Int where
  numGenerators := 2
  numRelations := 3
  relationMatrix := rankDeficientMatrix

example :
    rankDeficient.relationMap ![3, 4, 5] = ![6, 0] := by
  decide

private def unitMatrix :
    _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 2]

private def withUnit :
    FiniteFreePresentation Int where
  numGenerators := 2
  numRelations := 2
  relationMatrix := unitMatrix

private theorem unitMatrix_isSmith :
    IsSmithNormalFormFin unitMatrix := by
  apply NormalForms.Matrix.Smith.Internal.isSmithNormalFormDiag_toFin
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [unitMatrix] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      simp [NormalForms.Matrix.Smith.Internal.diagEntry, unitMatrix,
        Int.normalize_of_nonneg]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, unitMatrix]

example :
    withUnit.fittingIdeal 0 = Ideal.span {(2 : Int)} := by
  change determinantalIdealFin unitMatrix 2 = Ideal.span {(2 : Int)}
  have hk :
      2 ≤ (SmithData.ofSmithMatrix unitMatrix unitMatrix_isSmith).rank := by
    norm_num [SmithData.ofSmithMatrix, smithInvariantFactorsFin,
      NormalForms.Matrix.Smith.Internal.invariantFactors, unitMatrix,
      NormalForms.Matrix.Hermite.lowerRight]
  simpa [SmithData.prefixProduct, SmithData.ofSmithMatrix,
      smithDiagonalFin, unitMatrix] using
    (determinantalIdealFin_eq_span_prefixProduct
      unitMatrix_isSmith 2 hk)

example :
    (smithNormalFormFin unitMatrix).S = unitMatrix := by
  let result := smithNormalFormFin unitMatrix
  exact
    (NormalForms.Matrix.Smith.Internal.isSmithNormalFormFin_unique_of_two_sided_equiv
      unitMatrix_isSmith result.isSmith
      result.U_cert.unimodular result.V_cert.unimodular
      result.equation).symm

example :
    FiniteFreePresentation.displayFactors [(1 : Int), 2] = [2] := by
  norm_num [FiniteFreePresentation.displayFactors,
    Int.isUnit_iff_abs_eq]

noncomputable example :
    Nonempty
      (withUnit.presentedModule ≃ₗ[Int]
        (((i : Fin withUnit.smithRank) →
            Int ⧸ Ideal.span ({withUnit.invariantFactor i} : Set Int)) ×
          (Fin withUnit.freeRank → Int))) :=
  ⟨withUnit.smithDecomposition⟩

private def intPresentation :=
  NormalForms.Applications.AbelianGroups.presentationOfMatrix unitMatrix

example : intPresentation.relationMatrix = unitMatrix := rfl

end NormalForms.Tests.Presentation
