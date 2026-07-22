/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Bridge.MathlibPID.Signature
import all NormalForms.Matrix.Smith.Algorithm
import all NormalForms.Matrix.Smith.Uniqueness

set_option linter.privateModule false

/-!
# PID Signature Bridge Regressions

Concrete identity and rectangular-zero witnesses exercise the associate,
normalized, and integer readouts.  The zero case also checks that the bridge
does not confuse presentation column count with Smith rank.
-/

namespace NormalForms.Tests.PIDSignature

open scoped Matrix
open NormalForms.Matrix.Smith
open NormalForms.Bridge.MathlibPID

private def identityMatrix :
    _root_.Matrix (Fin 2) (Fin 2) Int :=
  1

private theorem identityColumnSpan :
    pidSmithColumnSpan identityMatrix = ⊤ := by
  rw [pidSmithColumnSpan_eq_range_mulVecLin]
  apply LinearMap.range_eq_top.mpr
  intro x
  exact ⟨x, by simp [identityMatrix]⟩

private noncomputable def identityWitness :
    Module.Basis.SmithNormalForm
      (pidSmithColumnSpan identityMatrix) (Fin 2) 2 := by
  let ambient := Pi.basisFun Int (Fin 2)
  let submoduleBasis :
      Module.Basis (Fin 2) Int
        (pidSmithColumnSpan identityMatrix) :=
    ambient.map (LinearEquiv.ofTop _ identityColumnSpan).symm
  exact
    { bM := ambient
      bN := submoduleBasis
      f := ⟨id, Function.injective_id⟩
      a := fun _ => 1
      snf := by
        intro i
        simp [ambient, submoduleBasis] }

@[simp] private theorem identityWitness_a (i : Fin 2) :
    identityWitness.a i = 1 := by
  unfold identityWitness
  simp

private theorem identityDiagonal :
    pidSmithBasisDiagonalMatrix identityWitness = identityMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pidSmithBasisDiagonalMatrix, identityMatrix]

private theorem identityIsSmith :
    IsSmithNormalFormFin
      (pidSmithBasisDiagonalMatrix identityWitness) := by
  rw [identityDiagonal]
  apply NormalForms.Matrix.Smith.Internal.isSmithNormalFormDiag_toFin
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [identityMatrix] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      simp [Internal.diagEntry, identityMatrix]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [Internal.diagEntry, identityMatrix]

private noncomputable def identityCanonicalBasis :
    CanonicalPIDSmithBasis identityMatrix where
  count := 2
  witness := identityWitness
  canonical := identityIsSmith

private noncomputable def identityResult :
    SNFResultFin identityMatrix :=
  smithNormalFormFin identityMatrix

example :
    identityCanonicalBasis.associateFactors =
      Multiset.ofList
        [Associates.mk (1 : Int), Associates.mk (1 : Int)] := by
  simp [CanonicalPIDSmithBasis.associateFactors,
    identityCanonicalBasis]

example :
    identityCanonicalBasis.normalizedFactors =
      Multiset.ofList [(1 : Int), 1] := by
  simp [CanonicalPIDSmithBasis.normalizedFactors,
    identityCanonicalBasis]

example :
    identityCanonicalBasis.intCoeffNatAbsList = [1, 1] := by
  change ([1, 1] : Multiset Nat).sort (· ≤ ·) = [1, 1]
  exact List.mergeSort_eq_self _ (by simp)

example :
    identityResult.smithSignature =
      identityCanonicalBasis.signature :=
  identityCanonicalBasis.smithSignature_eq identityResult

example :
    pidNormalizedFactors identityResult.smithSignature =
      identityCanonicalBasis.normalizedFactors :=
  identityCanonicalBasis.normalizedFactors_eq identityResult

example :
    pidIntNatAbsList identityResult.smithSignature =
      identityCanonicalBasis.intCoeffNatAbsList :=
  identityCanonicalBasis.intNatAbsList_eq identityResult

private def zeroMatrix :
    _root_.Matrix (Fin 2) (Fin 3) Int :=
  0

private theorem zeroColumnSpan :
    pidSmithColumnSpan zeroMatrix = ⊥ := by
  rw [pidSmithColumnSpan_eq_range_mulVecLin]
  simp [zeroMatrix]

private noncomputable def zeroWitness :
    Module.Basis.SmithNormalForm
      (pidSmithColumnSpan zeroMatrix) (Fin 2) 0 := by
  rw [zeroColumnSpan]
  exact
    { bM := Pi.basisFun Int (Fin 2)
      bN := Module.Basis.empty _
      f := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
      a := Fin.elim0
      snf := fun i => Fin.elim0 i }

private theorem zeroIsSmith :
    IsSmithNormalFormFin
      (pidSmithBasisDiagonalMatrix zeroWitness) :=
  .emptyCols _

private noncomputable def zeroCanonicalBasis :
    CanonicalPIDSmithBasis zeroMatrix where
  count := 0
  witness := zeroWitness
  canonical := zeroIsSmith

private noncomputable def zeroResult :
    SNFResultFin zeroMatrix :=
  smithNormalFormFin zeroMatrix

example : zeroCanonicalBasis.signature.rows = 2 := rfl
example : zeroCanonicalBasis.signature.cols = 3 := rfl
example : zeroCanonicalBasis.signature.rank = 0 := rfl
example : zeroCanonicalBasis.signature.factors = 0 := rfl

example :
    zeroResult.smithSignature = zeroCanonicalBasis.signature :=
  zeroCanonicalBasis.smithSignature_eq zeroResult

end NormalForms.Tests.PIDSignature
