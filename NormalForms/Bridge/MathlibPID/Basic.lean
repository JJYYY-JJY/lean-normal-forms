import NormalForms.Matrix.Smith
import Mathlib.Data.List.Sort

/-!
# PID Bridge Shapes

Bridge-side helpers for comparing executable Smith data with PID-style
`Basis.SmithNormalForm` readouts.
-/

namespace NormalForms.Bridge.MathlibPID

abbrev pidSmithColumnSpan {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    (A : _root_.Matrix m n R) : Submodule R (m -> R) :=
  NormalForms.Matrix.Smith.smithColumnSpan A

@[simp] theorem pidSmithColumnSpan_eq_range_mulVecLin {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    (A : _root_.Matrix m n R) :
    pidSmithColumnSpan A = LinearMap.range A.mulVecLin := by
  unfold pidSmithColumnSpan NormalForms.Matrix.Smith.smithColumnSpan
  rfl

noncomputable def pidUnimodularMulVecEquiv {m R : Type _}
    [Fintype m] [DecidableEq m] [EuclideanDomain R]
    (U : _root_.Matrix m m R) (hU : NormalForms.Matrix.Certificates.Unimodular U) :
    (m -> R) ≃ₗ[R] (m -> R) := by
  letI := _root_.Matrix.invertibleOfIsUnitDet U hU
  exact U.toLinearEquiv' inferInstance

@[simp] theorem pidSmithColumnSpan_mul_right_unimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    {A : _root_.Matrix m n R} {V : _root_.Matrix n n R}
    (hV : NormalForms.Matrix.Certificates.Unimodular V) :
    pidSmithColumnSpan (A * V) = pidSmithColumnSpan A := by
  unfold pidSmithColumnSpan NormalForms.Matrix.Smith.smithColumnSpan
  rw [_root_.Matrix.mulVecLin_mul]
  have hsurj : Function.Surjective V.mulVecLin := by
    intro v
    refine ⟨V⁻¹.mulVecLin v, ?_⟩
    simp [_root_.Matrix.mul_nonsing_inv V hV]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)]

@[simp] theorem pidSmithColumnSpan_mul_left_unimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    {A : _root_.Matrix m n R} {U : _root_.Matrix m m R}
    (_hU : NormalForms.Matrix.Certificates.Unimodular U) :
    pidSmithColumnSpan (U * A) = Submodule.map U.mulVecLin (pidSmithColumnSpan A) := by
  unfold pidSmithColumnSpan NormalForms.Matrix.Smith.smithColumnSpan
  rw [_root_.Matrix.mulVecLin_mul, LinearMap.range_comp]

noncomputable def pidExecutableInvariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (S : _root_.Matrix m n R) : List R :=
  NormalForms.Matrix.Smith.smithInvariantFactors S

noncomputable def pidSmithNormalFormData {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) :
    Σ k : ℕ, Module.Basis.SmithNormalForm (pidSmithColumnSpan A) m k :=
  Submodule.smithNormalForm (Pi.basisFun R m) (pidSmithColumnSpan A)

noncomputable def pidSmithNormalFormOfLEData {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) :
    Σ o k : ℕ,
      Module.Basis.SmithNormalForm
        ((pidSmithColumnSpan A).comap (⊤ : Submodule R (m -> R)).subtype) (Fin o) k :=
  (pidSmithColumnSpan A).smithNormalFormOfLE (Pi.basisFun R m) ⊤ le_top

noncomputable def pidSmithNormalFormCoeffs {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) :
    Fin (pidSmithNormalFormData A).1 -> R :=
  (pidSmithNormalFormData A).2.a

noncomputable def pidSmithNormalFormCoeffList {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) : List R :=
  (Classical.choose (NormalForms.Matrix.Smith.smithNormalForm_exists A)).invariantFactors

@[simp] theorem pidSmithNormalFormCoeffList_eq_resultInvariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    {A : _root_.Matrix m n R} {result : NormalForms.Matrix.Smith.SNFResult A}
    (hresult : NormalForms.Matrix.Smith.smithNormalForm A = some result) :
    pidSmithNormalFormCoeffList A = result.invariantFactors := by
  let chosen := Classical.choose (NormalForms.Matrix.Smith.smithNormalForm_exists A)
  have hchosen : NormalForms.Matrix.Smith.smithNormalForm A = some chosen :=
    Classical.choose_spec (NormalForms.Matrix.Smith.smithNormalForm_exists A)
  have hEq : chosen = result := by
    rw [hresult] at hchosen
    injection hchosen with hEq'
    exact hEq'.symm
  unfold pidSmithNormalFormCoeffList
  simpa using congrArg NormalForms.Matrix.Smith.SNFResult.invariantFactors hEq

@[simp] theorem pidSmithNormalFormCoeffList_eq_of_isSmith {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    {S : _root_.Matrix m n R}
    (hS : NormalForms.Matrix.Smith.IsSmithNormalForm S) :
    pidSmithNormalFormCoeffList S = NormalForms.Matrix.Smith.smithInvariantFactors S := by
  let result := Classical.choose (NormalForms.Matrix.Smith.smithNormalForm_exists S)
  have hresult : NormalForms.Matrix.Smith.smithNormalForm S = some result :=
    Classical.choose_spec (NormalForms.Matrix.Smith.smithNormalForm_exists S)
  have hEq : S = result.S := by
    exact NormalForms.Matrix.Smith.isSmithNormalForm_unique_of_two_sided_equiv
      hS
      (NormalForms.Matrix.Smith.smithNormalForm_isSmith hresult)
      (NormalForms.Matrix.Smith.smithNormalForm_leftUnimodular hresult)
      (NormalForms.Matrix.Smith.smithNormalForm_rightUnimodular hresult)
      result.two_sided_mul
  simpa [pidSmithNormalFormCoeffList, NormalForms.Matrix.Smith.SNFResult.invariantFactors] using
    congrArg NormalForms.Matrix.Smith.smithInvariantFactors hEq.symm

noncomputable def pidFullRankSmithNormalFormCoeffs {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R)
    (hfull : Module.finrank R (pidSmithColumnSpan A) = Fintype.card m) :
    m -> R :=
  let b := Pi.basisFun R m
  let hfull' : Module.finrank R (pidSmithColumnSpan A) = Module.finrank R (m -> R) := by
    simpa [Module.finrank_eq_card_basis b] using hfull
  Submodule.smithNormalFormCoeffs b hfull'

/-- Mathlib-side normalized coeff list for full-rank `Int` submodules.

This reads the chosen `mathlib` Smith witness coefficients via
`pidFullRankSmithNormalFormCoeffs`, applies `Int.natAbs`, and sorts the resulting
list in ascending order. Unlike `pidSmithNormalFormCoeffList`, this is a
mathlib-side readout rather than an executable-SNF readout.
-/
noncomputable def pidFullRankMathlibSmithCoeffNatAbsList {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : _root_.Matrix m n Int)
    (hfull : Module.finrank Int (pidSmithColumnSpan A) = Fintype.card m) : List Nat :=
  (((Finset.univ : Finset m).toList.map fun i =>
      Int.natAbs (pidFullRankSmithNormalFormCoeffs A hfull i))).insertionSort (· ≤ ·)

@[simp] theorem pidFullRankMathlibSmithCoeffNatAbsList_length {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : _root_.Matrix m n Int)
    (hfull : Module.finrank Int (pidSmithColumnSpan A) = Fintype.card m) :
    (pidFullRankMathlibSmithCoeffNatAbsList A hfull).length = Fintype.card m := by
  unfold pidFullRankMathlibSmithCoeffNatAbsList
  rw [List.length_insertionSort]
  simp

end NormalForms.Bridge.MathlibPID
