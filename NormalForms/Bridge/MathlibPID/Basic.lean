/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Matrix.Smith
public import NormalForms.Euclidean.Int

/-!
# PID Bridge Shapes

Bridge-side helpers for comparing executable Smith data with PID-style
`Basis.SmithNormalForm` readouts, including normalized full-rank `Int`
coefficient lists on both the executable and mathlib sides.
-/

@[expose] public section

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
    (U : _root_.Matrix m m R)
    (U_cert : NormalForms.Matrix.Certificates.MatrixInverseCertificate U) :
    (m -> R) ≃ₗ[R] (m -> R) := by
  letI : Invertible U :=
    { invOf := U_cert.inverse
      invOf_mul_self := U_cert.left_inv
      mul_invOf_self := U_cert.right_inv }
  exact U.toLinearEquiv' inferInstance

@[simp] theorem pidSmithColumnSpan_mul_right_unimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    {A : _root_.Matrix m n R} {V : _root_.Matrix n n R}
    (V_cert : NormalForms.Matrix.Certificates.MatrixInverseCertificate V) :
    pidSmithColumnSpan (A * V) = pidSmithColumnSpan A := by
  unfold pidSmithColumnSpan NormalForms.Matrix.Smith.smithColumnSpan
  rw [_root_.Matrix.mulVecLin_mul]
  have hsurj : Function.Surjective V.mulVecLin := by
    intro v
    refine ⟨V_cert.inverse.mulVecLin v, ?_⟩
    simp [V_cert.right_inv]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)]

@[simp] theorem pidSmithColumnSpan_mul_left_unimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    {A : _root_.Matrix m n R} {U : _root_.Matrix m m R}
    (_U_cert : NormalForms.Matrix.Certificates.MatrixInverseCertificate U) :
    pidSmithColumnSpan (U * A) = Submodule.map U.mulVecLin (pidSmithColumnSpan A) := by
  unfold pidSmithColumnSpan NormalForms.Matrix.Smith.smithColumnSpan
  rw [_root_.Matrix.mulVecLin_mul, LinearMap.range_comp]

noncomputable def pidExecutableInvariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (indexing : NormalForms.Matrix.MatrixIndexing m n)
    (S : _root_.Matrix m n R) : List R :=
  NormalForms.Matrix.Smith.smithInvariantFactorsWith indexing S

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
    [EuclideanDomain R] [NormalizationMonoid R]
    [NormalForms.ComputableEuclideanOps R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) : List R :=
  (NormalForms.Matrix.Smith.smithNormalForm A).invariantFactors

noncomputable def pidExecutableInvariantFactorCount {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R]
    [NormalForms.ComputableEuclideanOps R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) : Nat :=
  (pidSmithNormalFormCoeffList A).length

noncomputable def pidExecutableInvariantFactorFn {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R]
    [NormalForms.ComputableEuclideanOps R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    Fin (pidExecutableInvariantFactorCount A) → R :=
  fun i => (pidSmithNormalFormCoeffList A).get i

@[simp] theorem pidSmithNormalFormCoeffList_eq_resultInvariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R]
    [NormalForms.ComputableEuclideanOps R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    pidSmithNormalFormCoeffList A =
      (NormalForms.Matrix.Smith.smithNormalForm A).invariantFactors := by
  rfl

@[simp] theorem pidExecutableInvariantFactorCount_eq_length {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R]
    [NormalForms.ComputableEuclideanOps R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    pidExecutableInvariantFactorCount A = (pidSmithNormalFormCoeffList A).length :=
  rfl

@[simp] theorem pidSmithNormalFormCoeffList_eq_of_isSmith {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R]
    [NormalForms.ComputableEuclideanOps R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    {S : _root_.Matrix m n R}
    (hS : NormalForms.Matrix.Smith.IsSmithNormalFormWith
      (NormalForms.Matrix.Smith.smithNormalForm S).indexing S) :
    pidSmithNormalFormCoeffList S =
      NormalForms.Matrix.Smith.smithInvariantFactorsWith
        (NormalForms.Matrix.Smith.smithNormalForm S).indexing S := by
  let result := NormalForms.Matrix.Smith.smithNormalForm S
  have hEq : S = result.S := by
    exact NormalForms.Matrix.Smith.isSmithNormalFormWith_unique_of_two_sided_equiv
      result.indexing
      hS
      result.isSmith
      result.U_cert.unimodular
      result.V_cert.unimodular
      result.equation
  calc
    pidSmithNormalFormCoeffList S = result.invariantFactors := by rfl
    _ = NormalForms.Matrix.Smith.smithInvariantFactorsWith result.indexing result.S :=
      result.invariantFactorsWith_S.symm
    _ = NormalForms.Matrix.Smith.smithInvariantFactorsWith result.indexing S :=
      (congrArg (NormalForms.Matrix.Smith.smithInvariantFactorsWith result.indexing) hEq).symm

/-- Executable-side normalized coefficient list for `Int` matrices.

This reads the chosen executable Smith result via `pidSmithNormalFormCoeffList`,
applies `Int.natAbs`, and sorts the resulting list in ascending order.
-/
noncomputable def pidExecutableSmithCoeffNatAbsList {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int) : List Nat :=
  ((pidSmithNormalFormCoeffList A).map Int.natAbs).insertionSort (· ≤ ·)

@[simp] theorem pidExecutableSmithCoeffNatAbsList_length {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int) :
    (pidExecutableSmithCoeffNatAbsList A).length = (pidSmithNormalFormCoeffList A).length := by
  unfold pidExecutableSmithCoeffNatAbsList
  rw [List.length_insertionSort, List.length_map]

theorem pidExecutableSmithCoeffNatAbsList_eq_resultInvariantFactors {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int) :
    pidExecutableSmithCoeffNatAbsList A =
      ((NormalForms.Matrix.Smith.smithNormalForm A).invariantFactors.map Int.natAbs).insertionSort
        (· ≤ ·) := by
  rfl

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
