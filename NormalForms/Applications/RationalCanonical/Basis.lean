/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.RationalCanonical.ModuleDecomposition
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import all NormalForms.Matrix.Smith.Defs

/-!
# Cyclic Bases and Explicit Similarity

Every endomorphism invariant factor is nonzero and monic, and their degrees
sum to the ambient dimension.  These facts turn the product of quotient power
bases supplied by the cyclic module decomposition into a basis of `Rat^n`.

The resulting change-of-basis matrix carries an explicit inverse certificate.
This file proves the exact similarity equation; the companion-block
identification is layered on top in the rational-canonical-result module.
-/

namespace NormalForms.RationalCanonical

open Polynomial
open NormalForms.Matrix.Smith

public theorem endomorphismInvariantFactor_ne_zero
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat)
    (i : Fin n) :
    endomorphismInvariantFactor A i ≠ 0 := by
  intro hzero
  have hmem :
      0 ∈ endomorphismInvariantFactors A := by
    rw [endomorphismInvariantFactors_eq_diagonal]
    exact List.mem_map.mpr
      ⟨i, List.mem_finRange i, hzero⟩
  have hproduct :
      (endomorphismInvariantFactors A).prod = 0 :=
    List.prod_eq_zero_iff.mpr hmem
  rw [endomorphismInvariantFactors_product] at hproduct
  exact A.charpoly_monic.ne_zero hproduct

public theorem endomorphismInvariantFactor_normalized
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat)
    (i : Fin n) :
    normalize (endomorphismInvariantFactor A i) =
      endomorphismInvariantFactor A i := by
  let result := endomorphismSmithResult A
  have hdiag :=
    Internal.isSmithNormalFormFin_toDiag result.isSmith
  have hi : i.1 < Nat.min n n :=
    (Nat.lt_min).2 ⟨i.2, i.2⟩
  have hnormalized :
      result.S i i = normalize (result.S i i) := by
    simpa [Internal.diagEntry] using
      hdiag.2.1 i.1 hi
  rw [endomorphismSmithResult_diagonal] at hnormalized
  exact hnormalized.symm

public theorem endomorphismInvariantFactor_monic
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat)
    (i : Fin n) :
    (endomorphismInvariantFactor A i).Monic :=
  (normalize_eq_self_iff_monic
    (endomorphismInvariantFactor_ne_zero A i)).mp
      (endomorphismInvariantFactor_normalized A i)

public theorem endomorphismInvariantFactor_degree_sum
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    ∑ i : Fin n,
        (endomorphismInvariantFactor A i).natDegree =
      n := by
  have hdegree :=
    natDegree_prod Finset.univ
      (endomorphismInvariantFactor A)
      (by
        intro i _
        exact endomorphismInvariantFactor_ne_zero A i)
  have hproduct :
      (∏ i : Fin n, endomorphismInvariantFactor A i) =
        A.charpoly := by
    rw [Fin.prod_univ_def]
    rw [← endomorphismInvariantFactors_eq_diagonal]
    exact endomorphismInvariantFactors_product A
  rw [hproduct, Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin] at hdegree
  exact hdegree.symm

public abbrev CyclicIndex
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :=
  (i : Fin n) ×
    Fin (endomorphismInvariantFactor A i).natDegree

public noncomputable def cyclicIndexEquiv
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    CyclicIndex A ≃ Fin n :=
  finSigmaFinEquiv.trans
    (finCongr (endomorphismInvariantFactor_degree_sum A))

noncomputable def cyclicCoordinateEquiv
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    ((i : Fin n) →
        Rat[X] ⧸
          Ideal.span
            ({endomorphismInvariantFactor A i} :
              Set Rat[X])) ≃ₗ[Rat]
      (CyclicIndex A → Rat) := by
  let components :
      ((i : Fin n) →
          Rat[X] ⧸
            Ideal.span
              ({endomorphismInvariantFactor A i} :
                Set Rat[X])) ≃ₗ[Rat]
        ((i : Fin n) →
          Fin (endomorphismInvariantFactor A i).natDegree →
            Rat) :=
    LinearEquiv.piCongrRight fun i =>
      (AdjoinRoot.powerBasis'
        (endomorphismInvariantFactor_monic A i)).basis.equivFun
  exact components.trans
    (LinearEquiv.piCurry Rat
      (fun (i : Fin n)
        (_ : Fin
          (endomorphismInvariantFactor A i).natDegree) => Rat)).symm

noncomputable def cyclicBasisAEval
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    Module.Basis (CyclicIndex A) Rat
      (EndomorphismModule A) :=
  Module.Basis.ofEquivFun <|
    ((endomorphismCyclicDecomposition A).restrictScalars Rat).trans
      (cyclicCoordinateEquiv A)

public noncomputable def rationalCanonicalBasis
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    Module.Basis (Fin n) Rat (Fin n → Rat) :=
  ((cyclicBasisAEval A).map
    (Module.AEval'.of A.toLin').symm).reindex
      (cyclicIndexEquiv A)

public noncomputable def rationalCanonicalChange
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    Matrix (Fin n) (Fin n) Rat :=
  (Pi.basisFun Rat (Fin n)).toMatrix
    (rationalCanonicalBasis A)

public noncomputable def rationalCanonicalChangeInverse
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    Matrix (Fin n) (Fin n) Rat :=
  (rationalCanonicalBasis A).toMatrix
    (Pi.basisFun Rat (Fin n))

public theorem rationalCanonicalChangeInverse_mul
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    rationalCanonicalChangeInverse A *
      rationalCanonicalChange A =
      1 := by
  simp [rationalCanonicalChangeInverse,
    rationalCanonicalChange,
    Module.Basis.toMatrix_mul_toMatrix]

public theorem rationalCanonicalChange_mul_inverse
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    rationalCanonicalChange A *
        rationalCanonicalChangeInverse A =
      1 := by
  simp [rationalCanonicalChangeInverse,
    rationalCanonicalChange,
    Module.Basis.toMatrix_mul_toMatrix]

public noncomputable def rationalCanonicalChangeCertificate
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    NormalForms.Matrix.Certificates.MatrixInverseCertificate
      (rationalCanonicalChange A) where
  inverse := rationalCanonicalChangeInverse A
  left_inv := rationalCanonicalChangeInverse_mul A
  right_inv := rationalCanonicalChange_mul_inverse A

public noncomputable def rationalCanonicalMatrix
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    Matrix (Fin n) (Fin n) Rat :=
  LinearMap.toMatrix
    (rationalCanonicalBasis A)
    (rationalCanonicalBasis A)
    A.toLin'

public theorem rationalCanonical_similarity
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    rationalCanonicalChangeInverse A * A *
        rationalCanonicalChange A =
      rationalCanonicalMatrix A := by
  have hchange :=
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      (rationalCanonicalBasis A)
      (Pi.basisFun Rat (Fin n))
      (rationalCanonicalBasis A)
      (Pi.basisFun Rat (Fin n))
      A.toLin'
  have hstandard :
      LinearMap.toMatrix
          (Pi.basisFun Rat (Fin n))
          (Pi.basisFun Rat (Fin n))
          A.toLin' =
        A := by
    rw [← Matrix.toLin_eq_toLin']
    exact LinearMap.toMatrix_toLin _ _ A
  calc
    rationalCanonicalChangeInverse A * A *
          rationalCanonicalChange A =
        rationalCanonicalChangeInverse A *
          (LinearMap.toMatrix
            (Pi.basisFun Rat (Fin n))
            (Pi.basisFun Rat (Fin n))
            A.toLin') *
          rationalCanonicalChange A := by
      rw [hstandard]
    _ = rationalCanonicalMatrix A := by
      simpa only [rationalCanonicalChangeInverse,
        rationalCanonicalChange, rationalCanonicalMatrix] using
          hchange

end NormalForms.RationalCanonical
