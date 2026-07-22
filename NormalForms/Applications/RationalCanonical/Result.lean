/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.RationalCanonical.Basis
public import NormalForms.Applications.RationalCanonical.Companion
import all NormalForms.Applications.RationalCanonical.Basis

/-!
# Rational Canonical Results

The cyclic Smith decomposition supplies a basis indexed by the powers below
each invariant factor.  In that basis, multiplication by `X` is the dependent
block diagonal of the corresponding companion matrices.

`RationalCanonicalResult` exposes only the change of basis, its explicit
two-sided inverse certificate, and the exact similarity equation.  The
canonical matrix is derived from `A`, so stored fields cannot disagree with
the executable invariant factors.
-/

namespace NormalForms.RationalCanonical

open Polynomial

private noncomputable def rationalCanonicalCyclicBasis
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    Module.Basis (CyclicIndex A) Rat (Fin n → Rat) :=
  (cyclicBasisAEval A).map
    (Module.AEval'.of A.toLin').symm

private noncomputable def aEvalXAction
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    EndomorphismModule A →ₗ[Rat] EndomorphismModule A where
  toFun x := (X : Rat[X]) • x
  map_add' x y := by simp
  map_smul' r x :=
    smul_comm (X : Rat[X]) r x

private theorem rationalCanonicalCyclicBasis_toMatrix
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    LinearMap.toMatrix
        (rationalCanonicalCyclicBasis A)
        (rationalCanonicalCyclicBasis A)
        A.toLin' =
      LinearMap.toMatrix
        (cyclicBasisAEval A)
        (cyclicBasisAEval A)
        (aEvalXAction A) := by
  ext i j
  simp only [rationalCanonicalCyclicBasis,
    LinearMap.toMatrix_apply, aEvalXAction,
    Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, Matrix.toLin'_apply]
  congr 2
  rw [Module.Basis.map_apply]
  change
    Module.AEval'.of A.toLin'
        (A.toLin'
          ((Module.AEval'.of A.toLin').symm
            ((cyclicBasisAEval A) j))) =
      (X : Rat[X]) • (cyclicBasisAEval A) j
  rw [← Module.AEval'.X_smul_of]
  simp

private theorem rationalCanonicalMatrix_eq_reindex_cyclic
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    rationalCanonicalMatrix A =
      Matrix.reindex (cyclicIndexEquiv A)
        (cyclicIndexEquiv A)
        (LinearMap.toMatrix
          (rationalCanonicalCyclicBasis A)
          (rationalCanonicalCyclicBasis A)
          A.toLin') := by
  ext i j
  simp [rationalCanonicalMatrix, rationalCanonicalBasis,
    rationalCanonicalCyclicBasis, LinearMap.toMatrix_apply,
    Matrix.reindex_apply]

private abbrev CyclicProduct
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :=
  (i : Fin n) →
    AdjoinRoot (endomorphismInvariantFactor A i)

private noncomputable def cyclicComponentBasis
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat)
    (i : Fin n) :
    Module.Basis
      (Fin (endomorphismInvariantFactor A i).natDegree)
      Rat
      (AdjoinRoot (endomorphismInvariantFactor A i)) :=
  (AdjoinRoot.powerBasis'
    (endomorphismInvariantFactor_monic A i)).basis

private noncomputable def cyclicProductBasis
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    Module.Basis (CyclicIndex A) Rat (CyclicProduct A) :=
  Pi.basis (cyclicComponentBasis A)

private theorem cyclicBasisAEval_eq_map
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    cyclicBasisAEval A =
      (cyclicProductBasis A).map
        ((endomorphismCyclicDecomposition A).restrictScalars Rat).symm := by
  rw [← Module.Basis.ofEquivFun_equivFun (cyclicBasisAEval A)]
  rw [← Module.Basis.ofEquivFun_equivFun
    ((cyclicProductBasis A).map
      ((endomorphismCyclicDecomposition A).restrictScalars Rat).symm)]
  congr 1

private noncomputable def cyclicProductXAction
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    CyclicProduct A →ₗ[Rat] CyclicProduct A where
  toFun v i :=
    (Algebra.lmul Rat
      (AdjoinRoot (endomorphismInvariantFactor A i))
      (AdjoinRoot.root (endomorphismInvariantFactor A i))) (v i)
  map_add' x y := by
    ext i
    exact map_add _ _ _
  map_smul' r x := by
    ext i
    exact
      (Algebra.lmul Rat
        (AdjoinRoot (endomorphismInvariantFactor A i))
        (AdjoinRoot.root
          (endomorphismInvariantFactor A i))).map_smul r (x i)

private theorem cyclicBasisAEval_toMatrix
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    LinearMap.toMatrix
        (cyclicBasisAEval A)
        (cyclicBasisAEval A)
        (aEvalXAction A) =
      LinearMap.toMatrix
        (cyclicProductBasis A)
        (cyclicProductBasis A)
        (cyclicProductXAction A) := by
  rw [cyclicBasisAEval_eq_map]
  ext i j
  simp only [LinearMap.toMatrix_apply,
    Module.Basis.map_repr, Module.Basis.map_apply,
    cyclicProductXAction, aEvalXAction]
  change
    ((cyclicProductBasis A).repr
      ((endomorphismCyclicDecomposition A)
        ((X : Rat[X]) •
          (endomorphismCyclicDecomposition A).symm
            ((cyclicProductBasis A) j)))) i =
      ((cyclicProductBasis A).repr
        (fun k =>
          (Algebra.lmul Rat
            (AdjoinRoot (endomorphismInvariantFactor A k))
            (AdjoinRoot.root
              (endomorphismInvariantFactor A k)))
            ((cyclicProductBasis A) j k))) i
  rw [(endomorphismCyclicDecomposition A).map_smul,
    (endomorphismCyclicDecomposition A).apply_symm_apply]
  congr 2

private theorem cyclicProductXAction_toMatrix
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    LinearMap.toMatrix
        (cyclicProductBasis A)
        (cyclicProductBasis A)
        (cyclicProductXAction A) =
      Matrix.blockDiagonal' fun i =>
        companionMatrix (endomorphismInvariantFactor A i) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [LinearMap.toMatrix_apply]
  simp only [cyclicProductBasis, Pi.basis_repr,
    Pi.basis_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.blockDiagonal'_apply_eq]
    have haction :
        cyclicProductXAction A
            (Pi.single i
              (cyclicComponentBasis A i l)) i =
          (Algebra.lmul Rat
            (AdjoinRoot (endomorphismInvariantFactor A i))
            (AdjoinRoot.root
              (endomorphismInvariantFactor A i)))
            (cyclicComponentBasis A i l) := by
      change
        AdjoinRoot.root
              (endomorphismInvariantFactor A i) *
            ((Pi.single i
              (cyclicComponentBasis A i l) :
                CyclicProduct A) i) =
          AdjoinRoot.root
              (endomorphismInvariantFactor A i) *
            (cyclicComponentBasis A i l)
      rw [Pi.single_eq_same]
    rw [haction]
    rw [companionMatrix_eq_toMatrix
      (endomorphismInvariantFactor A i)
      (endomorphismInvariantFactor_monic A i)]
    rw [LinearMap.toMatrix_apply]
    rfl
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hij]
    change
      (cyclicComponentBasis A i).repr
          (cyclicProductXAction A
            (Pi.single j
              (cyclicComponentBasis A j l)) i) k =
        0
    change
      (cyclicComponentBasis A i).repr
          ((Algebra.lmul Rat
            (AdjoinRoot (endomorphismInvariantFactor A i))
            (AdjoinRoot.root
              (endomorphismInvariantFactor A i)))
            ((Pi.single j
              (cyclicComponentBasis A j l) :
                CyclicProduct A) i)) k =
        0
    simp [hij]

private structure FactorBlockData (n : Nat) where
  factor : Fin n → Rat[X]
  degree_sum :
    ∑ i : Fin n, (factor i).natDegree = n

private theorem FactorBlockData.ext
    {n : Nat}
    {source target : FactorBlockData n}
    (factor : source.factor = target.factor) :
    source = target := by
  cases source
  cases target
  cases factor
  rfl

private abbrev FactorBlockData.Index
    {n : Nat}
    (data : FactorBlockData n) :=
  (i : Fin n) × Fin (data.factor i).natDegree

private noncomputable def FactorBlockData.indexEquiv
    {n : Nat}
    (data : FactorBlockData n) :
    data.Index ≃ Fin n :=
  finSigmaFinEquiv.trans
    (finCongr data.degree_sum)

private noncomputable def FactorBlockData.blockMatrix
    {n : Nat}
    (data : FactorBlockData n) :
    Matrix (Fin n) (Fin n) Rat :=
  Matrix.reindex
    data.indexEquiv
    data.indexEquiv
    (Matrix.blockDiagonal' fun i =>
      companionMatrix (data.factor i))

private noncomputable def endomorphismFactorBlockData
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    FactorBlockData n where
  factor := endomorphismInvariantFactor A
  degree_sum := endomorphismInvariantFactor_degree_sum A

public noncomputable def rationalCanonicalBlockMatrix
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    Matrix (Fin n) (Fin n) Rat :=
  (endomorphismFactorBlockData A).blockMatrix

public theorem rationalCanonicalBlockMatrix_eq_of_factor_eq
    {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Rat}
    (factors :
      endomorphismInvariantFactor A =
        endomorphismInvariantFactor B) :
    rationalCanonicalBlockMatrix A =
      rationalCanonicalBlockMatrix B := by
  apply congrArg FactorBlockData.blockMatrix
  apply FactorBlockData.ext
  exact factors

public theorem rationalCanonicalMatrix_eq_blocks
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    rationalCanonicalMatrix A =
      rationalCanonicalBlockMatrix A := by
  rw [rationalCanonicalMatrix_eq_reindex_cyclic]
  rw [rationalCanonicalCyclicBasis_toMatrix]
  rw [cyclicBasisAEval_toMatrix]
  rw [cyclicProductXAction_toMatrix]
  rfl

public structure RationalCanonicalResult
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) where
  change : Matrix (Fin n) (Fin n) Rat
  changeCertificate :
    NormalForms.Matrix.Certificates.MatrixInverseCertificate
      change
  equation :
    changeCertificate.inverse * A * change =
      rationalCanonicalBlockMatrix A

public noncomputable def rationalCanonicalResult
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    RationalCanonicalResult A where
  change := rationalCanonicalChange A
  changeCertificate := rationalCanonicalChangeCertificate A
  equation := by
    simpa [rationalCanonicalChangeCertificate] using
      (rationalCanonical_similarity A).trans
        (rationalCanonicalMatrix_eq_blocks A)

end NormalForms.RationalCanonical
