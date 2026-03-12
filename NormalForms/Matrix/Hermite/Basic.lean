import NormalForms.Matrix.Hermite.Algorithm

/-!
# Hermite Normal Form API

Public Hermite result packaging and the executable wrapper over arbitrary finite index types.
-/

namespace NormalForms.Matrix.Hermite

open scoped Matrix
open NormalForms.Matrix.Certificates

structure HNFResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  H : _root_.Matrix m n R
  left_mul : U * A = H
  isHermite : IsHermiteNormalForm H


def HNFResult.toCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : HNFResult A) :
    LeftCertificate A :=
  { U := result.U
    result := result.H
    equation := result.left_mul }


noncomputable def hermiteNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) : Option (HNFResult A) :=
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let Afin : _root_.Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) R :=
    _root_.Matrix.reindex em en A
  let result := Internal.hermiteNormalFormFin Afin
  some
    { U := _root_.Matrix.reindex em.symm em.symm result.U
      H := _root_.Matrix.reindex em.symm en.symm result.H
      left_mul := by
        simpa [Matrix.reindexLinearEquiv, Afin] using
          (Matrix.reindexLinearEquiv_mul R R em.symm em.symm en.symm result.U Afin).trans
            (by simpa [Matrix.reindexLinearEquiv, Afin] using congrArg (_root_.Matrix.reindex em.symm en.symm) result.left_mul)
      isHermite := by
        unfold IsHermiteNormalForm
        convert result.isHermite using 1
        ext i j
        simp [em, en] }


theorem hermiteNormalForm_exists {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) : ∃ result, hermiteNormalForm A = some result := by
  unfold hermiteNormalForm
  simp


theorem hermiteNormalForm_unimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {A : _root_.Matrix m n R} {result : HNFResult A}
    (hresult : hermiteNormalForm A = some result) :
    Unimodular result.U := by
  unfold hermiteNormalForm at hresult
  dsimp at hresult
  injection hresult with hEq
  subst hEq
  exact unimodular_reindex (Fintype.equivFin m).symm
    (Internal.hermiteNormalFormFin
      (_root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) A)).unimodular

end NormalForms.Matrix.Hermite
