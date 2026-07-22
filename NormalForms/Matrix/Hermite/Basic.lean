/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Matrix.Certificates
public import NormalForms.Matrix.Hermite.Defs
public import NormalForms.Matrix.Hermite.Algorithm

/-!
# Hermite Normal Form Interface

The executable kernel is stated over `Fin`. Arbitrary finite index types retain
the exact caller-selected indexing together with that strong `Fin` result;
matrices on the original index types are derived projections.
-/

namespace NormalForms.Matrix.Hermite

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix

/-- A strong Hermite result together with the exact indexing used to compute it. -/
public structure HNFResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) where
  indexing : MatrixIndexing m n
  finResult : HNFResultFin (indexing.reindex A)

namespace HNFResult

/-- Left transform expressed on the original row index type. -/
@[expose] public def U {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : HNFResult A) :
    _root_.Matrix m m R :=
  _root_.Matrix.reindex result.indexing.rows.equiv.symm
    result.indexing.rows.equiv.symm result.finResult.U

/-- Hermite matrix expressed on the original row and column index types. -/
@[expose] public def H {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : HNFResult A) :
    _root_.Matrix m n R :=
  _root_.Matrix.reindex result.indexing.rows.equiv.symm
    result.indexing.cols.equiv.symm result.finResult.H

/-- Explicit inverse certificate transported back to the original row type. -/
@[expose] public def U_cert {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : HNFResult A) :
    MatrixInverseCertificate result.U :=
  result.finResult.U_cert.reindex result.indexing.rows.equiv.symm

/-- The transformation equation on the original index types. -/
public theorem equation {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : HNFResult A) :
    result.U * A = result.H := by
  let em := result.indexing.rows.equiv
  let en := result.indexing.cols.equiv
  let Afin := result.indexing.reindex A
  have hmul :
      _root_.Matrix.reindex em.symm en.symm (result.finResult.U * Afin) =
        _root_.Matrix.reindex em.symm em.symm result.finResult.U *
          _root_.Matrix.reindex em.symm en.symm Afin := by
    have h :=
      Matrix.reindexLinearEquiv_mul R R em.symm em.symm en.symm result.finResult.U Afin
    simpa only [Matrix.coe_reindexLinearEquiv] using h.symm
  have hEq :=
    congrArg (_root_.Matrix.reindex em.symm en.symm) result.finResult.equation
  have hAfin : _root_.Matrix.reindex em.symm en.symm Afin = A := by
    ext i j
    simp [Afin, MatrixIndexing.reindex, em, en]
  change
    _root_.Matrix.reindex em.symm em.symm result.finResult.U * A =
      _root_.Matrix.reindex em.symm en.symm result.finResult.H
  calc
    _root_.Matrix.reindex em.symm em.symm result.finResult.U * A =
        _root_.Matrix.reindex em.symm em.symm result.finResult.U *
          _root_.Matrix.reindex em.symm en.symm Afin := by rw [hAfin]
    _ = _root_.Matrix.reindex em.symm en.symm (result.finResult.U * Afin) := hmul.symm
    _ = _root_.Matrix.reindex em.symm en.symm result.finResult.H := by
      simpa [Afin] using hEq

/-- The derived original-index Hermite matrix has the semantics for the stored indexing. -/
public theorem isHermite {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : HNFResult A) :
    IsHermiteNormalFormWith result.indexing result.H := by
  unfold IsHermiteNormalFormWith MatrixIndexing.reindex
  convert result.finResult.isHermite using 1
  ext i j
  simp [H]

/-- Forget the Hermite witness while retaining the constructive inverse. -/
@[expose] public def toCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : HNFResult A) :
    LeftCertificate A :=
  { U := result.U
    U_cert := result.U_cert
    result := result.H
    equation := result.equation }

/--
Results computed with any two indexings remain constructively left equivalent.
No equality is claimed when the stored column orderings differ.
-/
@[expose] public def leftEquivalentCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (source target : HNFResult A) :
    LeftCertificate source.H :=
  { U := target.U * source.U_cert.inverse
    U_cert := target.U_cert.mul source.U_cert.symm
    result := target.H
    equation := by
      have hRecover : source.U_cert.inverse * source.H = A := by
        calc
          source.U_cert.inverse * source.H =
              source.U_cert.inverse * (source.U * A) := by rw [source.equation]
          _ = (source.U_cert.inverse * source.U) * A := by
                rw [_root_.Matrix.mul_assoc]
          _ = A := by rw [source.U_cert.left_inv]; simp
      calc
        (target.U * source.U_cert.inverse) * source.H =
            target.U * (source.U_cert.inverse * source.H) := by
              rw [_root_.Matrix.mul_assoc]
        _ = target.U * A := by rw [hRecover]
        _ = target.H := target.equation }

end HNFResult

/-- Compute using an explicit row and column indexing. -/
@[expose] public def hermiteNormalFormWithIndexing {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (indexing : MatrixIndexing m n) (A : _root_.Matrix m n R) : HNFResult A :=
  { indexing := indexing
    finResult := hermiteNormalFormFin (indexing.reindex A) }

@[simp] public theorem hermiteNormalFormWithIndexing_indexing {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (indexing : MatrixIndexing m n) (A : _root_.Matrix m n R) :
    (hermiteNormalFormWithIndexing indexing A).indexing = indexing :=
  rfl

@[simp] public theorem hermiteNormalFormWithIndexing_finResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (indexing : MatrixIndexing m n) (A : _root_.Matrix m n R) :
    (hermiteNormalFormWithIndexing indexing A).finResult =
      hermiteNormalFormFin (indexing.reindex A) :=
  rfl

/-- Compute using caller-supplied row and column equivalences. -/
@[expose] public def hermiteNormalFormWithEquiv {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (rows : m ≃ Fin (Fintype.card m)) (cols : n ≃ Fin (Fintype.card n))
    (A : _root_.Matrix m n R) : HNFResult A :=
  hermiteNormalFormWithIndexing (MatrixIndexing.ofEquiv rows cols) A

@[simp] public theorem hermiteNormalFormWithEquiv_indexing {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (rows : m ≃ Fin (Fintype.card m)) (cols : n ≃ Fin (Fintype.card n))
    (A : _root_.Matrix m n R) :
    (hermiteNormalFormWithEquiv rows cols A).indexing =
      MatrixIndexing.ofEquiv rows cols :=
  rfl

/-- Compute using increasing enumeration on finite linear orders. -/
@[expose] public def hermiteNormalFormOrdered {m n R : Type _}
    [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) : HNFResult A :=
  hermiteNormalFormWithIndexing (MatrixIndexing.ordered m n) A

@[simp] public theorem hermiteNormalFormOrdered_indexing {m n R : Type _}
    [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) :
    (hermiteNormalFormOrdered A).indexing = MatrixIndexing.ordered m n :=
  rfl

/-- Convenience wrapper using an arbitrary, explicitly stored finite indexing. -/
public noncomputable def hermiteNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) : HNFResult A :=
  hermiteNormalFormWithIndexing (MatrixIndexing.arbitrary m n) A

/-- The direct result always carries its Hermite proof. -/
public theorem hermiteNormalForm_isHermite {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) :
    IsHermiteNormalFormWith (hermiteNormalForm A).indexing (hermiteNormalForm A).H :=
  (hermiteNormalForm A).isHermite

/-- Determinant compatibility view derived from the explicit inverse certificate. -/
public theorem hermiteNormalForm_unimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) :
    Unimodular (hermiteNormalForm A).U :=
  (hermiteNormalForm A).U_cert.unimodular

end NormalForms.Matrix.Hermite
