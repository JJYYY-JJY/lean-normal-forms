/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Matrix.Certificates
public import NormalForms.Matrix.Hermite.Defs
public import NormalForms.Matrix.Smith.Defs
public import NormalForms.Matrix.Smith.Algorithm
import all NormalForms.Matrix.Smith.Algorithm

/-!
# Smith Normal Form Interface

The recursive kernel is stated over `Fin`. Results for arbitrary finite index
types retain the exact caller-selected indexing and derive all original-index
matrices and inverse certificates from the strong `Fin` result.
-/

namespace NormalForms.Matrix.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix
open NormalForms.Matrix.Hermite

/-- A strong Smith result together with the exact indexing used to compute it. -/
public structure SNFResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) where
  indexing : MatrixIndexing m n
  finResult : SNFResultFin (indexing.reindex A)

namespace SNFResult

@[expose] public def U {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    _root_.Matrix m m R :=
  _root_.Matrix.reindex result.indexing.rows.equiv.symm
    result.indexing.rows.equiv.symm result.finResult.U

@[expose] public def S {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    _root_.Matrix m n R :=
  _root_.Matrix.reindex result.indexing.rows.equiv.symm
    result.indexing.cols.equiv.symm result.finResult.S

@[expose] public def V {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    _root_.Matrix n n R :=
  _root_.Matrix.reindex result.indexing.cols.equiv.symm
    result.indexing.cols.equiv.symm result.finResult.V

@[expose] public def U_cert {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    MatrixInverseCertificate result.U :=
  result.finResult.U_cert.reindex result.indexing.rows.equiv.symm

@[expose] public def V_cert {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    MatrixInverseCertificate result.V :=
  result.finResult.V_cert.reindex result.indexing.cols.equiv.symm

/-- The two-sided transformation equation on the original index types. -/
public theorem equation {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    result.U * A * result.V = result.S := by
  let em := result.indexing.rows.equiv
  let en := result.indexing.cols.equiv
  let Afin := result.indexing.reindex A
  have hmulRight :
      _root_.Matrix.reindex em.symm en.symm
          (result.finResult.U * Afin * result.finResult.V) =
        _root_.Matrix.reindex em.symm en.symm (result.finResult.U * Afin) *
          _root_.Matrix.reindex en.symm en.symm result.finResult.V := by
    have h :=
      Matrix.reindexLinearEquiv_mul R R em.symm en.symm en.symm
        (result.finResult.U * Afin) result.finResult.V
    simpa only [Matrix.coe_reindexLinearEquiv] using h.symm
  have hmulLeft :
      _root_.Matrix.reindex em.symm en.symm (result.finResult.U * Afin) =
        _root_.Matrix.reindex em.symm em.symm result.finResult.U *
          _root_.Matrix.reindex em.symm en.symm Afin := by
    have h :=
      Matrix.reindexLinearEquiv_mul R R em.symm em.symm en.symm result.finResult.U Afin
    simpa only [Matrix.coe_reindexLinearEquiv] using h.symm
  have hAfin : _root_.Matrix.reindex em.symm en.symm Afin = A := by
    ext i j
    simp [Afin, MatrixIndexing.reindex, em, en]
  have hEq :=
    congrArg (_root_.Matrix.reindex em.symm en.symm) result.finResult.equation
  change
    _root_.Matrix.reindex em.symm em.symm result.finResult.U * A *
        _root_.Matrix.reindex en.symm en.symm result.finResult.V =
      _root_.Matrix.reindex em.symm en.symm result.finResult.S
  calc
    _root_.Matrix.reindex em.symm em.symm result.finResult.U * A *
        _root_.Matrix.reindex en.symm en.symm result.finResult.V =
      _root_.Matrix.reindex em.symm en.symm (result.finResult.U * Afin) *
        _root_.Matrix.reindex en.symm en.symm result.finResult.V := by
          rw [hmulLeft, hAfin]
    _ = _root_.Matrix.reindex em.symm en.symm
        (result.finResult.U * Afin * result.finResult.V) := hmulRight.symm
    _ = _root_.Matrix.reindex em.symm en.symm result.finResult.S := by
      simpa [Afin] using hEq

/-- The derived original-index Smith matrix has the semantics for the stored indexing. -/
public theorem isSmith {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    IsSmithNormalFormWith result.indexing result.S := by
  unfold IsSmithNormalFormWith MatrixIndexing.reindex
  convert Internal.isSmithNormalFormFin_toDiag result.finResult.isSmith using 1
  ext i j
  simp [S]

/-- Canonical nonzero diagonal factors from the stored `Fin` result. -/
public noncomputable def invariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) : List R :=
  smithInvariantFactorsFin result.finResult.S

/-- The stored factors are exactly those of the strong `Fin` result. -/
public theorem invariantFactors_eq_fin {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    result.invariantFactors = smithInvariantFactorsFin result.finResult.S := by
  rfl

/-- Internal implementation bridge for proofs that recurse over the factor reader. -/
theorem invariantFactors_eq_internal {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    result.invariantFactors = Internal.invariantFactors result.finResult.S := by
  rfl

/-- Reindexing the derived Smith matrix recovers the stored canonical factors. -/
public theorem invariantFactorsWith_S {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    smithInvariantFactorsWith result.indexing result.S = result.invariantFactors := by
  rw [result.invariantFactors_eq_fin]
  unfold smithInvariantFactorsWith
  congr 1
  ext i j
  simp [S, MatrixIndexing.reindex]

/-- Forget the Smith witness while retaining both constructive inverses. -/
@[expose] public def toCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    TwoSidedCertificate A :=
  { U := result.U
    U_cert := result.U_cert
    result := result.S
    V := result.V
    V_cert := result.V_cert
    equation := result.equation }

/--
The canonical `Fin` matrices produced under two indexings are constructively
two-sided equivalent. Uniqueness upgrades this certificate to equality.
-/
@[expose] public def finChangeIndexingCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (source target : SNFResult A) :
    TwoSidedCertificate source.finResult.S :=
  let P := source.indexing.rowPermutation (R := R) target.indexing
  let Q := source.indexing.columnPermutation (R := R) target.indexing
  { U := target.finResult.U * P * source.finResult.U_cert.inverse
    U_cert :=
      (target.finResult.U_cert.mul
        (MatrixInverseCertificate.rowPermutation source.indexing target.indexing)).mul
        source.finResult.U_cert.symm
    result := target.finResult.S
    V := source.finResult.V_cert.inverse * Q * target.finResult.V
    V_cert :=
      (source.finResult.V_cert.symm.mul
        (MatrixInverseCertificate.columnPermutation source.indexing target.indexing)).mul
        target.finResult.V_cert
    equation := by
      have hRecover :
          source.finResult.U_cert.inverse * source.finResult.S *
              source.finResult.V_cert.inverse =
            source.indexing.reindex A := by
        calc
          source.finResult.U_cert.inverse * source.finResult.S *
                source.finResult.V_cert.inverse =
              source.finResult.U_cert.inverse *
                  (source.finResult.U * source.indexing.reindex A *
                    source.finResult.V) *
                source.finResult.V_cert.inverse := by
                  rw [source.finResult.equation]
          _ = (source.finResult.U_cert.inverse * source.finResult.U) *
                source.indexing.reindex A *
                  (source.finResult.V * source.finResult.V_cert.inverse) := by
                    simp only [_root_.Matrix.mul_assoc]
          _ = source.indexing.reindex A := by
                rw [source.finResult.U_cert.left_inv,
                  source.finResult.V_cert.right_inv]
                simp
      have hIndex :
          P * source.indexing.reindex A * Q = target.indexing.reindex A :=
        MatrixIndexing.rowPermutation_mul_reindex_mul_columnPermutation
          source.indexing target.indexing A
      calc
        (target.finResult.U * P * source.finResult.U_cert.inverse) *
              source.finResult.S *
            (source.finResult.V_cert.inverse * Q * target.finResult.V) =
          target.finResult.U * P *
              (source.finResult.U_cert.inverse * source.finResult.S *
                source.finResult.V_cert.inverse) *
            Q * target.finResult.V := by
              simp only [_root_.Matrix.mul_assoc]
        _ = target.finResult.U * P * source.indexing.reindex A *
              Q * target.finResult.V := by rw [hRecover]
        _ = target.finResult.U *
              (P * source.indexing.reindex A * Q) * target.finResult.V := by
                simp only [_root_.Matrix.mul_assoc]
        _ = target.finResult.U * target.indexing.reindex A *
              target.finResult.V := by rw [hIndex]
        _ = target.finResult.S := target.finResult.equation }

end SNFResult

/-- Compute using an explicit row and column indexing. -/
@[expose] public def smithNormalFormWithIndexing {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (indexing : MatrixIndexing m n) (A : _root_.Matrix m n R) : SNFResult A :=
  { indexing := indexing
    finResult := smithNormalFormFin (indexing.reindex A) }

@[simp] public theorem smithNormalFormWithIndexing_indexing {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (indexing : MatrixIndexing m n) (A : _root_.Matrix m n R) :
    (smithNormalFormWithIndexing indexing A).indexing = indexing :=
  rfl

@[simp] public theorem smithNormalFormWithIndexing_finResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (indexing : MatrixIndexing m n) (A : _root_.Matrix m n R) :
    (smithNormalFormWithIndexing indexing A).finResult =
      smithNormalFormFin (indexing.reindex A) :=
  rfl

/-- Compute using caller-supplied row and column equivalences. -/
@[expose] public def smithNormalFormWithEquiv {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (rows : m ≃ Fin (Fintype.card m)) (cols : n ≃ Fin (Fintype.card n))
    (A : _root_.Matrix m n R) : SNFResult A :=
  smithNormalFormWithIndexing (MatrixIndexing.ofEquiv rows cols) A

@[simp] public theorem smithNormalFormWithEquiv_indexing {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (rows : m ≃ Fin (Fintype.card m)) (cols : n ≃ Fin (Fintype.card n))
    (A : _root_.Matrix m n R) :
    (smithNormalFormWithEquiv rows cols A).indexing =
      MatrixIndexing.ofEquiv rows cols :=
  rfl

/-- Compute using increasing enumeration on finite linear orders. -/
@[expose] public def smithNormalFormOrdered {m n R : Type _}
    [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) : SNFResult A :=
  smithNormalFormWithIndexing (MatrixIndexing.ordered m n) A

@[simp] public theorem smithNormalFormOrdered_indexing {m n R : Type _}
    [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) :
    (smithNormalFormOrdered A).indexing = MatrixIndexing.ordered m n :=
  rfl

/-- Convenience wrapper using an arbitrary, explicitly stored finite indexing. -/
public noncomputable def smithNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) : SNFResult A :=
  smithNormalFormWithIndexing (MatrixIndexing.arbitrary m n) A

public theorem smithNormalForm_isSmith {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) :
    IsSmithNormalFormWith (smithNormalForm A).indexing (smithNormalForm A).S :=
  (smithNormalForm A).isSmith

public theorem smithNormalForm_leftUnimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) :
    Unimodular (smithNormalForm A).U :=
  (smithNormalForm A).U_cert.unimodular

public theorem smithNormalForm_rightUnimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) :
    Unimodular (smithNormalForm A).V :=
  (smithNormalForm A).V_cert.unimodular

end NormalForms.Matrix.Smith
