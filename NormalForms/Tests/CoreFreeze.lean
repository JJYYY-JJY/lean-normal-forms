/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms

/-!
# Version 1 Core Interface Freeze

These type ascriptions are intentionally more exact than the name-only facade
regression.  They pin the constructors, argument order, result dependencies,
certificate schema identifier, indexing storage, and presentation direction
that version 1 promises to preserve.
-/

namespace NormalForms.Tests.CoreFreeze

open scoped Matrix
open NormalForms
open NormalForms.Certificate
open NormalForms.Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith

noncomputable section

/-! ## Certificate schema and raw data -/

example : schemaV1 = "normalforms.cert/v1" :=
  schemaV1_eq

example :
    Option String → Option String → Option String → Option String →
      CertificateMetadata :=
  CertificateMetadata.mk

example : Nat → Nat → Array Int → RawMatrix :=
  RawMatrix.mk

example :
    RawMatrix → RawMatrix → RawMatrix → RawMatrix →
      CertificateMetadata → RawHNFCertificate :=
  RawHNFCertificate.mk

example :
    RawMatrix → RawMatrix → RawMatrix → RawMatrix → RawMatrix → RawMatrix →
      CertificateMetadata → RawSNFCertificate :=
  RawSNFCertificate.mk

example {m n : Nat} :
    Matrix (Fin m) (Fin m) Int →
      Matrix (Fin m) (Fin m) Int →
      Matrix (Fin m) (Fin n) Int →
      CheckedHNFData m n :=
  CheckedHNFData.mk

example {m n : Nat} :
    Matrix (Fin m) (Fin m) Int →
      Matrix (Fin m) (Fin m) Int →
      Matrix (Fin m) (Fin n) Int →
      Matrix (Fin n) (Fin n) Int →
      Matrix (Fin n) (Fin n) Int →
      CheckedSNFData m n :=
  CheckedSNFData.mk

example {m n : Nat} :
    Matrix (Fin m) (Fin n) Int → RawHNFCertificate →
      Except CertError (CheckedHNFData m n) :=
  checkHNF

example {m n : Nat} :
    Matrix (Fin m) (Fin n) Int → RawSNFCertificate →
      Except CertError (CheckedSNFData m n) :=
  checkSNF

example {m n : Nat}
    {expected : Matrix (Fin m) (Fin n) Int}
    {raw : RawHNFCertificate}
    {checked : CheckedHNFData m n} :
    checkHNF expected raw = .ok checked → HNFResultFin expected :=
  checkHNF_sound

example {m n : Nat}
    {expected : Matrix (Fin m) (Fin n) Int}
    {raw : RawSNFCertificate}
    {checked : CheckedSNFData m n} :
    checkSNF expected raw = .ok checked → SNFResultFin expected :=
  checkSNF_sound

/-! ## Explicit indexing and strong results -/

example {α : Type _} [Fintype α] :
    (α ≃ Fin (Fintype.card α)) → FiniteIndexing α :=
  FiniteIndexing.mk

example (n : Nat) : FiniteIndexing (Fin n) :=
  FiniteIndexing.fin n

example {α : Type _} [Fintype α] :
    (α ≃ Fin (Fintype.card α)) → FiniteIndexing α :=
  FiniteIndexing.ofEquiv

example (α : Type _) [Fintype α] [LinearOrder α] : FiniteIndexing α :=
  FiniteIndexing.ordered α

example (α : Type _) [Fintype α] : FiniteIndexing α :=
  FiniteIndexing.arbitrary α

example {m n : Type _} [Fintype m] [Fintype n] :
    FiniteIndexing m → FiniteIndexing n → MatrixIndexing m n :=
  MatrixIndexing.mk

example (m n : Nat) : MatrixIndexing (Fin m) (Fin n) :=
  MatrixIndexing.fin m n

example {m n : Type _} [Fintype m] [Fintype n] :
    (m ≃ Fin (Fintype.card m)) →
      (n ≃ Fin (Fintype.card n)) →
      MatrixIndexing m n :=
  MatrixIndexing.ofEquiv

example (m n : Type _)
    [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n] :
    MatrixIndexing m n :=
  MatrixIndexing.ordered m n

example (m n : Type _) [Fintype m] [Fintype n] :
    MatrixIndexing m n :=
  MatrixIndexing.arbitrary m n

example {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : Matrix m n R} :
    (U : Matrix m m R) →
      (result : Matrix m n R) →
      U * A = result →
      LeftTransformEquation A :=
  LeftTransformEquation.mk

example {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : Matrix m n R} :
    (U : Matrix m m R) →
      (result : Matrix m n R) →
      (V : Matrix n n R) →
      U * A * V = result →
      TwoSidedTransformEquation A :=
  TwoSidedTransformEquation.mk

example {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    {U : Matrix n n R} :
    (inverse : Matrix n n R) →
      inverse * U = 1 →
      U * inverse = 1 →
      MatrixInverseCertificate U :=
  MatrixInverseCertificate.mk

example {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : Matrix m n R} :
    (U : Matrix m m R) →
      MatrixInverseCertificate U →
      (result : Matrix m n R) →
      U * A = result →
      LeftCertificate A :=
  LeftCertificate.mk

example {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : Matrix m n R} :
    (U : Matrix m m R) →
      MatrixInverseCertificate U →
      (result : Matrix m n R) →
      (V : Matrix n n R) →
      MatrixInverseCertificate V →
      U * A * V = result →
      TwoSidedCertificate A :=
  TwoSidedCertificate.mk

example {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : Matrix (Fin m) (Fin n) R} :
    (U : Matrix (Fin m) (Fin m) R) →
      MatrixInverseCertificate U →
      (H : Matrix (Fin m) (Fin n) R) →
      U * A = H →
      IsHermiteNormalFormFin H →
      HNFResultFin A :=
  HNFResultFin.mk

example {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : Matrix (Fin m) (Fin n) R} :
    (U : Matrix (Fin m) (Fin m) R) →
      MatrixInverseCertificate U →
      (S : Matrix (Fin m) (Fin n) R) →
      (V : Matrix (Fin n) (Fin n) R) →
      MatrixInverseCertificate V →
      U * A * V = S →
      IsSmithNormalFormFin S →
      SNFResultFin A :=
  SNFResultFin.mk

example {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : Matrix m n R} :
    (indexing : MatrixIndexing m n) →
      HNFResultFin (indexing.reindex A) →
      HNFResult A :=
  HNFResult.mk

example {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : Matrix m n R} :
    (indexing : MatrixIndexing m n) →
      SNFResultFin (indexing.reindex A) →
      SNFResult A :=
  SNFResult.mk

section EntryPoints

variable {rows cols : Nat} {R : Type _}
  [EuclideanDomain R] [NormalizationMonoid R]
  [ComputableEuclideanOps R] [DecidableEq R] [CanonicalMod R]

example :
    (A : Matrix (Fin rows) (Fin cols) R) → HNFResultFin A :=
  hermiteNormalFormFin

example :
    (A : Matrix (Fin rows) (Fin cols) R) → SNFResultFin A :=
  smithNormalFormFin

variable {m n : Type _}
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

example :
    (indexing : MatrixIndexing m n) → (A : Matrix m n R) → HNFResult A :=
  hermiteNormalFormWithIndexing

example :
    (indexing : MatrixIndexing m n) → (A : Matrix m n R) → SNFResult A :=
  smithNormalFormWithIndexing

example :
    (m ≃ Fin (Fintype.card m)) →
      (n ≃ Fin (Fintype.card n)) →
      (A : Matrix m n R) →
      HNFResult A :=
  hermiteNormalFormWithEquiv

example :
    (m ≃ Fin (Fintype.card m)) →
      (n ≃ Fin (Fintype.card n)) →
      (A : Matrix m n R) →
      SNFResult A :=
  smithNormalFormWithEquiv

example : (A : Matrix m n R) → HNFResult A :=
  hermiteNormalForm

example : (A : Matrix m n R) → SNFResult A :=
  smithNormalForm

end EntryPoints

section OrderedEntryPoints

variable {m n R : Type _}
  [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n]
  [EuclideanDomain R] [NormalizationMonoid R]
  [ComputableEuclideanOps R] [DecidableEq R] [CanonicalMod R]

example : (A : Matrix m n R) → HNFResult A :=
  hermiteNormalFormOrdered

example : (A : Matrix m n R) → SNFResult A :=
  smithNormalFormOrdered

end OrderedEntryPoints

/-! ## Constructive Euclidean seam -/

section ComputableEuclidean

variable {R : Type _}
  [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]

example : R → R → Bool :=
  ComputableEuclideanOps.eqb

example : R → R → R × R :=
  ComputableEuclideanOps.divMod

example : R → R :=
  ComputableEuclideanOps.normalize

example : R → R :=
  ComputableEuclideanOps.normUnit

example : R → R → XGCDResult R :=
  ComputableEuclideanOps.xgcd

example : R → Nat :=
  ComputableEuclideanOps.measure

example : R → Rˣ :=
  ComputableEuclideanOps.normUnitUnit

example : R → R → R :=
  ComputableEuclideanOps.quot

example : R → R → R :=
  ComputableEuclideanOps.rem

example : R → Bool :=
  ComputableEuclideanOps.isZeroB

example : R → R → Bool :=
  ComputableEuclideanOps.dvdB

end ComputableEuclidean

/-! ## Intrinsic Smith data -/

example {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] :
    (rank : Nat) →
      (rank_le : rank ≤ Nat.min m n) →
      (diagonal : Fin (Nat.min m n) → R) →
      (∀ i, i.1 < rank → diagonal i ≠ 0) →
      (∀ i, rank ≤ i.1 → diagonal i = 0) →
      (∀ i, diagonal i = normalize (diagonal i)) →
      (∀ i j, i.1 ≤ j.1 → diagonal i ∣ diagonal j) →
      SmithData m n R :=
  SmithData.mk

example {R : Type _} [MonoidWithZero R] :
    (rows : Nat) →
      (cols : Nat) →
      (rank : Nat) →
      (factors : Multiset (Associates R)) →
      factors.card = rank →
      (∀ factor ∈ factors, factor ≠ 0) →
      SmithSignature R :=
  SmithSignature.mk

/-! ## Column-oriented finite-free presentations -/

example {R : Type _} :
    (numGenerators : Nat) →
      (numRelations : Nat) →
      Matrix (Fin numGenerators) (Fin numRelations) R →
      FiniteFreePresentation R :=
  FiniteFreePresentation.mk

example {R : Type _} [CommRing R]
    (presentation : FiniteFreePresentation R) :
    presentation.relationModule →ₗ[R] presentation.generatorModule :=
  presentation.relationMap

example {R : Type _} [CommRing R]
    (presentation : FiniteFreePresentation R) :
    presentation.presentedModule =
      (presentation.generatorModule ⧸ LinearMap.range presentation.relationMap) :=
  rfl

example {R : Type _} [CommRing R]
    (presentation : FiniteFreePresentation R) (k : Nat) :
    presentation.fittingIdeal k =
      Matrix.Smith.determinantalIdealFin presentation.relationMatrix
        (presentation.numGenerators - k) :=
  rfl

end

end NormalForms.Tests.CoreFreeze
