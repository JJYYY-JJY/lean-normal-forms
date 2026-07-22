/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms

set_option linter.privateModule false

/-!
# Explicit Indexing Regression Tests

These tests use two genuinely different row and column enumerations. They
exercise permutation transport, strict caller-order retention, HNF left
equivalence, SNF indexing independence, and zero-dimensional strong results.
-/

namespace NormalForms.Tests.Indexing

open scoped Matrix
open NormalForms.Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith

def matrixZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  !![2, 4, 6;
     0, 8, 10]

def reversedRows : Fin 2 ≃ Fin (Fintype.card (Fin 2)) :=
  (Equiv.swap (0 : Fin 2) (1 : Fin 2)).trans (FiniteIndexing.fin 2).equiv

def reversedCols : Fin 3 ≃ Fin (Fintype.card (Fin 3)) :=
  (Equiv.swap (0 : Fin 3) (2 : Fin 3)).trans (FiniteIndexing.fin 3).equiv

def sourceIndexing : MatrixIndexing (Fin 2) (Fin 3) :=
  MatrixIndexing.fin 2 3

def targetIndexing : MatrixIndexing (Fin 2) (Fin 3) :=
  MatrixIndexing.ofEquiv reversedRows reversedCols

theorem explicitIndexingsArePermuted :
    sourceIndexing.rowPermutation (R := Int) targetIndexing *
          sourceIndexing.reindex matrixZ *
        sourceIndexing.columnPermutation (R := Int) targetIndexing =
      targetIndexing.reindex matrixZ :=
  MatrixIndexing.rowPermutation_mul_reindex_mul_columnPermutation
    sourceIndexing targetIndexing matrixZ

noncomputable def hnfSource : HNFResult matrixZ :=
  hermiteNormalFormWithIndexing sourceIndexing matrixZ

noncomputable def hnfTarget : HNFResult matrixZ :=
  hermiteNormalFormWithEquiv reversedRows reversedCols matrixZ

theorem hnfWithEquivUsesCallerOrder :
    hnfTarget.indexing = targetIndexing := by
  simp [hnfTarget, targetIndexing]

theorem hnfWrapperMatchesFinKernel :
    hnfSource.finResult = hermiteNormalFormFin (sourceIndexing.reindex matrixZ) := by
  simp [hnfSource]

theorem hnfIndexingChangeIsLeftEquivalent :
    (hnfSource.leftEquivalentCertificate hnfTarget).U * hnfSource.H =
      hnfTarget.H :=
  (hnfSource.leftEquivalentCertificate hnfTarget).equation

theorem hnfIndexingChangeLeftInverse :
    (hnfSource.leftEquivalentCertificate hnfTarget).U_cert.inverse *
        (hnfSource.leftEquivalentCertificate hnfTarget).U = 1 :=
  (hnfSource.leftEquivalentCertificate hnfTarget).U_cert.left_inv

noncomputable def snfSource : SNFResult matrixZ :=
  smithNormalFormWithIndexing sourceIndexing matrixZ

noncomputable def snfTarget : SNFResult matrixZ :=
  smithNormalFormWithEquiv reversedRows reversedCols matrixZ

theorem snfWithEquivUsesCallerOrder :
    snfTarget.indexing = targetIndexing := by
  simp [snfTarget, targetIndexing]

theorem snfWrapperMatchesFinKernel :
    snfSource.finResult = smithNormalFormFin (sourceIndexing.reindex matrixZ) := by
  simp [snfSource]

theorem snfCanonicalFinMatrixIndependentOfIndexing :
    snfSource.finResult.S = snfTarget.finResult.S :=
  snfSource.finResult_S_eq snfTarget

theorem snfInvariantFactorsIndependentOfIndexing :
    snfSource.invariantFactors = snfTarget.invariantFactors :=
  snfSource.invariantFactors_eq_of_indexing_change snfTarget

theorem snfSmithDataIndependentOfIndexing :
    snfSource.smithData = snfTarget.smithData :=
  snfSource.smithData_eq_of_indexing_change snfTarget

theorem snfSmithSignatureIndependentOfIndexing :
    snfSource.smithSignature = snfTarget.smithSignature :=
  snfSource.smithSignature_eq_of_indexing_change snfTarget

theorem determinantalIdealsIndependentOfIndexing (k : Nat) :
    determinantalIdealWith sourceIndexing matrixZ k =
      determinantalIdealWith targetIndexing matrixZ k :=
  determinantalIdealWith_eq_of_indexing_change
    sourceIndexing targetIndexing matrixZ k

theorem orderedHNFUsesIncreasingEnumeration :
    (hermiteNormalFormOrdered matrixZ).indexing =
      MatrixIndexing.ordered (Fin 2) (Fin 3) :=
  hermiteNormalFormOrdered_indexing matrixZ

theorem orderedSNFUsesIncreasingEnumeration :
    (smithNormalFormOrdered matrixZ).indexing =
      MatrixIndexing.ordered (Fin 2) (Fin 3) :=
  smithNormalFormOrdered_indexing matrixZ

def zeroRowsZ : _root_.Matrix (Fin 0) (Fin 3) Int := 0
def zeroColsZ : _root_.Matrix (Fin 2) (Fin 0) Int := 0

noncomputable def zeroRowsHNF : HNFResultFin zeroRowsZ :=
  hermiteNormalFormFin zeroRowsZ

noncomputable def zeroColsSNF : SNFResultFin zeroColsZ :=
  smithNormalFormFin zeroColsZ

theorem zeroRowsHNFLeftInverse :
    zeroRowsHNF.U_cert.inverse * zeroRowsHNF.U = 1 :=
  zeroRowsHNF.U_cert.left_inv

theorem zeroRowsHNFRightInverse :
    zeroRowsHNF.U * zeroRowsHNF.U_cert.inverse = 1 :=
  zeroRowsHNF.U_cert.right_inv

theorem zeroColsSNFLeftInverse :
    zeroColsSNF.U_cert.inverse * zeroColsSNF.U = 1 :=
  zeroColsSNF.U_cert.left_inv

theorem zeroColsSNFRightInverse :
    zeroColsSNF.V * zeroColsSNF.V_cert.inverse = 1 :=
  zeroColsSNF.V_cert.right_inv

end NormalForms.Tests.Indexing
