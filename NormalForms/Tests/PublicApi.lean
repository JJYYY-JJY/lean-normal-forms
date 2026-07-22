/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms

/-!
# Public facade API regression

This module intentionally imports only `NormalForms`. The checks below are the
v0.4.0 public-declaration baseline.
-/

#check NormalForms.XGCDResult
#check NormalForms.ComputableEuclideanOps
#check NormalForms.ComputableEuclideanOps.quot
#check NormalForms.ComputableEuclideanOps.rem
#check NormalForms.ComputableEuclideanOps.isZeroB
#check NormalForms.ComputableEuclideanOps.dvdB
#synth NormalForms.ComputableEuclideanOps Int

#check NormalForms.Certificate.schemaV1
#check NormalForms.Certificate.schemaV1_eq
#check NormalForms.Certificate.ParseError
#check NormalForms.Certificate.CertificateMetadata
#check NormalForms.Certificate.RawMatrix
#check NormalForms.Certificate.RawHNFCertificate
#check NormalForms.Certificate.RawSNFCertificate
#check NormalForms.Certificate.RawCertificate
#check NormalForms.Certificate.parseCertificate
#check NormalForms.Certificate.MatrixField
#check NormalForms.Certificate.TransformMatrix
#check NormalForms.Certificate.CertError
#check NormalForms.Certificate.CheckedHNFData
#check NormalForms.Certificate.CheckedSNFData
#check NormalForms.Certificate.HNFKernelChecks
#check NormalForms.Certificate.SNFKernelChecks
#check NormalForms.Certificate.hnfKernelChecks
#check NormalForms.Certificate.snfKernelChecks
#check NormalForms.Certificate.HNFKernelEvidence
#check NormalForms.Certificate.SNFKernelEvidence
#check NormalForms.Certificate.checkHNF
#check NormalForms.Certificate.checkSNF
#check NormalForms.Certificate.checkHNF_isOk_of_kernelEvidence
#check NormalForms.Certificate.checkSNF_isOk_of_kernelEvidence
#check NormalForms.Certificate.checkHNF_sound
#check NormalForms.Certificate.checkSNF_sound

#check NormalForms.Matrix.FiniteIndexing
#check NormalForms.Matrix.FiniteIndexing.fin
#check NormalForms.Matrix.FiniteIndexing.ofEquiv
#check NormalForms.Matrix.FiniteIndexing.ordered
#check NormalForms.Matrix.FiniteIndexing.arbitrary
#check NormalForms.Matrix.MatrixIndexing
#check NormalForms.Matrix.MatrixIndexing.fin
#check NormalForms.Matrix.MatrixIndexing.ofEquiv
#check NormalForms.Matrix.MatrixIndexing.ordered
#check NormalForms.Matrix.MatrixIndexing.arbitrary
#check NormalForms.Matrix.MatrixIndexing.rowPermutation
#check NormalForms.Matrix.MatrixIndexing.columnPermutation
#check NormalForms.Matrix.MatrixIndexing.rowPermutation_mul_reindex_mul_columnPermutation

#check NormalForms.Matrix.Certificates.Unimodular
#check NormalForms.Matrix.Certificates.LeftTransformEquation
#check NormalForms.Matrix.Certificates.TwoSidedTransformEquation
#check NormalForms.Matrix.Certificates.MatrixInverseCertificate
#check NormalForms.Matrix.Certificates.MatrixInverseCertificate.one
#check NormalForms.Matrix.Certificates.MatrixInverseCertificate.mul
#check NormalForms.Matrix.Certificates.MatrixInverseCertificate.symm
#check NormalForms.Matrix.Certificates.MatrixInverseCertificate.reindex
#check NormalForms.Matrix.Certificates.MatrixInverseCertificate.isUnit
#check NormalForms.Matrix.Certificates.MatrixInverseCertificate.unimodular
#check NormalForms.Matrix.Certificates.MatrixInverseCertificate.rowPermutation
#check NormalForms.Matrix.Certificates.MatrixInverseCertificate.columnPermutation
#check NormalForms.Matrix.Certificates.LeftCertificate
#check NormalForms.Matrix.Certificates.TwoSidedCertificate

#check NormalForms.Matrix.Hermite.CanonicalMod
#check NormalForms.Matrix.Hermite.IsHermiteNormalFormFin
#check NormalForms.Matrix.Hermite.IsHermiteNormalFormWith
#check NormalForms.Matrix.Hermite.IsHermiteNormalFormOrdered
#check NormalForms.Matrix.Hermite.HNFResultFin
#check NormalForms.Matrix.Hermite.HNFResult
#check NormalForms.Matrix.Hermite.HNFResult.toCertificate
#check NormalForms.Matrix.Hermite.HNFResult.leftEquivalentCertificate
#check NormalForms.Matrix.Hermite.hermiteNormalFormFin
#check NormalForms.Matrix.Hermite.hermiteNormalFormWithIndexing
#check NormalForms.Matrix.Hermite.hermiteNormalFormWithEquiv
#check NormalForms.Matrix.Hermite.hermiteNormalFormOrdered
#check NormalForms.Matrix.Hermite.hermiteNormalForm
#check NormalForms.Matrix.Hermite.hermiteNormalForm_isHermite
#check NormalForms.Matrix.Hermite.hermiteNormalForm_unimodular
#check NormalForms.Matrix.Hermite.isHermiteNormalFormFin_unique_of_left_equiv
#check NormalForms.Matrix.Hermite.isHermiteNormalFormWith_unique_of_left_equiv

#check NormalForms.Matrix.Smith.IsSmithNormalFormFin
#check NormalForms.Matrix.Smith.IsSmithNormalFormWith
#check NormalForms.Matrix.Smith.IsSmithNormalFormOrdered
#check NormalForms.Matrix.Smith.SNFResultFin
#check NormalForms.Matrix.Smith.SNFResult
#check NormalForms.Matrix.Smith.SmithData
#check NormalForms.Matrix.Smith.SmithData.ofSmithMatrix
#check NormalForms.Matrix.Smith.SmithData.factorAt
#check NormalForms.Matrix.Smith.SmithData.signature
#check NormalForms.Matrix.Smith.SmithSignature
#check NormalForms.Matrix.Smith.SmithSignature.rightKernelRank
#check NormalForms.Matrix.Smith.SmithSignature.leftKernelRank
#check NormalForms.Matrix.Smith.SmithSignature.cokernelFreeRank
#check NormalForms.Matrix.Smith.minorDeterminantsFin
#check NormalForms.Matrix.Smith.determinantalIdealFin
#check NormalForms.Matrix.Smith.determinantalIdealWith
#check NormalForms.Matrix.Smith.SmithData.prefixProduct
#check NormalForms.Matrix.Smith.determinantalIdealFin_zero
#check NormalForms.Matrix.Smith.determinantalIdealFin_eq_span_prefixProduct
#check NormalForms.Matrix.Smith.determinantalIdealFin_eq_bot_of_rank_lt
#check NormalForms.Matrix.Smith.determinantalIdealFin_eq_of_certificate
#check NormalForms.Matrix.Smith.determinantalIdealWith_eq_of_indexing_change
#check NormalForms.Matrix.Smith.smithRank_eq_of_determinantalIdeals
#check NormalForms.Matrix.Smith.smithFactors_eq_of_determinantalIdeals
#check NormalForms.Matrix.Smith.smithData_eq_of_determinantalIdeals
#check NormalForms.Matrix.Smith.smithSignature_eq_of_determinantalIdeals
#check NormalForms.Matrix.Smith.smithDiagonalFin
#check NormalForms.Matrix.Smith.SNFResultFin.smithData
#check NormalForms.Matrix.Smith.SNFResultFin.smithSignature
#check NormalForms.Matrix.Smith.SNFResult.smithData
#check NormalForms.Matrix.Smith.SNFResult.smithSignature
#check NormalForms.Matrix.Smith.SNFResult.smithData_eq_of_indexing_change
#check NormalForms.Matrix.Smith.SNFResult.smithSignature_eq_of_indexing_change
#check NormalForms.Matrix.Smith.smithSignature_eq_of_two_sided_equiv
#check NormalForms.Matrix.Smith.SNFResult.toCertificate
#check NormalForms.Matrix.Smith.SNFResult.finChangeIndexingCertificate
#check NormalForms.Matrix.Smith.SNFResult.finResult_S_eq
#check NormalForms.Matrix.Smith.SNFResult.invariantFactors_eq_of_indexing_change
#check NormalForms.Matrix.Smith.smithInvariantFactorsFin
#check NormalForms.Matrix.Smith.smithInvariantFactorsWith
#check NormalForms.Matrix.Smith.smithColumnSpan
#check NormalForms.Matrix.Smith.smithNormalFormFin
#check NormalForms.Matrix.Smith.smithNormalFormWithIndexing
#check NormalForms.Matrix.Smith.smithNormalFormWithEquiv
#check NormalForms.Matrix.Smith.smithNormalFormOrdered
#check NormalForms.Matrix.Smith.smithNormalForm
#check NormalForms.Matrix.Smith.smithNormalForm_isSmith
#check NormalForms.Matrix.Smith.smithNormalForm_leftUnimodular
#check NormalForms.Matrix.Smith.smithNormalForm_rightUnimodular
#check NormalForms.Matrix.Smith.isSmithNormalFormWith_unique_of_two_sided_equiv

#check NormalForms.PolynomialRatRuntime.hermiteNormalFormFin
#check NormalForms.PolynomialRatRuntime.hermiteLeftTransformFin
#check NormalForms.PolynomialRatRuntime.hermiteLeftInverseFin
#check NormalForms.PolynomialRatRuntime.smithNormalFormFin
#check NormalForms.PolynomialRatRuntime.smithLeftTransformFin
#check NormalForms.PolynomialRatRuntime.smithLeftInverseFin
#check NormalForms.PolynomialRatRuntime.smithRightTransformFin
#check NormalForms.PolynomialRatRuntime.smithRightInverseFin
#check NormalForms.PolynomialRatRuntime.certificateChecksFin

#check NormalForms.Bridge.MathlibPID.pidExecutableInvariantFactorCount
#check NormalForms.Bridge.MathlibPID.CanonicalPIDSmithBasis
#check NormalForms.Bridge.MathlibPID.CanonicalPIDSmithBasis.ofMathlib
#check NormalForms.Bridge.MathlibPID.pidSmithBasisDiagonalMatrix
#check NormalForms.Bridge.MathlibPID.pidNormalizedFactors
#check NormalForms.Bridge.MathlibPID.pidIntNatAbsList
#check NormalForms.Bridge.MathlibPID.CanonicalPIDSmithBasis.smithSignature_eq
#check NormalForms.Bridge.MathlibPID.CanonicalPIDSmithBasis.normalizedFactors_eq
#check NormalForms.Bridge.MathlibPID.CanonicalPIDSmithBasis.intNatAbsList_eq
#check NormalForms.Bridge.MathlibPID.pidExecutableQuotientEquivPiSpanProd
#check NormalForms.Bridge.MathlibPID.pidExecutableQuotientEquivPiZModProd

#check NormalForms.FiniteFreePresentation
#check NormalForms.FiniteFreePresentation.relationMap
#check NormalForms.FiniteFreePresentation.relationSubmodule
#check NormalForms.FiniteFreePresentation.presentedModule
#check NormalForms.FiniteFreePresentation.smithResult
#check NormalForms.FiniteFreePresentation.smithData
#check NormalForms.FiniteFreePresentation.smithSignature
#check NormalForms.FiniteFreePresentation.smithRank
#check NormalForms.FiniteFreePresentation.invariantFactor
#check NormalForms.FiniteFreePresentation.invariantFactors
#check NormalForms.FiniteFreePresentation.freeRank
#check NormalForms.FiniteFreePresentation.smithDecomposition
#check NormalForms.FiniteFreePresentation.displayInvariantFactors
#check NormalForms.FiniteFreePresentation.fittingIdeal
#check NormalForms.FiniteFreePresentation.fittingIdeal_numGenerators
#check NormalForms.FiniteFreePresentation.fittingIdeal_eq_bot_of_min_lt
#check NormalForms.FiniteFreePresentation.mathlibRelations
#check NormalForms.FiniteFreePresentation.mathlibQuotientEquivPresentedModule
#check NormalForms.FiniteFreePresentation.mathlibPresentation

#check NormalForms.Applications.AbelianGroups.presentationOfMatrix
#check NormalForms.Applications.AbelianGroups.presentationSubmodule
#check NormalForms.Applications.AbelianGroups.presentationQuotient
#check NormalForms.Applications.AbelianGroups.presentationInvariantFactors
#check NormalForms.Applications.AbelianGroups.presentationFreeRank
#check NormalForms.Applications.AbelianGroups.presentationQuotientEquivPiZModProd
