/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Applications.Homology

set_option linter.privateModule false
set_option linter.hashCommand false

/-!
# Finite Free Homology Public API

Compilation-only freeze for the independently versioned homology facade.
-/

open NormalForms.Applications.Homology

#check IntChainComplex
#check IntChainComplex.ofLengthTwo
#check IntChainComplex.outgoingBoundary
#check IntChainComplex.incomingBoundary
#check IntChainComplex.cycles
#check IntChainComplex.boundaries
#check IntChainComplex.homology
#check IntChainComplex.outgoingSmithResult
#check IntChainComplex.outgoingSmithRank
#check IntChainComplex.kernelRank
#check IntChainComplex.incomingSmithCoordinates
#check IntChainComplex.incomingSmithCoordinates_leading_zero
#check IntChainComplex.kernelCoordinateMatrix
#check IntChainComplex.homologyPresentation
#check IntChainComplex.kernelBasisEquiv
#check IntChainComplex.kernelBasisEquiv_symm_boundary
#check IntChainComplex.homologyPresentationEquiv
#check IntChainComplex.homologySmithResult
#check IntChainComplex.homologySmithData
#check IntChainComplex.homologyInvariantFactors
#check IntChainComplex.homologyTorsionFactors
#check IntChainComplex.bettiNumber
#check IntChainComplex.homologyDecomposition
#check IntChainComplex.runtimeOutgoingRank
#check IntChainComplex.runtimeKernelCoordinateMatrix
#check IntChainComplex.runtimeKernelCoordinateMatrix_reindex
#check IntChainComplex.runtimeHomologySmithResult
#check IntChainComplex.runtimeHomologyInvariantFactors
#check IntChainComplex.runtimeHomologySummary
#check IntChainComplex.RuntimeHomologySummary
#check simplicialFaceSign
#check normalizedFaceTerm
#check normalizedBoundaryMatrix
#check FiniteNormalizedSimplicialData
#check FiniteNormalizedSimplicialData.boundary
#check FiniteNormalizedSimplicialData.boundary_mul_boundary
#check FiniteNormalizedSimplicialData.toIntChainComplex
#check FiniteNormalizedSimplicialData.ofDimensionTwo
#check IntChainComplex.toMathlibChainComplex
#check IntChainComplex.toMathlibChainComplex_d
#check IntChainComplex.mathlibDegreeShortComplex
#check IntChainComplex.homologyToDegreeQuotient
#check IntChainComplex.degreeShortComplexToSc
#check IntChainComplex.degreeHomologyIso
#check IntChainComplex.mathlibHomologyEquiv
#check IntChainComplex.mathlibHomologyDecomposition
#check intCoefficientModule
#check NormalizedMooreComparison
#check NormalizedMooreComparison.chainIso
#check NormalizedMooreComparison.karoubiNormalizedMooreIso
#check NormalizedMooreComparison.normalizedMooreChainIso
#check NormalizedMooreComparison.normalizedChainHomologyDecomposition
#check NormalizedMooreComparison.normalizedMooreHomologyDecomposition
