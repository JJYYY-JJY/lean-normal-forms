/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Applications.Homology
meta import NormalForms.Applications.Homology
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public meta import NormalForms.Tests.AuditEngine

/-!
# Finite-Free Homology Axiom Audit

The semantic kernel, quotient, and decomposition layers may use
`Classical.choice`. No project axiom, `sorryAx`, or compiler/native trust
axiom is allowed.
-/

open Lean Elab Command

run_cmd do
  let declarations : Array Name :=
    #[``NormalForms.Applications.Homology.IntChainComplex.outgoing_mul_incoming,
      ``NormalForms.Applications.Homology.IntChainComplex.outgoingSmithResult,
      ``NormalForms.Applications.Homology.IntChainComplex.incomingSmithCoordinates_leading_zero,
      ``NormalForms.Applications.Homology.IntChainComplex.kernelCoordinateMatrix,
      ``NormalForms.Applications.Homology.IntChainComplex.homologyPresentation,
      ``NormalForms.Applications.Homology.IntChainComplex.kernelBasisEquiv,
      ``NormalForms.Applications.Homology.IntChainComplex.kernelBasisEquiv_symm_boundary,
      ``NormalForms.Applications.Homology.IntChainComplex.homologyPresentationEquiv,
      ``NormalForms.Applications.Homology.IntChainComplex.homologySmithResult,
      ``NormalForms.Applications.Homology.IntChainComplex.homologySmithData,
      ``NormalForms.Applications.Homology.IntChainComplex.homologyInvariantFactors,
      ``NormalForms.Applications.Homology.IntChainComplex.homologyDecomposition,
      ``NormalForms.Applications.Homology.IntChainComplex.runtimeOutgoingRank_eq_outgoingSmithRank,
      ``NormalForms.Applications.Homology.IntChainComplex.runtimeKernelCoordinateMatrix_reindex,
      ``NormalForms.Applications.Homology.IntChainComplex.runtimeHomologySmithResult,
      ``NormalForms.Applications.Homology.IntChainComplex.runtimeHomologyInvariantFactors_eq_strong,
      ``NormalForms.Applications.Homology.simplicialFaceSign,
      ``NormalForms.Applications.Homology.normalizedFaceTerm,
      ``NormalForms.Applications.Homology.normalizedBoundaryMatrix,
      ``NormalForms.Applications.Homology.FiniteNormalizedSimplicialData.boundary_mul_boundary,
      ``NormalForms.Applications.Homology.FiniteNormalizedSimplicialData.toIntChainComplex,
      ``NormalForms.Applications.Homology.FiniteNormalizedSimplicialData.ofDimensionTwo,
      ``NormalForms.Applications.Homology.IntChainComplex.toMathlibChainComplex,
      ``NormalForms.Applications.Homology.IntChainComplex.toMathlibChainComplex_d,
      ``NormalForms.Applications.Homology.IntChainComplex.mathlibDegreeShortComplex,
      ``NormalForms.Applications.Homology.IntChainComplex.homologyToDegreeQuotient,
      ``NormalForms.Applications.Homology.IntChainComplex.degreeShortComplexToSc,
      ``NormalForms.Applications.Homology.IntChainComplex.degreeHomologyIso,
      ``NormalForms.Applications.Homology.IntChainComplex.mathlibHomologyEquiv,
      ``NormalForms.Applications.Homology.IntChainComplex.mathlibHomologyDecomposition,
      ``NormalForms.Applications.Homology.intCoefficientModule,
      ``NormalForms.Applications.Homology.NormalizedMooreComparison,
      ``NormalForms.Applications.Homology.NormalizedMooreComparison.chainIso,
      ``NormalForms.Applications.Homology.NormalizedMooreComparison.karoubiNormalizedMooreIso,
      ``NormalForms.Applications.Homology.NormalizedMooreComparison.normalizedMooreChainIso,
      ``NormalForms.Applications.Homology.NormalizedMooreComparison.normalizedChainHomologyDecomposition,
      ``NormalForms.Applications.Homology.NormalizedMooreComparison.normalizedMooreHomologyDecomposition]
  let allowed : Array Name :=
    #[``propext, ``Quot.sound, ``Classical.choice]
  NormalFormsScripts.AuditEngine.run declarations allowed
    [ ("schema", Lean.Json.str "normalforms.homology-axiom-audit/v1")
    ]
    "homology audit found forbidden axioms"
