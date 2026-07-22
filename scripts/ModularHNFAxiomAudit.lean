/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Research.ModularHNF
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public meta import NormalForms.Tests.AuditEngine

/-!
# Modular-HNF research axiom audit

The executable value kernel and cost mirrors contain no native evaluation or
foreign-code trust.  The proof layer may inherit the registered mathlib
extensionality/quotient/classical principles; project axioms, `sorryAx`, and
compiler-trust axioms are forbidden.
-/

open Lean Elab Command

run_cmd do
  let declarations : Array Name :=
    #[``NormalForms.Research.ModularHNF.FullColumnRankWitness.columns_le_rows,
      ``NormalForms.Research.ModularHNF.FullColumnRankWitness.rational_rank_eq,
      ``NormalForms.Research.ModularHNF.ModulusWitness.positive,
      ``NormalForms.Research.ModularHNF.ModulusWitness.nonzero,
      ``NormalForms.Research.ModularHNF.rowSpan_mul_eq,
      ``NormalForms.Research.ModularHNF.augmentedRowSpan_eq_of_congruent,
      ``NormalForms.Research.ModularHNF.determinantModulus_augmentedRowSpan_eq,
      ``NormalForms.Research.ModularHNF.coefficients_zero_before_of_combination_zero,
      ``NormalForms.Research.ModularHNF.coordinate_dvd_of_mem_augmented,
      ``NormalForms.Research.ModularHNF.fullColumnShape_unique_of_rowSpan_eq,
      ``NormalForms.Research.ModularHNF.runWithDeterminantWitness_candidate_eq_reference,
      ``NormalForms.Research.ModularHNF.modularHNFFullRank_eq_reference,
      ``NormalForms.Research.ModularHNF.modularHNFFullRank_inverse_equation,
      ``NormalForms.Research.ModularHNF.FractionFreeRankProfile.column_identity_mul,
      ``NormalForms.Research.ModularHNF.integerHermiteNormalFormModularWithProfile_eq_reference,
      ``NormalForms.Research.ModularHNF.searchRankProfile_isSome,
      ``NormalForms.Research.ModularHNF.searchRankProfile_valid,
      ``NormalForms.Research.ModularHNF.integerHermiteNormalFormModular_eq_reference,
      ``NormalForms.Research.ModularHNF.ModularOperationCount.total_add,
      ``NormalForms.Research.ModularHNF.runRaw_operations_total_le,
      ``NormalForms.Research.ModularHNF.runWithDeterminantWitness_operations_total_le,
      ``NormalForms.Research.ModularHNF.entry_natAbs_le_matrixHeight,
      ``NormalForms.Research.ModularHNF.coefficientSteps_add,
      ``NormalForms.Research.ModularHNF.runRawPrefix_entriesBounded,
      ``NormalForms.Research.ModularHNF.runRaw_matrixHeight_le_intermediateBound,
      ``NormalForms.Research.ModularHNF.runWithDeterminantWitness_entry_natAbs_le,
      ``NormalForms.Research.ModularHNF.runWithDeterminantWitness_matrixHeight_le,
      ``NormalForms.Research.ModularHNF.StandardXGCD.natAuxWithCost_value,
      ``NormalForms.Research.ModularHNF.StandardXGCD.natAuxWithCost_coefficient_natAbs_le,
      ``NormalForms.Research.ModularHNF.StandardXGCD.natAuxWithCost_cost_le_closed,
      ``NormalForms.Research.ModularHNF.StandardXGCD.standardIntXGCDWithCost_value,
      ``NormalForms.Research.ModularHNF.StandardXGCD.standardIntXGCDWithCost_coefficient_natAbs_le_uniform,
      ``NormalForms.Research.ModularHNF.StandardXGCD.standardIntXGCDWithCost_coefficient_bitLength_le_uniform,
      ``NormalForms.Research.ModularHNF.StandardXGCD.standardIntXGCDWithCost_cost_le_closed,
      ``NormalForms.Research.ModularHNF.StandardXGCD.standardXGCDAuxStepBitOperationBound_mono_iterations,
      ``NormalForms.Research.ModularHNF.StandardXGCD.standardIntXGCDWithCost_cost_le_uniform,
      ``NormalForms.Research.ModularHNF.ModularOperationCount.bitOperationCost_le_total_mul_charge,
      ``NormalForms.Research.ModularHNF.Internal.addition_call_cost_le_charge,
      ``NormalForms.Research.ModularHNF.Internal.multiplication_call_cost_le_charge,
      ``NormalForms.Research.ModularHNF.Internal.division_call_cost_le_charge,
      ``NormalForms.Research.ModularHNF.Internal.standard_xgcd_call_cost_le_charge,
      ``NormalForms.Research.ModularHNF.runRaw_bitOperationCost_le,
      ``NormalForms.Research.ModularHNF.runWithDeterminantWitness_bitOperationCost_le]
  let allowed : Array Name :=
    #[``propext, ``Quot.sound, ``Classical.choice]
  NormalFormsScripts.AuditEngine.run declarations allowed
    [ ("schema", Lean.Json.str "normalforms.modular-hnf-axiom-audit/v1")
    ]
    "modular-HNF audit found forbidden axioms"
