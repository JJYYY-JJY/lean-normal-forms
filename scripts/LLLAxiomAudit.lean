/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Research.LLL
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public meta import NormalForms.Tests.AuditEngine

/-!
# LLL research axiom audit

The profile may inherit the registered extensionality, quotient, and classical
principles used by finite matrices and the verified dense backend. Project
axioms, `sorryAx`, and native/compiler trust remain forbidden.
-/

open Lean Elab Command

run_cmd do
  let declarations : Array Name :=
    #[``NormalForms.Research.LLL.abs_sub_nearestInteger_le,
      ``NormalForms.Research.LLL.gramSchmidtAux_of_lt,
      ``NormalForms.Research.LLL.dot_comm,
      ``NormalForms.Research.LLL.ofDense_toDense,
      ``NormalForms.Research.LLL.toDense_ofDense,
      ``NormalForms.Research.LLL.ofDense_rowAdd,
      ``NormalForms.Research.LLL.ofDense_rowSwap,
      ``NormalForms.Research.LLL.exists_leftTransform_of_memLattice,
      ``NormalForms.Research.LLL.exists_mutualLeftTransforms_of_memLattice_iff,
      ``NormalForms.Research.LLL.isLLLReducedB_sound,
      ``NormalForms.Research.LLL.entry_natAbs_le_basisHeight,
      ``NormalForms.Research.LLL.PrimitiveCost.addition_call_cost_le_charge,
      ``NormalForms.Research.LLL.PrimitiveCost.multiplication_call_cost_le_charge,
      ``NormalForms.Research.LLL.PrimitiveCost.division_call_cost_le_charge,
      ``NormalForms.Research.LLL.FullRankLLLProfile.result_bitLength_le,
      ``NormalForms.Research.LLL.FullRankLLLProfile.bitOperationCost_le,
      ``NormalForms.Research.LLL.fullRankLLLProfilePositive,
      ``NormalForms.Research.LLL.fullRankLLLPositive,
      ``NormalForms.Research.LLL.integerLLL,
      ``NormalForms.Research.LLL.integerColumnLLL]
  let allowed : Array Name :=
    #[``propext, ``Quot.sound, ``Classical.choice]
  NormalFormsScripts.AuditEngine.run declarations allowed
    [ ("schema", Lean.Json.str "normalforms.lll-axiom-audit/v1")
    ]
    "LLL audit found forbidden axioms"
