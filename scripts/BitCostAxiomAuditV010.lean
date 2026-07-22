/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Research.BitCost
meta import all NormalForms.Research.BitCost.Representation
meta import all NormalForms.Research.BitCost.Addition
meta import all NormalForms.Research.BitCost.Multiplication
meta import all NormalForms.Research.BitCost.Division
meta import all NormalForms.Research.BitCost.XGCD
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public meta import NormalForms.Tests.AuditEngine

/-!
# Bit-cost 0.1.0 axiom-audit snapshot

This preserves the original 21 proof roots independently of the current
additive audit in `BitCostAxiomAudit.lean`.
-/

open Lean Elab Command

run_cmd do
  let declarations : Array Name :=
    #[``NormalForms.Research.BitCost.SignMagnitude.value_ofInt,
      ``NormalForms.Research.BitCost.SignMagnitude.ofInt_value,
      ``NormalForms.Research.BitCost.SignMagnitude.bitLength_eq_natSize_natAbs,
      ``NormalForms.Research.BitCost.addWithCost_value,
      ``NormalForms.Research.BitCost.addWithCost_value_bitLength_le,
      ``NormalForms.Research.BitCost.addWithCost_cost_le,
      ``NormalForms.Research.BitCost.mulWithCost_value,
      ``NormalForms.Research.BitCost.mulWithCost_value_bitLength_le,
      ``NormalForms.Research.BitCost.mulWithCost_cost_le,
      ``NormalForms.Research.BitCost.divModWithCost_quotient_value,
      ``NormalForms.Research.BitCost.divModWithCost_remainder_value,
      ``NormalForms.Research.BitCost.divModWithCost_quotient_bitLength_le,
      ``NormalForms.Research.BitCost.divModWithCost_remainder_bitLength_le,
      ``NormalForms.Research.BitCost.divModWithCost_remainder_measure_lt,
      ``NormalForms.Research.BitCost.divModWithCost_cost_le,
      ``NormalForms.Research.BitCost.xgcdWithCost_spec,
      ``NormalForms.Research.BitCost.xgcdWithCost_gcd_value,
      ``NormalForms.Research.BitCost.xgcdWithCost_bezout,
      ``NormalForms.Research.BitCost.xgcdWithCost_gcd_nonnegative,
      ``NormalForms.Research.BitCost.xgcdWithCost_coefficient_bitLength_le,
      ``NormalForms.Research.BitCost.xgcdWithCost_cost_le]
  let allowed : Array Name :=
    #[``propext, ``Quot.sound, ``Classical.choice]
  NormalFormsScripts.AuditEngine.run declarations allowed
    [ ("schema", Lean.Json.str "normalforms.bit-cost-axiom-audit/v1")
    , ("profile", Lean.Json.str "research-bit-cost-0.1.0")
    ]
    "bit-cost 0.1.0 audit found forbidden axioms"
