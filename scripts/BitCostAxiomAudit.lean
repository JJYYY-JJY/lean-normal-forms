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
# Bit-Cost Reference Model Axiom Audit

The executable binary reference model contains no noncomputable branch. Its
proof layer bridges to mathlib's `ZNum`/`Nat.size` semantic lemmas, whose
transitive axiom set includes `Classical.choice`, `propext`, and `Quot.sound`.
Project axioms, `sorryAx`, and native/compiler trust remain forbidden.
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
      ``NormalForms.Research.BitCost.xgcdWithCost_cost_le,
      ``NormalForms.Research.BitCost.normalizedXGCDWithCost_spec,
      ``NormalForms.Research.BitCost.normalizedXGCDWithCost_coefficient_bitLength_le,
      ``NormalForms.Research.BitCost.normalizedXGCDWithCost_cost_le,
      ``NormalForms.Research.BitCost.euclideanIterations_le_bitLengths,
      ``NormalForms.Research.BitCost.boundedEuclideanXGCDWithCost_spec,
      ``NormalForms.Research.BitCost.boundedEuclideanXGCDWithCost_coefficient_natAbs_le,
      ``NormalForms.Research.BitCost.boundedXGCDWithCost_spec,
      ``NormalForms.Research.BitCost.boundedXGCDWithCost_coefficient_natAbs_le,
      ``NormalForms.Research.BitCost.boundedEuclideanXGCDWithCost_coefficient_bitLength_le,
      ``NormalForms.Research.BitCost.boundedEuclideanXGCDWithCost_cost_le,
      ``NormalForms.Research.BitCost.boundedEuclideanXGCDDivisions_eq_euclideanIterations,
      ``NormalForms.Research.BitCost.boundedXGCDWithCost_cost_le,
      ``NormalForms.Research.BitCost.boundedXGCDWithCost_cost_le_uniform]
  let allowed : Array Name :=
    #[``propext, ``Quot.sound, ``Classical.choice]
  NormalFormsScripts.AuditEngine.run declarations allowed
    [ ("schema", Lean.Json.str "normalforms.bit-cost-axiom-audit/v1")
    ]
    "bit-cost audit found forbidden axioms"
