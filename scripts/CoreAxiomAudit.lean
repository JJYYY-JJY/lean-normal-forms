/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Euclidean.Int
import all NormalForms.Euclidean.PolynomialRat
import all NormalForms.Matrix.Certificates
import all NormalForms.Matrix.Hermite.Algorithm
import all NormalForms.Matrix.PolynomialRat
import all NormalForms.Matrix.Smith.Algorithm
meta import all NormalForms.Euclidean.Int
meta import all NormalForms.Euclidean.PolynomialRat
meta import all NormalForms.Matrix.Certificates
meta import all NormalForms.Matrix.Hermite.Algorithm
meta import all NormalForms.Matrix.PolynomialRat
meta import all NormalForms.Matrix.Smith.Algorithm
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public meta import NormalForms.Tests.AuditEngine

/-!
# Executable `Fin` core axiom audit

The constructive integer and rational-polynomial kernels are audited apart
from arbitrary finite-index wrappers and semantic quotient bridges.
`Classical.choice` and compiler/native trust axioms are forbidden.
-/

open Lean Elab Command

run_cmd do
  let declarations : Array Name :=
    #[``NormalForms.ComputableEuclideanOps,
      ``NormalForms.instComputableEuclideanOpsInt,
      ``NormalForms.Matrix.Certificates.MatrixInverseCertificate,
      ``NormalForms.Matrix.Hermite.IsHermiteNormalFormFin,
      ``NormalForms.Matrix.Smith.IsSmithNormalFormFin,
      ``NormalForms.Matrix.Hermite.HNFResultFin,
      ``NormalForms.Matrix.Smith.SNFResultFin,
      ``NormalForms.Matrix.Hermite.hermiteNormalFormFin,
      ``NormalForms.Matrix.Smith.smithNormalFormFin,
      ``NormalForms.PolynomialRatRuntime.hermiteNormalFormFin,
      ``NormalForms.PolynomialRatRuntime.smithNormalFormFin,
      ``NormalForms.PolynomialRatRuntime.certificateChecksFin]
  let allowed : Array Name := #[``propext, ``Quot.sound]
  NormalFormsScripts.AuditEngine.run declarations allowed
    [ ("schema", Lean.Json.str "normalforms.core-axiom-audit/v1")
    ]
    "executable core audit found forbidden axioms"
