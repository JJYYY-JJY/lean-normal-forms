/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Tests.Certificate
import NormalForms.Tests.Generated.MediumHNF
import NormalForms.Tests.Generated.MediumSNF
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public meta import NormalForms.Tests.AuditEngine

/-!
# Strict certificate axiom audit

The concrete `decide_cbv` certificate reconstructions are audited separately
from the arbitrary-index facade. In particular, `Classical.choice` and
compiler/native trust axioms are not permitted here.
-/

open Lean Elab Command

run_cmd do
  let declarations : Array Name :=
    #[``NormalForms.Matrix.Certificates.MatrixInverseCertificate,
      ``NormalForms.Matrix.Hermite.IsHermiteNormalFormFin,
      ``NormalForms.Matrix.Smith.IsSmithNormalFormFin,
      ``NormalForms.Matrix.Hermite.HNFResultFin,
      ``NormalForms.Matrix.Smith.SNFResultFin,
      ``NormalForms.Certificate.CheckedHNFData,
      ``NormalForms.Certificate.CheckedSNFData,
      ``NormalForms.Certificate.HNFKernelChecks,
      ``NormalForms.Certificate.SNFKernelChecks,
      ``NormalForms.Certificate.HNFKernelEvidence,
      ``NormalForms.Certificate.SNFKernelEvidence,
      ``NormalForms.Certificate.hnfKernelChecks,
      ``NormalForms.Certificate.snfKernelChecks,
      ``NormalForms.Certificate.checkHNF,
      ``NormalForms.Certificate.checkSNF,
      ``NormalForms.Certificate.checkHNF_isOk_of_kernelEvidence,
      ``NormalForms.Certificate.checkSNF_isOk_of_kernelEvidence,
      ``NormalForms.Certificate.checkHNF_sound,
      ``NormalForms.Certificate.checkSNF_sound,
      ``NormalForms.Tests.Certificate.strictHNFResult,
      ``NormalForms.Tests.Certificate.strictSNFResult,
      ``NormalForms.Tests.Generated.mediumHNFCertificate,
      ``NormalForms.Tests.Generated.mediumSNFCertificate]
  let allowed : Array Name := #[``propext, ``Quot.sound]
  NormalFormsScripts.AuditEngine.run declarations allowed
    [ ("schema", Lean.Json.str "normalforms.certificate-axiom-audit/v1")
    ]
    "strict certificate audit found forbidden axioms"
