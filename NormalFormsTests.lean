/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Tests.PublicApi
import NormalForms.Tests.CoreFreeze
import NormalForms.Tests.AuditEngine
import NormalForms.Tests.Indexing
import NormalForms.Tests.SmithData
import NormalForms.Tests.PIDSignature
import NormalForms.Tests.Presentation
import NormalForms.Tests.Execution
import NormalForms.Tests.Certificate
import NormalForms.Tests.CertificateCLI
import NormalForms.Tests.Generated.MediumHNF
import NormalForms.Tests.Generated.MediumSNF
import NormalForms.Tests.RationalCanonical.Presentation
import NormalForms.Tests.RationalCanonical.Invariants
import NormalForms.Tests.RationalCanonical.ModuleDecomposition
import NormalForms.Tests.RationalCanonical.Companion
import NormalForms.Tests.RationalCanonical.Basis
import NormalForms.Tests.RationalCanonical.Result
import NormalForms.Tests.RationalCanonical.MinimalPolynomial
import NormalForms.Tests.RationalCanonical.Similarity
import NormalForms.Tests.RationalCanonical.PublicApi
import NormalForms.Tests.Homology.ChainComplex
import NormalForms.Tests.Homology.Execution
import NormalForms.Tests.Homology.PublicApi
import NormalForms.Tests.Homology.Simplicial
import NormalForms.Tests.Homology.Mathlib
import NormalForms.Tests.Research.BitCost.PublicApi
import NormalForms.Tests.Research.BitCost.PublicApiV010
import NormalForms.Tests.Research.BitCost.Execution
import NormalForms.Tests.Research.KannanBachem.PublicApi
import NormalForms.Tests.Research.KannanBachem.Execution
import NormalForms.Tests.Research.ModularHNF.PublicApi
import NormalForms.Tests.Research.ModularHNF.Execution
import NormalForms.Tests.Research.LLL.PublicApi
import NormalForms.Tests.Research.LLL.Execution
import all NormalForms.Examples.AbelianGroups.Basic

/-!
# NormalForms test driver

Building this test library compiles the facade API checks and the complete
internal example suite. The command elaborator also verifies the negative
facade import test against the exact intended Lean diagnostic.
-/

run_cmd do
  let checkFailure (path expected visibleMessage : String) := do
    let result ← IO.Process.output
      { cmd := "bash"
        args := #["-c", s!"exec lean {path} 1>&2"] }
    if result.exitCode == 0 then
      throwError visibleMessage
    else if result.exitCode != 1 then
      throwError
        "facade isolation test failed with exit code {result.exitCode}: {path}"
    else if result.stderr.trimAscii.toString == expected then
      Lean.logInfo s!"facade isolation test passed: {path}"
    else
      throwError "facade isolation test failed with an unexpected diagnostic:\n{result.stderr}"
  let cases : Array (String × String × String) := #[
    ("Tests/Facade/InternalLeak.lean",
      "Tests/Facade/InternalLeak.lean:15:7: error(lean.unknownIdentifier): " ++
        "Unknown identifier `NormalForms.Matrix.Smith.Internal.smithNormalFormFin`",
      "facade isolation test failed: the internal Smith kernel was visible"),
    ("Tests/Facade/CertificateInternalLeak.lean",
      "Tests/Facade/CertificateInternalLeak.lean:15:7: error(lean.unknownIdentifier): " ++
        "Unknown identifier `NormalForms.Certificate.validateHNF`",
      "facade isolation test failed: certificate checker internals were visible"),
    ("Tests/Facade/FlintFFILeak.lean",
      "Tests/Facade/FlintFFILeak.lean:15:7: error(lean.unknownIdentifier): " ++
        "Unknown identifier `NormalForms.External.Flint.generateSNF`",
      "facade isolation test failed: the optional FLINT FFI was visible"),
    ("Tests/Facade/PIDBridgeInternalLeak.lean",
      "Tests/Facade/PIDBridgeInternalLeak.lean:15:7: error(lean.unknownIdentifier): " ++
        "Unknown identifier " ++
        "`NormalForms.Bridge.MathlibPID.Internal.pidSmithRangeSplitting`",
      "facade isolation test failed: PID bridge internals were visible"),
    ("Tests/Facade/RationalCanonicalLeak.lean",
      "Tests/Facade/RationalCanonicalLeak.lean:13:7: error(lean.unknownIdentifier): " ++
        "Unknown identifier " ++
        "`NormalForms.RationalCanonical.endomorphismPresentationMatrix`",
      "facade isolation test failed: the v1.1 application was visible from the v1 core"),
    ("Tests/Facade/HomologyLeak.lean",
      "Tests/Facade/HomologyLeak.lean:13:7: error(lean.unknownIdentifier): " ++
        "Unknown identifier " ++
        "`NormalForms.Applications.Homology.IntChainComplex`",
      "facade isolation test failed: the v1.2 application was visible from the v1 core"),
    ("Tests/Facade/BitCostLeak.lean",
      "Tests/Facade/BitCostLeak.lean:13:7: error(lean.unknownIdentifier): " ++
        "Unknown identifier `NormalForms.Research.BitCost.xgcdWithCost`",
      "facade isolation test failed: the bit-cost research facade was visible from the v1 core"),
    ("Tests/Facade/KannanBachemLeak.lean",
      "Tests/Facade/KannanBachemLeak.lean:13:7: error(lean.unknownIdentifier): " ++
        "Unknown identifier " ++
        "`NormalForms.Research.KannanBachem.Hermite.semanticReference`",
      "facade isolation test failed: the Kannan--Bachem research facade " ++
        "was visible from the v1 core"),
    ("Tests/Facade/KannanBachemInternalLeak.lean",
      "Tests/Facade/KannanBachemInternalLeak.lean:13:7: error(lean.unknownIdentifier): " ++
        "Unknown identifier " ++
        "`NormalForms.Research.KannanBachem.Hermite.Traced.compute`",
      "facade isolation test failed: the traced HNF implementation was visible"),
    ("Tests/Facade/KannanBachemPrincipalInternalLeak.lean",
      "Tests/Facade/KannanBachemPrincipalInternalLeak.lean:13:7: " ++
        "error(lean.unknownIdentifier): Unknown identifier " ++
        "`NormalForms.Research.KannanBachem.Hermite.Principal.compute`",
      "facade isolation test failed: the principal-minor implementation was visible"),
    ("Tests/Facade/ModularHNFLeak.lean",
      "Tests/Facade/ModularHNFLeak.lean:13:7: " ++
        "error(lean.unknownIdentifier): Unknown identifier " ++
        "`NormalForms.Research.ModularHNF.runRaw`",
      "facade isolation test failed: the modular-HNF research facade was visible"),
    ("Tests/Facade/LLLLeak.lean",
      "Tests/Facade/LLLLeak.lean:13:7: " ++
        "error(lean.unknownIdentifier): Unknown identifier " ++
        "`NormalForms.Research.LLL.integerLLL`",
      "facade isolation test failed: the LLL research facade was visible")]
  for (path, expected, visibleMessage) in cases do
    checkFailure path expected visibleMessage
