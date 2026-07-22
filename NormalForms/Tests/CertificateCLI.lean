/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.CLI.EmitLean
import all NormalForms.CLI.EmitLean
meta import all NormalForms.CLI.EmitLean

set_option linter.privateModule false
set_option linter.hashCommand false

/-!
# Certificate source-emitter guards

These pure tests complement the process-level emit/compile regression. They
also ensure user-controlled names cannot inject Lean syntax.
-/

namespace NormalForms.Tests.CertificateCLI

open NormalForms.Certificate
open NormalForms.CLI.EmitLean

private def emptyMatrix : RawMatrix :=
  { rows := 0, cols := 0, entries := #[] }

private def certificate : RawCertificate :=
  .hnf
    { input := emptyMatrix
      U := emptyMatrix
      UInverse := emptyMatrix
      H := emptyMatrix }

private def options : Options :=
  { importModule := "NormalForms.Tests.Generated.ExpectedMatrices"
    matrixName := "NormalForms.Tests.Generated.mediumInput"
    declarationName := "NormalForms.Tests.Generated.emittedCertificate" }

private def renderedStrictSource : Bool :=
  match render options certificate with
  | .ok source =>
      source.contains "decide_cbv" &&
        source.contains "checkHNF_sound" &&
        !source.contains ("native_" ++ "decide") &&
        !source.contains ("Lean.ofReduce" ++ "Bool") &&
        !source.contains ("Lean.ofReduce" ++ "Nat")
  | .error _ => false

private def rejects (options : Options) : Bool :=
  !(render options certificate).isOk

#guard renderedStrictSource
#guard rejects { options with importModule := "Unsafe\n#eval 1" }
#guard rejects { options with matrixName := "Matrix); #check Nat; (" }
#guard rejects { options with declarationName := "def" }
#guard rejects { options with declarationName := "bad-name" }
#guard rejects { options with declarationName := "certificateRaw" }

end NormalForms.Tests.CertificateCLI
