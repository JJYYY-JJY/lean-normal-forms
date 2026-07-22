/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Examples.Homology.Basic
meta import NormalForms.Applications.Homology.Runtime

set_option linter.privateModule false
set_option linter.hashCommand false

/-!
# Executable Homology Regressions
-/

namespace NormalForms.Tests.Homology.Execution

open NormalForms.Applications.Homology
open NormalForms.Examples.Homology
open IntChainComplex

private def expected
    (degree chainRank outgoingRank kernelRank : Nat)
    (invariantFactors torsionFactors : List Nat)
    (bettiNumber : Nat) :
    RuntimeHomologySummary :=
  { degree
    chainRank
    outgoingRank
    kernelRank
    invariantFactors
    torsionFactors
    bettiNumber }

#guard circle.runtimeHomologySummary 0 =
  expected 0 1 0 1 [] [] 1

#guard circle.runtimeHomologySummary 1 =
  expected 1 1 0 1 [] [] 1

#guard circle.runtimeHomologySummary 2 =
  expected 2 0 0 0 [] [] 0

#guard torus.runtimeHomologySummary 0 =
  expected 0 1 0 1 [] [] 1

#guard torus.runtimeHomologySummary 1 =
  expected 1 2 0 2 [] [] 2

#guard torus.runtimeHomologySummary 2 =
  expected 2 1 0 1 [] [] 1

#guard realProjectivePlane.runtimeHomologySummary 0 =
  expected 0 1 0 1 [] [] 1

#guard realProjectivePlane.runtimeHomologySummary 1 =
  expected 1 1 0 1 [2] [2] 0

#guard realProjectivePlane.runtimeHomologySummary 2 =
  expected 2 1 1 0 [] [] 0

#guard circleWithSixCell.runtimeHomologySummary 0 =
  expected 0 1 0 1 [] [] 1

#guard circleWithSixCell.runtimeHomologySummary 1 =
  expected 1 2 0 2 [6] [6] 1

#guard circleWithSixCell.runtimeHomologySummary 2 =
  expected 2 1 1 0 [] [] 0

example :
    (realProjectivePlane.outgoingSmithResult 1).V_cert.inverse *
        (realProjectivePlane.outgoingSmithResult 1).V =
      1 :=
  (realProjectivePlane.outgoingSmithResult 1).V_cert.left_inv

example :
    (circleWithSixCell.runtimeHomologySmithResult 1).U_cert.inverse *
        (circleWithSixCell.runtimeHomologySmithResult 1).U =
      1 :=
  (circleWithSixCell.runtimeHomologySmithResult 1).U_cert.left_inv

end NormalForms.Tests.Homology.Execution
