/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Examples.Homology.Simplicial
meta import NormalForms.Applications.Homology.Runtime
meta import all NormalForms.Applications.Homology.Simplicial

set_option linter.privateModule false
set_option linter.hashCommand false

/-!
# Finite Normalized Simplicial Regressions
-/

namespace NormalForms.Tests.Homology.Simplicial

open NormalForms.Applications.Homology
open NormalForms.Examples.Homology
open FiniteNormalizedSimplicialData
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

private def circleBoundary :
    Matrix (Fin 1) (Fin 1) Int :=
  !![0]

private def filledTriangleBoundaryOne :
    Matrix (Fin 3) (Fin 3) Int :=
  !![-1, -1, 0;
      1,  0, -1;
      0,  1, 1]

private def filledTriangleBoundaryTwo :
    Matrix (Fin 3) (Fin 1) Int :=
  !![1;
     -1;
      1]

private def collapsedSphereSimplex :
    Fin (collapsedBoundarySphere.simplexCount 2) :=
  ⟨0, by
    change 0 < 1
    decide⟩

#guard simplicialFaceSign 0 = 1
#guard simplicialFaceSign 1 = -1
#guard simplicialFaceSign 2 = 1

#guard simplicialCircle.boundary 0 = circleBoundary
#guard filledTriangle.boundary 0 = filledTriangleBoundaryOne
#guard filledTriangle.boundary 1 = filledTriangleBoundaryTwo

#guard collapsedBoundarySphere.face 1 0 collapsedSphereSimplex = none

example :
    normalizedFaceTerm
        (fun _ => 1)
        (fun _ _ _ => (none : Option (Fin 1))) 1
        (row := 0)
        (column := 0)
        (i := 0) =
      0 := by
  rfl

example :
    filledTriangle.boundary 0 * filledTriangle.boundary 1 = 0 :=
  filledTriangle.boundary_mul_boundary 0

example :
    filledTriangle.toIntChainComplex.boundary 1 =
      filledTriangle.boundary 1 :=
  rfl

#guard simplicialCircle.toIntChainComplex.runtimeHomologySummary 0 =
  expected 0 1 0 1 [] [] 1

#guard simplicialCircle.toIntChainComplex.runtimeHomologySummary 1 =
  expected 1 1 0 1 [] [] 1

#guard collapsedBoundarySphere.toIntChainComplex.runtimeHomologySummary 0 =
  expected 0 1 0 1 [] [] 1

#guard collapsedBoundarySphere.toIntChainComplex.runtimeHomologySummary 1 =
  expected 1 0 0 0 [] [] 0

#guard collapsedBoundarySphere.toIntChainComplex.runtimeHomologySummary 2 =
  expected 2 1 0 1 [] [] 1

#guard filledTriangle.toIntChainComplex.runtimeHomologySummary 0 =
  expected 0 3 0 3 [1, 1] [] 1

#guard filledTriangle.toIntChainComplex.runtimeHomologySummary 1 =
  expected 1 3 2 1 [1] [] 0

#guard filledTriangle.toIntChainComplex.runtimeHomologySummary 2 =
  expected 2 1 1 0 [] [] 0

end NormalForms.Tests.Homology.Simplicial
