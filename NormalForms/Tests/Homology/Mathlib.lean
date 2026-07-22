/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Examples.Homology.Basic
import all NormalForms.Examples.Homology.Simplicial
import NormalForms.Applications.Homology.NormalizedMoore

set_option linter.privateModule false

/-!
# mathlib Homology and Normalized Moore Regressions

These tests exercise the degree-zero short-complex edge case, the direct
`HomologicalComplex` realization, and the generic normalized Moore transport.
-/

namespace NormalForms.Tests.Homology.Mathlib

open CategoryTheory
open NormalForms.Applications.Homology
open NormalForms.Examples.Homology

example :
    circle.toMathlibChainComplex.d 1 0 =
      ModuleCat.ofHom (circle.boundary 0).mulVecLin :=
  circle.toMathlibChainComplex_d 0

example :
    (circle.degreeShortComplexToSc 0).τ₃ = 0 :=
  rfl

example :
    Function.Bijective (circle.mathlibHomologyEquiv 0) :=
  (circle.mathlibHomologyEquiv 0).bijective

example :
    Function.Bijective (circle.mathlibHomologyEquiv 1) :=
  (circle.mathlibHomologyEquiv 1).bijective

example :
    Function.Bijective (realProjectivePlane.mathlibHomologyDecomposition 1) :=
  (realProjectivePlane.mathlibHomologyDecomposition 1).bijective

section NormalizedMoore

variable {data : FiniteNormalizedSimplicialData}
variable (comparison : NormalizedMooreComparison data)

example :
    IsIso comparison.chainIso.hom :=
  inferInstance

example (n : Nat) :
    Function.Bijective
      (comparison.normalizedChainHomologyDecomposition n) :=
  (comparison.normalizedChainHomologyDecomposition n).bijective

example (n : Nat) :
    Function.Bijective
      (comparison.normalizedMooreHomologyDecomposition n) :=
  (comparison.normalizedMooreHomologyDecomposition n).bijective

end NormalizedMoore

end NormalForms.Tests.Homology.Mathlib
