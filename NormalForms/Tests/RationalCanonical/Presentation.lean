/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Applications.RationalCanonical
meta import NormalForms.Applications.RationalCanonical

set_option linter.privateModule false
set_option linter.hashCommand false

/-!
# Rational Canonical Presentation Tests

Regression coverage for the explicit `XI - A` formula, its zero-dimensional
case, and the bridge to mathlib's characteristic matrix.
-/

namespace NormalForms.Tests.RationalCanonical.Presentation

open Polynomial
open NormalForms.RationalCanonical

private def exampleMatrix : Matrix (Fin 2) (Fin 2) Rat :=
  !![1, 2;
     3, 4]

#guard
  (endomorphismPresentationMatrix exampleMatrix 0 0).coeff 1 == 1
#guard
  (endomorphismPresentationMatrix exampleMatrix 0 0).coeff 0 == -1
#guard
  (endomorphismPresentationMatrix exampleMatrix 0 1).coeff 0 == -2
#guard
  (endomorphismPresentationMatrix exampleMatrix 0 1).coeff 1 == 0

example :
    endomorphismPresentationMatrix exampleMatrix 0 0 =
      (X : Rat[X]) - C 1 := by
  simp [exampleMatrix]

example :
    endomorphismPresentationMatrix exampleMatrix 0 1 =
      -(C 2 : Rat[X]) := by
  simp [exampleMatrix]

example :
    endomorphismPresentationMatrix exampleMatrix =
      exampleMatrix.charmatrix :=
  endomorphismPresentationMatrix_eq_charmatrix exampleMatrix

example :
    (endomorphismPresentationMatrix exampleMatrix).det =
      exampleMatrix.charpoly :=
  endomorphismPresentationMatrix_det exampleMatrix

private def emptyMatrix : Matrix (Fin 0) (Fin 0) Rat := 0

example :
    endomorphismPresentationMatrix emptyMatrix = emptyMatrix.charmatrix :=
  endomorphismPresentationMatrix_eq_charmatrix emptyMatrix

example :
    (endomorphismPresentationMatrix emptyMatrix).det = 1 := by
  rw [endomorphismPresentationMatrix_det]
  simp

end NormalForms.Tests.RationalCanonical.Presentation
