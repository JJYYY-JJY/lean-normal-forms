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
# Executable Rational Canonical Invariant Tests

The corpus checks the runtime-to-standard polynomial bridge, exact invariant
factor coefficients, retention of a unit factor, and the empty-dimensional
largest-factor convention.
-/

namespace NormalForms.Tests.RationalCanonical.Invariants

open NormalForms.RationalCanonical

private def scalarTwo : Matrix (Fin 1) (Fin 1) Rat :=
  !![2]

private def diagonalOneTwo : Matrix (Fin 2) (Fin 2) Rat :=
  !![1, 0;
     0, 2]

private def scalarTwoChecks : Bool :=
  match endomorphismInvariantFactors scalarTwo with
  | [factor] =>
      factor.coeff 0 == -2 &&
        factor.coeff 1 == 1 &&
        factor.natDegree == 1
  | _ => false

private def diagonalOneTwoChecks : Bool :=
  match endomorphismInvariantFactors diagonalOneTwo with
  | [unitFactor, quadratic] =>
      unitFactor.coeff 0 == 1 &&
        unitFactor.natDegree == 0 &&
        quadratic.coeff 0 == 2 &&
        quadratic.coeff 1 == -3 &&
        quadratic.coeff 2 == 1 &&
        quadratic.natDegree == 2
  | _ => false

#guard scalarTwoChecks
#guard diagonalOneTwoChecks

example :
    (endomorphismInvariantFactors scalarTwo).length = 1 :=
  endomorphismInvariantFactors_length scalarTwo

example :
    (endomorphismInvariantFactors diagonalOneTwo).length = 2 :=
  endomorphismInvariantFactors_length diagonalOneTwo

example :
    (endomorphismInvariantFactors scalarTwo).prod =
      scalarTwo.charpoly :=
  endomorphismInvariantFactors_product scalarTwo

example :
    (endomorphismInvariantFactors diagonalOneTwo).prod =
      diagonalOneTwo.charpoly :=
  endomorphismInvariantFactors_product diagonalOneTwo

private def emptyMatrix : Matrix (Fin 0) (Fin 0) Rat := 0

#guard largestInvariantFactor? emptyMatrix |>.isNone

example : largestInvariantFactor? emptyMatrix = none :=
  largestInvariantFactor?_empty emptyMatrix

example :
    (endomorphismPresentationMatrixRuntime diagonalOneTwo).map
        runtimePolynomialEquiv =
      diagonalOneTwo.charmatrix :=
  endomorphismPresentationMatrixRuntime_eq_charmatrix
    diagonalOneTwo

end NormalForms.Tests.RationalCanonical.Invariants
