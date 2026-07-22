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
# Rational Minimal-Polynomial Tests

The executable final Smith factor is checked against mathlib's minimal
polynomial for scalar and noncyclic-looking diagonal inputs.  Dimension zero
retains the separate `none` convention.
-/

namespace NormalForms.Tests.RationalCanonical.MinimalPolynomial

open NormalForms.RationalCanonical

private def scalarTwo : Matrix (Fin 1) (Fin 1) Rat :=
  !![2]

private def diagonalOneTwo : Matrix (Fin 2) (Fin 2) Rat :=
  !![1, 0;
     0, 2]

private def emptyMatrix : Matrix (Fin 0) (Fin 0) Rat :=
  0

example :
    endomorphismInvariantFactor scalarTwo (Fin.last 0) =
      minpoly Rat scalarTwo :=
  lastInvariantFactor_eq_minpoly scalarTwo

example :
    largestInvariantFactor? scalarTwo =
      some (minpoly Rat scalarTwo) :=
  largestInvariantFactor?_eq_minpoly scalarTwo (by omega)

example :
    largestInvariantFactor? diagonalOneTwo =
      some (minpoly Rat diagonalOneTwo) :=
  largestInvariantFactor?_eq_minpoly diagonalOneTwo (by omega)

example :
    largestInvariantFactor? emptyMatrix = none :=
  largestInvariantFactor?_empty emptyMatrix

end NormalForms.Tests.RationalCanonical.MinimalPolynomial
