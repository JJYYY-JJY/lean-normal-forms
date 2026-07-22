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
# Rational Canonical Basis Tests

Regression coverage for factor monicity, total cyclic dimension, both inverse
identities, and the explicit similarity equation.
-/

namespace NormalForms.Tests.RationalCanonical.Basis

open NormalForms.RationalCanonical

private def diagonalOneTwo : Matrix (Fin 2) (Fin 2) Rat :=
  !![1, 0;
     0, 2]

private def scalarTwo : Matrix (Fin 1) (Fin 1) Rat :=
  !![2]

private def emptyMatrix : Matrix (Fin 0) (Fin 0) Rat :=
  0

example (i : Fin 2) :
    endomorphismInvariantFactor diagonalOneTwo i ≠ 0 :=
  endomorphismInvariantFactor_ne_zero diagonalOneTwo i

example (i : Fin 2) :
    (endomorphismInvariantFactor diagonalOneTwo i).Monic :=
  endomorphismInvariantFactor_monic diagonalOneTwo i

example :
    ∑ i : Fin 2,
        (endomorphismInvariantFactor diagonalOneTwo i).natDegree =
      2 :=
  endomorphismInvariantFactor_degree_sum diagonalOneTwo

example :
    rationalCanonicalChangeInverse diagonalOneTwo *
        rationalCanonicalChange diagonalOneTwo =
      1 :=
  rationalCanonicalChangeInverse_mul diagonalOneTwo

example :
    rationalCanonicalChange diagonalOneTwo *
        rationalCanonicalChangeInverse diagonalOneTwo =
      1 :=
  rationalCanonicalChange_mul_inverse diagonalOneTwo

example :
    rationalCanonicalChangeInverse scalarTwo * scalarTwo *
        rationalCanonicalChange scalarTwo =
      rationalCanonicalMatrix scalarTwo :=
  rationalCanonical_similarity scalarTwo

example :
    rationalCanonicalChangeInverse diagonalOneTwo *
          diagonalOneTwo *
          rationalCanonicalChange diagonalOneTwo =
        rationalCanonicalMatrix diagonalOneTwo :=
  rationalCanonical_similarity diagonalOneTwo

example :
    ∑ i : Fin 0,
        (endomorphismInvariantFactor emptyMatrix i).natDegree =
      0 :=
  endomorphismInvariantFactor_degree_sum emptyMatrix

end NormalForms.Tests.RationalCanonical.Basis
