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
# Rational Canonical Result Tests

Regression coverage for the companion-block identification and the strong
result's exact similarity and inverse obligations, including dimension zero.
-/

namespace NormalForms.Tests.RationalCanonical.Result

open NormalForms.RationalCanonical

private def diagonalOneTwo : Matrix (Fin 2) (Fin 2) Rat :=
  !![1, 0;
     0, 2]

private def scalarTwo : Matrix (Fin 1) (Fin 1) Rat :=
  !![2]

private def emptyMatrix : Matrix (Fin 0) (Fin 0) Rat :=
  0

example :
    rationalCanonicalMatrix diagonalOneTwo =
      rationalCanonicalBlockMatrix diagonalOneTwo :=
  rationalCanonicalMatrix_eq_blocks diagonalOneTwo

example :
    (rationalCanonicalResult scalarTwo).changeCertificate.inverse *
          scalarTwo *
          (rationalCanonicalResult scalarTwo).change =
        rationalCanonicalBlockMatrix scalarTwo :=
  (rationalCanonicalResult scalarTwo).equation

example :
    (rationalCanonicalResult diagonalOneTwo).changeCertificate.inverse *
          (rationalCanonicalResult diagonalOneTwo).change =
        1 :=
  (rationalCanonicalResult diagonalOneTwo).changeCertificate.left_inv

example :
    (rationalCanonicalResult diagonalOneTwo).change *
          (rationalCanonicalResult diagonalOneTwo).changeCertificate.inverse =
        1 :=
  (rationalCanonicalResult diagonalOneTwo).changeCertificate.right_inv

example :
    (rationalCanonicalResult emptyMatrix).changeCertificate.inverse *
          emptyMatrix *
          (rationalCanonicalResult emptyMatrix).change =
        rationalCanonicalBlockMatrix emptyMatrix :=
  (rationalCanonicalResult emptyMatrix).equation

end NormalForms.Tests.RationalCanonical.Result
