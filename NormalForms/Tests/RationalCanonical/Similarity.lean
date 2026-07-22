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
# Rational Similarity Tests

A nontrivial coordinate swap checks the explicit similarity certificate,
factor invariance, and canonical-block invariance.  A second regression states
basis independence for the standard and certified cyclic bases.
-/

namespace NormalForms.Tests.RationalCanonical.Similarity

open NormalForms.Matrix.Certificates
open NormalForms.RationalCanonical

private def diagonalOneTwo : Matrix (Fin 2) (Fin 2) Rat :=
  !![1, 0;
     0, 2]

private def diagonalTwoOne : Matrix (Fin 2) (Fin 2) Rat :=
  !![2, 0;
     0, 1]

private def swap : Matrix (Fin 2) (Fin 2) Rat :=
  !![0, 1;
     1, 0]

private theorem swap_mul_swap : swap * swap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private def swapCertificate :
    MatrixInverseCertificate swap where
  inverse := swap
  left_inv := swap_mul_swap
  right_inv := swap_mul_swap

private def coordinateSwap :
    SimilarityCertificate diagonalOneTwo diagonalTwoOne where
  change := swap
  changeCertificate := swapCertificate
  equation := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [swapCertificate, swap, diagonalOneTwo, diagonalTwoOne,
        Matrix.mul_apply, Fin.sum_univ_two]

example :
    endomorphismInvariantFactors diagonalOneTwo =
      endomorphismInvariantFactors diagonalTwoOne :=
  endomorphismInvariantFactors_eq_of_similarity coordinateSwap

example (i : Fin 2) :
    endomorphismInvariantFactor diagonalOneTwo i =
      endomorphismInvariantFactor diagonalTwoOne i :=
  endomorphismInvariantFactor_eq_of_similarity coordinateSwap i

example :
    rationalCanonicalBlockMatrix diagonalOneTwo =
      rationalCanonicalBlockMatrix diagonalTwoOne :=
  rationalCanonicalBlockMatrix_eq_of_similarity coordinateSwap

example :
    rationalCanonicalBlockMatrix
          (LinearMap.toMatrix
            (Pi.basisFun Rat (Fin 2))
            (Pi.basisFun Rat (Fin 2))
            diagonalOneTwo.toLin') =
        rationalCanonicalBlockMatrix
          (LinearMap.toMatrix
            (rationalCanonicalBasis diagonalOneTwo)
            (rationalCanonicalBasis diagonalOneTwo)
            diagonalOneTwo.toLin') :=
  rationalCanonicalBlockMatrix_toMatrix_eq
    (Pi.basisFun Rat (Fin 2))
    (rationalCanonicalBasis diagonalOneTwo)
    diagonalOneTwo.toLin'

example :
    ((rationalCanonicalResult diagonalOneTwo).toSimilarityCertificate).changeCertificate.inverse *
        diagonalOneTwo *
        ((rationalCanonicalResult diagonalOneTwo).toSimilarityCertificate).change =
      rationalCanonicalBlockMatrix diagonalOneTwo :=
  ((rationalCanonicalResult diagonalOneTwo).toSimilarityCertificate).equation

end NormalForms.Tests.RationalCanonical.Similarity
