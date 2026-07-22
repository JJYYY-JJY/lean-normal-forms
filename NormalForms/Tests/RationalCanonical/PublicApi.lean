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
# Rational Canonical Public API Freeze

These checks pin the independent v1.1 facade without adding it to the frozen
core `NormalForms` facade.
-/

namespace NormalForms.Tests.RationalCanonical.PublicApi

open Polynomial
open NormalForms.Matrix.Certificates
open NormalForms.RationalCanonical

#check endomorphismPresentationMatrix
#check endomorphismPresentationMatrix_eq_charmatrix
#check endomorphismSmithResult
#check endomorphismInvariantFactor
#check endomorphismInvariantFactors
#check endomorphismInvariantFactors_product
#check largestInvariantFactor?
#check endomorphismCyclicDecomposition
#check companionMatrix
#check companionMatrix_charpoly
#check rationalCanonicalBasis
#check rationalCanonicalChangeCertificate
#check rationalCanonicalBlockMatrix
#check RationalCanonicalResult
#check rationalCanonicalResult
#check lastInvariantFactor_eq_minpoly
#check largestInvariantFactor?_eq_minpoly
#check SimilarityCertificate
#check endomorphismInvariantFactors_eq_of_similarity
#check rationalCanonicalBlockMatrix_eq_of_similarity
#check endomorphismInvariantFactors_toMatrix_eq
#check rationalCanonicalBlockMatrix_toMatrix_eq

example {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    Matrix (Fin n) (Fin n) Rat[X] :=
  endomorphismPresentationMatrix A

example {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    List Rat[X] :=
  endomorphismInvariantFactors A

example {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    Option Rat[X] :=
  largestInvariantFactor? A

example {n : Nat}
    {A : Matrix (Fin n) (Fin n) Rat}
    (result : RationalCanonicalResult A) :
    MatrixInverseCertificate result.change :=
  result.changeCertificate

example {n : Nat}
    {A : Matrix (Fin n) (Fin n) Rat}
    (result : RationalCanonicalResult A) :
    result.changeCertificate.inverse * A * result.change =
      rationalCanonicalBlockMatrix A :=
  result.equation

example {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Rat}
    (similarity : SimilarityCertificate A B) :
    endomorphismInvariantFactors A =
      endomorphismInvariantFactors B :=
  endomorphismInvariantFactors_eq_of_similarity similarity

end NormalForms.Tests.RationalCanonical.PublicApi
