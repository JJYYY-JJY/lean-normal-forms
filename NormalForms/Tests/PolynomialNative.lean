/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Matrix.PolynomialRat
import NormalForms.Euclidean.PolynomialRat

/-!
# Native rational-polynomial execution smoke test

This executable forces genuine native evaluation of both certified normal-form
kernels and checks the resulting transformation equations and inverse
certificates.
-/

namespace NormalForms.Tests.PolynomialNative

open NormalForms.PolynomialRatRuntime
open scoped Matrix

private def pivotInput : Matrix (Fin 2) (Fin 2) RuntimePolynomial :=
  !![add X one, X;
     one, zero]

private def pivotExpected : Matrix (Fin 2) (Fin 2) RuntimePolynomial :=
  !![one, zero;
     zero, X]

private def zeroMatrix : Matrix (Fin 2) (Fin 2) RuntimePolynomial :=
  !![zero, zero;
     zero, zero]

private def constantInput : Matrix (Fin 2) (Fin 2) RuntimePolynomial :=
  !![C 2, C 4;
     C 6, C 8]

private def identity : Matrix (Fin 2) (Fin 2) RuntimePolynomial :=
  !![one, zero;
     zero, one]

private def rankDeficientInput : Matrix (Fin 2) (Fin 2) RuntimePolynomial :=
  !![X, mul X X;
     zero, zero]

private def rankDeficientHNF : Matrix (Fin 2) (Fin 2) RuntimePolynomial :=
  rankDeficientInput

private def rankDeficientSNF : Matrix (Fin 2) (Fin 2) RuntimePolynomial :=
  !![X, zero;
     zero, zero]

private def zeroRows : Matrix (Fin 0) (Fin 2) RuntimePolynomial :=
  fun i => Fin.elim0 i

private def assertCheck (name : String) (check : Bool) : IO Unit := do
  if check then
    IO.println s!"{name} passed"
  else
    throw <| IO.userError s!"{name} failed"

def run : IO Unit := do
  assertCheck "pivot-improvement certificate check" <|
    certificateChecksFin pivotInput pivotExpected pivotExpected
  assertCheck "zero-matrix certificate check" <|
    certificateChecksFin zeroMatrix zeroMatrix zeroMatrix
  assertCheck "constant full-rank certificate check" <|
    certificateChecksFin constantInput identity identity
  assertCheck "rank-deficient certificate check" <|
    certificateChecksFin rankDeficientInput rankDeficientHNF rankDeficientSNF
  assertCheck "zero-row certificate check" <|
    certificateChecksFin zeroRows zeroRows zeroRows

end NormalForms.Tests.PolynomialNative

public def main : IO Unit :=
  NormalForms.Tests.PolynomialNative.run
