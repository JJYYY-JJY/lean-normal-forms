/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Euclidean.Int
import all NormalForms.Euclidean.PolynomialRat
import all NormalForms.Matrix.Hermite.Algorithm
import all NormalForms.Matrix.Smith.Algorithm
meta import all NormalForms.Euclidean.Int
meta import all NormalForms.Euclidean.PolynomialRat
meta import all NormalForms.Matrix.Hermite.Algorithm
meta import all NormalForms.Matrix.Smith.Algorithm

set_option linter.privateModule false
set_option linter.hashCommand false

/-!
# Constructive execution regressions

These guards cover the lightweight deterministic execution corpus.  The
larger rational-polynomial matrix case lives in the dedicated native
`normalforms-polynomial-smoke` target.
-/

namespace NormalForms.Tests.Execution

open scoped Matrix
open NormalForms
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith

private def intMatrixEqb {m n : Nat}
    (A B : Matrix (Fin m) (Fin n) Int) : Bool :=
  (List.finRange m).all fun i =>
    (List.finRange n).all fun j => decide (A i j = B i j)

private def intCertificateChecks {m n : Nat}
    (A expectedH expectedS : Matrix (Fin m) (Fin n) Int) : Bool :=
  let h := hermiteNormalFormFin A
  let s := smithNormalFormFin A
  intMatrixEqb h.H expectedH &&
    intMatrixEqb (h.U * A) h.H &&
    intMatrixEqb (h.U_cert.inverse * h.U) 1 &&
    intMatrixEqb (h.U * h.U_cert.inverse) 1 &&
    intMatrixEqb s.S expectedS &&
    intMatrixEqb (s.U * A * s.V) s.S &&
    intMatrixEqb (s.U_cert.inverse * s.U) 1 &&
    intMatrixEqb (s.U * s.U_cert.inverse) 1 &&
    intMatrixEqb (s.V_cert.inverse * s.V) 1 &&
    intMatrixEqb (s.V * s.V_cert.inverse) 1

private def pivotImprovementInput : Matrix (Fin 2) (Fin 3) Int :=
  !![6, 15, 9;
     4, 10, 6]

private def pivotImprovementHNF : Matrix (Fin 2) (Fin 3) Int :=
  !![2, 5, 3;
     0, 0, 0]

private def pivotImprovementSNF : Matrix (Fin 2) (Fin 3) Int :=
  !![1, 0, 0;
     0, 0, 0]

#guard intCertificateChecks pivotImprovementInput
  pivotImprovementHNF pivotImprovementSNF

private def rectangularInput : Matrix (Fin 2) (Fin 3) Int :=
  !![2, 0, 0;
     0, 6, 0]

#guard intCertificateChecks rectangularInput rectangularInput rectangularInput

private def negativeInput : Matrix (Fin 1) (Fin 1) Int :=
  !![-7]

private def normalizedNegative : Matrix (Fin 1) (Fin 1) Int :=
  !![7]

#guard intCertificateChecks negativeInput normalizedNegative normalizedNegative

private def unitInput : Matrix (Fin 1) (Fin 1) Int :=
  !![-1]

private def normalizedUnit : Matrix (Fin 1) (Fin 1) Int :=
  !![1]

#guard intCertificateChecks unitInput normalizedUnit normalizedUnit

private def zeroMatrix : Matrix (Fin 2) (Fin 3) Int := 0
private def zeroRows : Matrix (Fin 0) (Fin 3) Int := 0
private def zeroColumns : Matrix (Fin 2) (Fin 0) Int := 0

#guard intCertificateChecks zeroMatrix zeroMatrix zeroMatrix
#guard intCertificateChecks zeroRows zeroRows zeroRows
#guard intCertificateChecks zeroColumns zeroColumns zeroColumns

#guard ComputableEuclideanOps.eqb (-3 : Int) (-3)
#guard !ComputableEuclideanOps.eqb (-3 : Int) 3
#guard ComputableEuclideanOps.divMod (-7 : Int) 3 == (-3, 2)
#guard ComputableEuclideanOps.normalize (-7 : Int) == 7
#guard ComputableEuclideanOps.normUnit (-7 : Int) == -1
#guard (ComputableEuclideanOps.xgcd (6 : Int) 15).gcd == 3
#guard ComputableEuclideanOps.measure (-7 : Int) == 7
#guard NormalForms.ComputableEuclideanOps.dvdB (3 : Int) 15
#guard !(NormalForms.ComputableEuclideanOps.dvdB (4 : Int) 15)

namespace Polynomial

open NormalForms.PolynomialRatRuntime

private def quadratic : RuntimePolynomial :=
  sub (mul X X) one

private def linear : RuntimePolynomial :=
  sub X one

private def polynomialPrimitiveChecks : Bool :=
  let dm := divMod quadratic linear
  let dmZero := divMod quadratic zero
  let xg := runtimeAlgebra.operations.xgcd quadratic linear
  let xgZero := runtimeAlgebra.operations.xgcd zero zero
  let xgLeftZero := runtimeAlgebra.operations.xgcd zero linear
  let xgConstants :=
    runtimeAlgebra.operations.xgcd (C (-6)) (C 9)
  let eqb := runtimeAlgebra.operations.eqb
  isZeroB zero &&
    !isZeroB one &&
    eqb dm.1 (add X one) &&
    eqb dm.2 zero &&
    eqb dmZero.1 zero &&
    eqb dmZero.2 quadratic &&
    eqb (PolynomialRatRuntime.normalize zero) zero &&
    eqb (PolynomialRatRuntime.normalize (C (-2))) one &&
    eqb
      (PolynomialRatRuntime.normalize (mul (C (-2)) (add X one)))
      (add X one) &&
    eqb xg.gcd linear &&
    eqb
      (add (mul quadratic xg.leftCoeff) (mul linear xg.rightCoeff))
      xg.gcd &&
    eqb xgZero.gcd zero &&
    eqb xgLeftZero.gcd linear &&
    eqb xgConstants.gcd one &&
    eqb
      (add
        (mul (C (-6)) xgConstants.leftCoeff)
        (mul (C 9) xgConstants.rightCoeff))
      one &&
    runtimeAlgebra.operations.measure zero == 0 &&
    runtimeAlgebra.operations.measure (C 4) == 1 &&
    runtimeAlgebra.operations.measure X == 2

#guard polynomialPrimitiveChecks

end Polynomial

end NormalForms.Tests.Execution
