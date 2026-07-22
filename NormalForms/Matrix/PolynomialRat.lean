/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Basic
public import NormalForms.Euclidean.PolynomialRat
import all NormalForms.Matrix.Hermite.Algorithm
import all NormalForms.Matrix.Smith.Algorithm

/-!
# Executable rational-polynomial normal forms

This module instantiates the generic certified kernels with the coherent
rational-polynomial runtime dictionary.  The public functions below are
computational projections of the strong generic results; all certificate and
normal-form proofs are constructed before the projections are taken.
-/

namespace NormalForms.PolynomialRatRuntime

open scoped Matrix

private theorem canonicalModOf (rt : RuntimeAlgebra) :
    @NormalForms.Matrix.Hermite.CanonicalMod (RuntimePolynomial) rt.euclidean := by
  exact @NormalForms.Matrix.Hermite.CanonicalMod.mk (RuntimePolynomial) rt.euclidean
    rt.canonicalMod.mod_mod rt.canonicalMod.reduced_eq_of_dvd_sub

private def hnfResult {m n : Nat} (rt : RuntimeAlgebra)
    (A : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    @NormalForms.Matrix.Hermite.HNFResultFin m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A :=
  @NormalForms.Matrix.Hermite.hermiteNormalFormFin m n (RuntimePolynomial)
    rt.euclidean rt.normalization rt.operations rt.decidableEq
    (canonicalModOf rt) A

private def snfResult {m n : Nat} (rt : RuntimeAlgebra)
    (A : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    @NormalForms.Matrix.Smith.SNFResultFin m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A :=
  @NormalForms.Matrix.Smith.smithNormalFormFin m n (RuntimePolynomial)
    rt.euclidean rt.normalization rt.operations rt.decidableEq
    (canonicalModOf rt) A

/-- Boolean polynomial equality from the constructive runtime dictionary. -/
public def eqb (p q : RuntimePolynomial) : Bool :=
  runtimeAlgebra.operations.eqb p q

/-- Boolean matrix equality from the constructive runtime dictionary. -/
public def matrixEqb {m n : Nat}
    (A B : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) : Bool :=
  (List.finRange m).all fun i =>
    (List.finRange n).all fun j => eqb (A i j) (B i j)

/-- Executable matrix multiplication using the runtime polynomial ring. -/
public def matrixMul {l m n : Nat}
    (A : _root_.Matrix (Fin l) (Fin m) (RuntimePolynomial))
    (B : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    _root_.Matrix (Fin l) (Fin n) (RuntimePolynomial) :=
  let rt := runtimeAlgebra
  fun i k =>
    (List.finRange m).foldl
      (fun acc j =>
        rt.euclidean.toCommRing.add acc
          (rt.euclidean.toCommRing.mul (A i j) (B j k)))
      rt.euclidean.toCommRing.zero

/-- Executable identity matrix using the runtime polynomial constants. -/
public def identityMatrix (n : Nat) :
    _root_.Matrix (Fin n) (Fin n) (RuntimePolynomial) :=
  fun i j => if i = j then one else zero

/-- The executable Hermite matrix over `RuntimePolynomial`. -/
public def hermiteNormalFormFin {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial) :=
  let rt := runtimeAlgebra
  @NormalForms.Matrix.Hermite.HNFResultFin.H m n (RuntimePolynomial)
    rt.euclidean rt.normalization rt.decidableEq A (hnfResult rt A)

/-- The executable left transform accompanying the Hermite matrix. -/
public def hermiteLeftTransformFin {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    _root_.Matrix (Fin m) (Fin m) (RuntimePolynomial) :=
  let rt := runtimeAlgebra
  @NormalForms.Matrix.Hermite.HNFResultFin.U m n (RuntimePolynomial)
    rt.euclidean rt.normalization rt.decidableEq A (hnfResult rt A)

/-- The explicit inverse of the executable Hermite left transform. -/
public def hermiteLeftInverseFin {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    _root_.Matrix (Fin m) (Fin m) (RuntimePolynomial) :=
  let rt := runtimeAlgebra
  let r := hnfResult rt A
  @NormalForms.Matrix.Certificates.MatrixInverseCertificate.inverse
    (Fin m) (RuntimePolynomial) inferInstance inferInstance
    rt.euclidean.toCommRing
    (@NormalForms.Matrix.Hermite.HNFResultFin.U m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A r)
    (@NormalForms.Matrix.Hermite.HNFResultFin.U_cert m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A r)

/-- The executable Smith matrix over `RuntimePolynomial`. -/
public def smithNormalFormFin {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial) :=
  let rt := runtimeAlgebra
  @NormalForms.Matrix.Smith.SNFResultFin.S m n (RuntimePolynomial)
    rt.euclidean rt.normalization rt.decidableEq A (snfResult rt A)

/-- The executable left transform accompanying the Smith matrix. -/
public def smithLeftTransformFin {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    _root_.Matrix (Fin m) (Fin m) (RuntimePolynomial) :=
  let rt := runtimeAlgebra
  @NormalForms.Matrix.Smith.SNFResultFin.U m n (RuntimePolynomial)
    rt.euclidean rt.normalization rt.decidableEq A (snfResult rt A)

/-- The explicit inverse of the executable Smith left transform. -/
public def smithLeftInverseFin {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    _root_.Matrix (Fin m) (Fin m) (RuntimePolynomial) :=
  let rt := runtimeAlgebra
  let r := snfResult rt A
  @NormalForms.Matrix.Certificates.MatrixInverseCertificate.inverse
    (Fin m) (RuntimePolynomial) inferInstance inferInstance
    rt.euclidean.toCommRing
    (@NormalForms.Matrix.Smith.SNFResultFin.U m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A r)
    (@NormalForms.Matrix.Smith.SNFResultFin.U_cert m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A r)

/-- The executable right transform accompanying the Smith matrix. -/
public def smithRightTransformFin {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    _root_.Matrix (Fin n) (Fin n) (RuntimePolynomial) :=
  let rt := runtimeAlgebra
  @NormalForms.Matrix.Smith.SNFResultFin.V m n (RuntimePolynomial)
    rt.euclidean rt.normalization rt.decidableEq A (snfResult rt A)

/-- The explicit inverse of the executable Smith right transform. -/
public def smithRightInverseFin {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) :
    _root_.Matrix (Fin n) (Fin n) (RuntimePolynomial) :=
  let rt := runtimeAlgebra
  let r := snfResult rt A
  @NormalForms.Matrix.Certificates.MatrixInverseCertificate.inverse
    (Fin n) (RuntimePolynomial) inferInstance inferInstance
    rt.euclidean.toCommRing
    (@NormalForms.Matrix.Smith.SNFResultFin.V m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A r)
    (@NormalForms.Matrix.Smith.SNFResultFin.V_cert m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A r)

/--
Execute one Hermite computation and one Smith computation, then check their
expected normal forms, transformation equations, and all four inverse
identities.  This is an executable regression oracle; the returned normal-form
results themselves were already constructed with proof-carrying certificates.
-/
public def certificateChecksFin {m n : Nat}
    (A expectedH expectedS :
      _root_.Matrix (Fin m) (Fin n) (RuntimePolynomial)) : Bool :=
  let rt := runtimeAlgebra
  let h := hnfResult rt A
  let H :=
    @NormalForms.Matrix.Hermite.HNFResultFin.H m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A h
  let hU :=
    @NormalForms.Matrix.Hermite.HNFResultFin.U m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A h
  let hUCert :=
    @NormalForms.Matrix.Hermite.HNFResultFin.U_cert m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A h
  let hUInv :=
    @NormalForms.Matrix.Certificates.MatrixInverseCertificate.inverse
      (Fin m) (RuntimePolynomial) inferInstance inferInstance
      rt.euclidean.toCommRing hU hUCert
  let s := snfResult rt A
  let S :=
    @NormalForms.Matrix.Smith.SNFResultFin.S m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A s
  let sU :=
    @NormalForms.Matrix.Smith.SNFResultFin.U m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A s
  let sUCert :=
    @NormalForms.Matrix.Smith.SNFResultFin.U_cert m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A s
  let sUInv :=
    @NormalForms.Matrix.Certificates.MatrixInverseCertificate.inverse
      (Fin m) (RuntimePolynomial) inferInstance inferInstance
      rt.euclidean.toCommRing sU sUCert
  let sV :=
    @NormalForms.Matrix.Smith.SNFResultFin.V m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A s
  let sVCert :=
    @NormalForms.Matrix.Smith.SNFResultFin.V_cert m n (RuntimePolynomial)
      rt.euclidean rt.normalization rt.decidableEq A s
  let sVInv :=
    @NormalForms.Matrix.Certificates.MatrixInverseCertificate.inverse
      (Fin n) (RuntimePolynomial) inferInstance inferInstance
      rt.euclidean.toCommRing sV sVCert
  matrixEqb H expectedH &&
    matrixEqb (matrixMul hU A) H &&
    matrixEqb (matrixMul hUInv hU) (identityMatrix m) &&
    matrixEqb (matrixMul hU hUInv) (identityMatrix m) &&
    matrixEqb S expectedS &&
    matrixEqb (matrixMul (matrixMul sU A) sV) S &&
    matrixEqb (matrixMul sUInv sU) (identityMatrix m) &&
    matrixEqb (matrixMul sU sUInv) (identityMatrix m) &&
    matrixEqb (matrixMul sVInv sV) (identityMatrix n) &&
    matrixEqb (matrixMul sV sVInv) (identityMatrix n)

end NormalForms.PolynomialRatRuntime
