/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.RationalCanonical.MinimalPolynomial
import all NormalForms.Matrix.Smith.Uniqueness

/-!
# Similarity and Basis Independence

`SimilarityCertificate` records a change-of-basis matrix, its explicit
two-sided inverse, and the exact conjugation equation.  Mapping that
certificate through polynomial constants gives a two-sided equivalence between
the characteristic presentations `XI - A` and `XI - B`.

Composing this equivalence with both strong Smith results and invoking
canonical uniqueness proves equality of every executable invariant factor.
Consequently the companion-block rational canonical matrix is invariant under
similarity and under a change of basis for an abstract endomorphism.
-/

namespace NormalForms.RationalCanonical

open Polynomial
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Smith

public structure SimilarityCertificate
    {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Rat) where
  change : Matrix (Fin n) (Fin n) Rat
  changeCertificate : MatrixInverseCertificate change
  equation :
    changeCertificate.inverse * A * change = B

private noncomputable def constantPolynomialCertificate
    {n : Nat}
    {P : Matrix (Fin n) (Fin n) Rat}
    (certificate : MatrixInverseCertificate P) :
    MatrixInverseCertificate
      ((Polynomial.C : Rat →+* Rat[X]).mapMatrix P) where
  inverse :=
    (Polynomial.C : Rat →+* Rat[X]).mapMatrix
      certificate.inverse
  left_inv := by
    rw [← map_mul, certificate.left_inv, map_one]
  right_inv := by
    rw [← map_mul, certificate.right_inv, map_one]

private theorem charmatrix_eq_of_similarity
    {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Rat}
    (similarity : SimilarityCertificate A B) :
    (Polynomial.C : Rat →+* Rat[X]).mapMatrix
          similarity.changeCertificate.inverse *
        A.charmatrix *
        (Polynomial.C : Rat →+* Rat[X]).mapMatrix
          similarity.change =
      B.charmatrix := by
  let Q :=
    (Polynomial.C : Rat →+* Rat[X]).mapMatrix
      similarity.changeCertificate.inverse
  let P :=
    (Polynomial.C : Rat →+* Rat[X]).mapMatrix
      similarity.change
  have hQP : Q * P = 1 := by
    dsimp only [Q, P]
    rw [← map_mul, similarity.changeCertificate.left_inv,
      map_one]
  have hConjugate :
      Q *
            (Polynomial.C : Rat →+* Rat[X]).mapMatrix A *
            P =
        (Polynomial.C : Rat →+* Rat[X]).mapMatrix B := by
    have h := congrArg
      (Polynomial.C : Rat →+* Rat[X]).mapMatrix
      similarity.equation
    simpa only [map_mul] using h
  have hScalarComm :
      Matrix.scalar (Fin n) (X : Rat[X]) * P =
        P * Matrix.scalar (Fin n) (X : Rat[X]) :=
    Matrix.scalar_comm (X : Rat[X]) (fun r => mul_comm _ r) P
  have hScalar :
      Q * Matrix.scalar (Fin n) (X : Rat[X]) * P =
        Matrix.scalar (Fin n) (X : Rat[X]) := by
    calc
      Q * Matrix.scalar (Fin n) (X : Rat[X]) * P =
          Q * (Matrix.scalar (Fin n) (X : Rat[X]) * P) := by
            rw [Matrix.mul_assoc]
      _ = Q * (P * Matrix.scalar (Fin n) (X : Rat[X])) := by
            rw [hScalarComm]
      _ = (Q * P) * Matrix.scalar (Fin n) (X : Rat[X]) := by
            rw [Matrix.mul_assoc]
      _ = Matrix.scalar (Fin n) (X : Rat[X]) := by
            rw [hQP, one_mul]
  change
    Q *
          (Matrix.scalar (Fin n) (X : Rat[X]) -
            (Polynomial.C : Rat →+* Rat[X]).mapMatrix A) *
          P =
      Matrix.scalar (Fin n) (X : Rat[X]) -
        (Polynomial.C : Rat →+* Rat[X]).mapMatrix B
  rw [mul_sub, sub_mul, hScalar, hConjugate]

private noncomputable def presentationSimilarityCertificate
    {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Rat}
    (similarity : SimilarityCertificate A B) :
    TwoSidedCertificate
      (endomorphismPresentationMatrix A) where
  U :=
    (Polynomial.C : Rat →+* Rat[X]).mapMatrix
      similarity.changeCertificate.inverse
  U_cert :=
    constantPolynomialCertificate
      similarity.changeCertificate.symm
  result := endomorphismPresentationMatrix B
  V :=
    (Polynomial.C : Rat →+* Rat[X]).mapMatrix
      similarity.change
  V_cert :=
    constantPolynomialCertificate
      similarity.changeCertificate
  equation := by
    rw [endomorphismPresentationMatrix_eq_charmatrix,
      endomorphismPresentationMatrix_eq_charmatrix]
    exact charmatrix_eq_of_similarity similarity

private noncomputable def smithSimilarityCertificate
    {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Rat}
    (similarity : SimilarityCertificate A B) :
    TwoSidedCertificate (endomorphismSmithResult A).S :=
  let source := endomorphismSmithResult A
  let target := endomorphismSmithResult B
  let middle := presentationSimilarityCertificate similarity
  { U :=
      target.U * middle.U * source.U_cert.inverse
    U_cert :=
      (target.U_cert.mul middle.U_cert).mul
        source.U_cert.symm
    result := target.S
    V :=
      source.V_cert.inverse * middle.V * target.V
    V_cert :=
      (source.V_cert.symm.mul middle.V_cert).mul
        target.V_cert
    equation := by
      have hRecover :
          source.U_cert.inverse * source.S *
              source.V_cert.inverse =
            endomorphismPresentationMatrix A := by
        calc
          source.U_cert.inverse * source.S *
                source.V_cert.inverse =
              source.U_cert.inverse *
                  (source.U *
                    endomorphismPresentationMatrix A *
                    source.V) *
                source.V_cert.inverse := by
                  rw [source.equation]
          _ =
              (source.U_cert.inverse * source.U) *
                endomorphismPresentationMatrix A *
                (source.V * source.V_cert.inverse) := by
                  simp only [Matrix.mul_assoc]
          _ = endomorphismPresentationMatrix A := by
                rw [source.U_cert.left_inv,
                  source.V_cert.right_inv]
                simp
      calc
        (target.U * middle.U * source.U_cert.inverse) *
              source.S *
            (source.V_cert.inverse * middle.V * target.V) =
          target.U * middle.U *
              (source.U_cert.inverse * source.S *
                source.V_cert.inverse) *
            middle.V * target.V := by
              simp only [Matrix.mul_assoc]
        _ =
          target.U * middle.U *
              endomorphismPresentationMatrix A *
            middle.V * target.V := by
              rw [hRecover]
        _ =
          target.U *
              (middle.U *
                endomorphismPresentationMatrix A *
                middle.V) *
            target.V := by
              simp only [Matrix.mul_assoc]
        _ =
          target.U * endomorphismPresentationMatrix B *
            target.V := by
              rw [middle.equation]
              rfl
        _ = target.S := target.equation }

private theorem smithResult_eq_of_similarity
    {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Rat}
    (similarity : SimilarityCertificate A B) :
    (endomorphismSmithResult A).S =
      (endomorphismSmithResult B).S := by
  let certificate := smithSimilarityCertificate similarity
  exact
    Internal.isSmithNormalFormFin_unique_of_two_sided_equiv
      (endomorphismSmithResult A).isSmith
      (endomorphismSmithResult B).isSmith
      certificate.U_cert.unimodular
      certificate.V_cert.unimodular
      certificate.equation

public theorem endomorphismInvariantFactor_eq_of_similarity
    {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Rat}
    (similarity : SimilarityCertificate A B)
    (i : Fin n) :
    endomorphismInvariantFactor A i =
      endomorphismInvariantFactor B i := by
  rw [← endomorphismSmithResult_diagonal A i,
    ← endomorphismSmithResult_diagonal B i]
  exact congrFun (congrFun
    (smithResult_eq_of_similarity similarity) i) i

public theorem endomorphismInvariantFactors_eq_of_similarity
    {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Rat}
    (similarity : SimilarityCertificate A B) :
    endomorphismInvariantFactors A =
      endomorphismInvariantFactors B := by
  rw [endomorphismInvariantFactors_eq_diagonal,
    endomorphismInvariantFactors_eq_diagonal]
  congr 1
  funext i
  exact endomorphismInvariantFactor_eq_of_similarity
    similarity i

public theorem rationalCanonicalBlockMatrix_eq_of_similarity
    {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Rat}
    (similarity : SimilarityCertificate A B) :
    rationalCanonicalBlockMatrix A =
      rationalCanonicalBlockMatrix B :=
  rationalCanonicalBlockMatrix_eq_of_factor_eq <|
    funext fun i =>
      endomorphismInvariantFactor_eq_of_similarity
        similarity i

namespace SimilarityCertificate

public def refl
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) Rat) :
    SimilarityCertificate A A where
  change := 1
  changeCertificate := MatrixInverseCertificate.one
  equation := by
    change (1 : Matrix (Fin n) (Fin n) Rat) * A * 1 = A
    simp

public def symm
    {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Rat}
    (similarity : SimilarityCertificate A B) :
    SimilarityCertificate B A where
  change := similarity.changeCertificate.inverse
  changeCertificate := similarity.changeCertificate.symm
  equation := by
    calc
      similarity.change * B *
            similarity.changeCertificate.inverse =
          similarity.change *
              (similarity.changeCertificate.inverse * A *
                similarity.change) *
            similarity.changeCertificate.inverse := by
              rw [similarity.equation]
      _ =
          (similarity.change *
              similarity.changeCertificate.inverse) *
            A *
            (similarity.change *
              similarity.changeCertificate.inverse) := by
              simp only [Matrix.mul_assoc]
      _ = A := by
            rw [similarity.changeCertificate.right_inv]
            simp

public def trans
    {n : Nat}
    {A B C : Matrix (Fin n) (Fin n) Rat}
    (first : SimilarityCertificate A B)
    (second : SimilarityCertificate B C) :
    SimilarityCertificate A C where
  change := first.change * second.change
  changeCertificate :=
    first.changeCertificate.mul second.changeCertificate
  equation := by
    calc
      (second.changeCertificate.inverse *
            first.changeCertificate.inverse) *
          A * (first.change * second.change) =
        second.changeCertificate.inverse *
          (first.changeCertificate.inverse * A *
            first.change) *
          second.change := by
            simp only [Matrix.mul_assoc]
      _ =
        second.changeCertificate.inverse * B *
          second.change := by
            rw [first.equation]
      _ = C := second.equation

end SimilarityCertificate

public def RationalCanonicalResult.toSimilarityCertificate
    {n : Nat}
    {A : Matrix (Fin n) (Fin n) Rat}
    (result : RationalCanonicalResult A) :
    SimilarityCertificate A
      (rationalCanonicalBlockMatrix A) where
  change := result.change
  changeCertificate := result.changeCertificate
  equation := result.equation

public noncomputable def basisSimilarityCertificate
    {n : Nat}
    {M : Type _}
    [AddCommGroup M] [Module Rat M]
    (source target : Module.Basis (Fin n) Rat M)
    (f : M →ₗ[Rat] M) :
    SimilarityCertificate
      (LinearMap.toMatrix source source f)
      (LinearMap.toMatrix target target f) where
  change := source.toMatrix target
  changeCertificate :=
    { inverse := target.toMatrix source
      left_inv := by
        simp [Module.Basis.toMatrix_mul_toMatrix]
      right_inv := by
        simp [Module.Basis.toMatrix_mul_toMatrix] }
  equation := by
    exact
      basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
        target source target source f

public theorem endomorphismInvariantFactors_toMatrix_eq
    {n : Nat}
    {M : Type _}
    [AddCommGroup M] [Module Rat M]
    (source target : Module.Basis (Fin n) Rat M)
    (f : M →ₗ[Rat] M) :
    endomorphismInvariantFactors
        (LinearMap.toMatrix source source f) =
      endomorphismInvariantFactors
        (LinearMap.toMatrix target target f) :=
  endomorphismInvariantFactors_eq_of_similarity
    (basisSimilarityCertificate source target f)

public theorem rationalCanonicalBlockMatrix_toMatrix_eq
    {n : Nat}
    {M : Type _}
    [AddCommGroup M] [Module Rat M]
    (source target : Module.Basis (Fin n) Rat M)
    (f : M →ₗ[Rat] M) :
    rationalCanonicalBlockMatrix
        (LinearMap.toMatrix source source f) =
      rationalCanonicalBlockMatrix
        (LinearMap.toMatrix target target f) :=
  rationalCanonicalBlockMatrix_eq_of_similarity
    (basisSimilarityCertificate source target f)

end NormalForms.RationalCanonical
