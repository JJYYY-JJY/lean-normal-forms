/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.RationalCanonical.Runtime
public import NormalForms.Matrix.Smith.Defs
import all NormalForms.Matrix.Smith.Algorithm

/-!
# Strong Polynomial Smith Results

The executable Smith kernel runs with the choice-free rational-polynomial
dictionary.  This module transports the complete strong result to standard
`Rat[X]`, including both explicit inverse certificates, the transformation
equation, and Smith-normal-form semantics.

The transport is an application-layer bridge.  It does not add a second Smith
algorithm and it does not alter the frozen v1 core facade.
-/

namespace NormalForms.RationalCanonical

open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Smith
open NormalForms.PolynomialRatRuntime
open Polynomial

private noncomputable def mapRuntimeInverseCertificate
    {n : Nat}
    (U : _root_.Matrix (Fin n) (Fin n) RuntimePolynomial)
    (certificate :
      @MatrixInverseCertificate (Fin n) RuntimePolynomial
        (constructiveFinFintype n) inferInstance
        runtimeAlgebra.euclidean.toCommRing U) :
    MatrixInverseCertificate (U.map runtimePolynomialEquiv) := by
  let inverse :=
    @MatrixInverseCertificate.inverse (Fin n) RuntimePolynomial
      (constructiveFinFintype n) inferInstance
      runtimeAlgebra.euclidean.toCommRing U certificate
  let hleft :=
    @MatrixInverseCertificate.left_inv (Fin n) RuntimePolynomial
      (constructiveFinFintype n) inferInstance
      runtimeAlgebra.euclidean.toCommRing U certificate
  let hright :=
    @MatrixInverseCertificate.right_inv (Fin n) RuntimePolynomial
      (constructiveFinFintype n) inferInstance
      runtimeAlgebra.euclidean.toCommRing U certificate
  let sourceAddCommMonoid : AddCommMonoid RuntimePolynomial :=
    @Semiring.toAddCommMonoid RuntimePolynomial
      runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring
  letI : AddCommMonoid RuntimePolynomial := sourceAddCommMonoid
  letI : Add RuntimePolynomial := sourceAddCommMonoid.toAdd
  letI : Zero RuntimePolynomial :=
    @MulZeroClass.toZero RuntimePolynomial
      (@instMulZeroClassOfSemiring RuntimePolynomial
        runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring)
  letI : Mul RuntimePolynomial :=
    (@instDistribOfSemiring RuntimePolynomial
      runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toMul
  letI : One RuntimePolynomial :=
    @AddMonoidWithOne.toOne RuntimePolynomial
      (@AddGroupWithOne.toAddMonoidWithOne RuntimePolynomial
        (@Ring.toAddGroupWithOne RuntimePolynomial
          runtimeAlgebra.euclidean.toCommRing.toRing))
  refine
    { inverse := inverse.map runtimePolynomialEquiv
      left_inv := ?_
      right_inv := ?_ }
  · calc
      inverse.map runtimePolynomialEquiv *
            U.map runtimePolynomialEquiv =
          (inverse * U).map runtimePolynomialEquiv :=
        (runtimePolynomialEquiv_certificateMatrixMul inverse U).symm
      _ =
          (1 : _root_.Matrix (Fin n) (Fin n)
            RuntimePolynomial).map runtimePolynomialEquiv :=
        congrArg (fun M => M.map runtimePolynomialEquiv) hleft
      _ = 1 := runtimePolynomialEquiv_certificateMatrixOne
  · calc
      U.map runtimePolynomialEquiv *
            inverse.map runtimePolynomialEquiv =
          (U * inverse).map runtimePolynomialEquiv :=
        (runtimePolynomialEquiv_certificateMatrixMul U inverse).symm
      _ =
          (1 : _root_.Matrix (Fin n) (Fin n)
            RuntimePolynomial).map runtimePolynomialEquiv :=
        congrArg (fun M => M.map runtimePolynomialEquiv) hright
      _ = 1 := runtimePolynomialEquiv_certificateMatrixOne

private theorem mapRuntimeIsSmith
    {m n : Nat}
    (S : _root_.Matrix (Fin m) (Fin n) RuntimePolynomial)
    (hS :
      @IsSmithNormalFormFin RuntimePolynomial
        runtimeAlgebra.euclidean runtimeAlgebra.normalization
        runtimeAlgebra.decidableEq m n S) :
    IsSmithNormalFormFin (S.map runtimePolynomialEquiv) := by
  induction hS with
  | emptyRows A =>
      exact .emptyRows _
  | emptyCols A =>
      exact .emptyCols _
  | @zeroLead m n A hzero hrow hcol hLowerZero =>
      apply IsSmithNormalFormFin.zeroLead
      · change runtimePolynomialEquiv (A 0 0) = 0
        rw [hzero]
        exact runtimePolynomialEquiv_runtimeZero
      · intro j
        change runtimePolynomialEquiv (A 0 j.succ) = 0
        rw [hrow j]
        exact runtimePolynomialEquiv_runtimeZero
      · intro i
        change runtimePolynomialEquiv (A i.succ 0) = 0
        rw [hcol i]
        exact runtimePolynomialEquiv_runtimeZero
      · apply _root_.Matrix.ext
        intro i j
        change runtimePolynomialEquiv (A i.succ j.succ) = 0
        have hentry :=
          congrFun (congrFun hLowerZero i) j
        have hmapped := congrArg runtimePolynomialEquiv hentry
        exact hmapped.trans runtimePolynomialEquiv_runtimeZero
  | @pivot m n A hpivot hnorm hrow hcol hLower hdiv ih =>
      apply IsSmithNormalFormFin.pivot
      · intro hzeroMapped
        change runtimePolynomialEquiv (A 0 0) = 0 at hzeroMapped
        apply hpivot
        apply runtimePolynomialEquiv.injective
        exact hzeroMapped.trans runtimePolynomialEquiv_runtimeZero.symm
      · have hmapped := congrArg runtimePolynomialEquiv hnorm
        rw [runtimePolynomialEquiv_normalize] at hmapped
        exact hmapped
      · intro j
        change runtimePolynomialEquiv (A 0 j.succ) = 0
        rw [hrow j]
        exact runtimePolynomialEquiv_runtimeZero
      · intro i
        change runtimePolynomialEquiv (A i.succ 0) = 0
        rw [hcol i]
        exact runtimePolynomialEquiv_runtimeZero
      · convert ih using 1
        rfl
      · intro i j
        rcases hdiv i j with ⟨c, hc⟩
        refine ⟨runtimePolynomialEquiv c, ?_⟩
        change
          runtimePolynomialEquiv (A i.succ j.succ) =
            runtimePolynomialEquiv (A 0 0) *
              runtimePolynomialEquiv c
        have hmapped := congrArg runtimePolynomialEquiv hc
        exact hmapped.trans
          (runtimePolynomialEquiv_divisibilityMul (A 0 0) c)

private theorem canonicalModOf
    (rt : RuntimeAlgebra) :
    @NormalForms.Matrix.Hermite.CanonicalMod
      RuntimePolynomial rt.euclidean := by
  exact
    @NormalForms.Matrix.Hermite.CanonicalMod.mk
      RuntimePolynomial rt.euclidean
      rt.canonicalMod.mod_mod
      rt.canonicalMod.reduced_eq_of_dvd_sub

def endomorphismSmithResultRuntime
    {n : Nat} (rt : RuntimeAlgebra)
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    @SNFResultFin n n RuntimePolynomial
      rt.euclidean rt.normalization rt.decidableEq
      (endomorphismPresentationMatrixRuntime A) :=
  @smithNormalFormFin n n RuntimePolynomial
    rt.euclidean rt.normalization rt.operations rt.decidableEq
    (canonicalModOf rt)
    (endomorphismPresentationMatrixRuntime A)

/--
The complete strong Smith result for `XI - A` over standard `Rat[X]`.

The result carries mapped forward transformations, explicit mapped inverses,
the exact equation `U * (XI - A) * V = S`, and standard Smith-normal-form
semantics.  Its diagonal retains every entry, including unit factors.
-/
public noncomputable def endomorphismSmithResult
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    SNFResultFin (endomorphismPresentationMatrix A) := by
  let rt := runtimeAlgebra
  letI : EuclideanDomain RuntimePolynomial := rt.euclidean
  let sourceMonoidWithZero : MonoidWithZero RuntimePolynomial :=
    @Semiring.toMonoidWithZero RuntimePolynomial
      rt.euclidean.toCommRing.toCommSemiring.toSemiring
  letI : MonoidWithZero RuntimePolynomial := sourceMonoidWithZero
  letI : NormalizationMonoid RuntimePolynomial := rt.normalization
  letI : DecidableEq RuntimePolynomial := rt.decidableEq
  let source := endomorphismPresentationMatrixRuntime A
  let result := endomorphismSmithResultRuntime rt A
  let sourceAddCommMonoid : AddCommMonoid RuntimePolynomial :=
    @Semiring.toAddCommMonoid RuntimePolynomial
      rt.euclidean.toCommRing.toCommSemiring.toSemiring
  letI : AddCommMonoid RuntimePolynomial := sourceAddCommMonoid
  letI : Add RuntimePolynomial := sourceAddCommMonoid.toAdd
  letI : Zero RuntimePolynomial :=
    @MulZeroClass.toZero RuntimePolynomial
      (@instMulZeroClassOfSemiring RuntimePolynomial
        rt.euclidean.toCommRing.toCommSemiring.toSemiring)
  letI : Mul RuntimePolynomial :=
    (@instDistribOfSemiring RuntimePolynomial
      rt.euclidean.toCommRing.toCommSemiring.toSemiring).toMul
  letI : One RuntimePolynomial :=
    @AddMonoidWithOne.toOne RuntimePolynomial
      (@AddGroupWithOne.toAddMonoidWithOne RuntimePolynomial
        (@Ring.toAddGroupWithOne RuntimePolynomial
          rt.euclidean.toCommRing.toRing))
  have hpresentation :
      source.map runtimePolynomialEquiv =
        endomorphismPresentationMatrix A := by
    rw [endomorphismPresentationMatrixRuntime_eq_charmatrix,
      endomorphismPresentationMatrix_eq_charmatrix]
  refine
    { U := result.U.map runtimePolynomialEquiv
      U_cert := mapRuntimeInverseCertificate result.U result.U_cert
      S := result.S.map runtimePolynomialEquiv
      V := result.V.map runtimePolynomialEquiv
      V_cert := mapRuntimeInverseCertificate result.V result.V_cert
      equation := ?_
      isSmith := mapRuntimeIsSmith result.S result.isSmith }
  calc
    result.U.map runtimePolynomialEquiv *
          endomorphismPresentationMatrix A *
          result.V.map runtimePolynomialEquiv =
        result.U.map runtimePolynomialEquiv *
          source.map runtimePolynomialEquiv *
          result.V.map runtimePolynomialEquiv := by
      rw [hpresentation]
    _ = (result.U * source).map runtimePolynomialEquiv *
          result.V.map runtimePolynomialEquiv := by
      rw [runtimePolynomialEquiv_certificateMatrixMul]
    _ = ((result.U * source) * result.V).map
          runtimePolynomialEquiv := by
      exact
        (runtimePolynomialEquiv_certificateMatrixMul
          (result.U * source) result.V).symm
    _ = result.S.map runtimePolynomialEquiv :=
      congrArg (fun M => M.map runtimePolynomialEquiv)
        result.equation

/--
The executable `i`th cyclic factor.

It is computed by the choice-free polynomial Smith kernel and transported to
standard `Rat[X]`.
-/
public def endomorphismInvariantFactor
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (i : Fin n) :
    Rat[X] :=
  let rt := runtimeAlgebra
  let result := endomorphismSmithResultRuntime rt A
  runtimePolynomialEquiv
    ((@SNFResultFin.S n n RuntimePolynomial
      rt.euclidean rt.normalization rt.decidableEq
      (endomorphismPresentationMatrixRuntime A) result) i i)

@[simp]
public theorem endomorphismSmithResult_diagonal
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (i : Fin n) :
    (endomorphismSmithResult A).S i i =
      endomorphismInvariantFactor A i := by
  unfold endomorphismInvariantFactor endomorphismSmithResult
  rfl

end NormalForms.RationalCanonical
