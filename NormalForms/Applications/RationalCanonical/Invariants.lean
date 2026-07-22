/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.RationalCanonical.Runtime
public import NormalForms.Applications.RationalCanonical.SmithResult
import all NormalForms.Applications.RationalCanonical.SmithResult
import all NormalForms.Matrix.Smith.Defs

/-!
# Executable Endomorphism Invariant Factors

The strong polynomial Smith kernel computes over the choice-free runtime.
This module reads its complete square diagonal and transports every factor to
standard `Rat[X]` through `runtimePolynomialEquiv`.

For an `n × n` characteristic matrix the complete Smith diagonal has exactly
`n` entries, including unit factors.  The later module-decomposition layer
filters unit factors only for the human-facing cyclic-summand view.
-/

namespace NormalForms.RationalCanonical

open Polynomial
open PolynomialRatRuntime
open NormalForms.Matrix.Smith
open NormalForms.Matrix.Certificates
open scoped Matrix

private theorem smithDet_associated
    {n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin n) (Fin n) R}
    (result : SNFResultFin A) :
    Associated result.S.det A.det := by
  have hdet :
      (result.U.det * A.det) * result.V.det =
        result.S.det := by
    have := congrArg _root_.Matrix.det result.equation
    simpa only [_root_.Matrix.det_mul] using this
  have hU : IsUnit result.U.det :=
    result.U_cert.unimodular
  have hV : IsUnit result.V.det :=
    result.V_cert.unimodular
  rw [← hdet]
  exact
    ((associated_mul_unit_left
        (result.U.det * A.det) result.V.det hV).trans
      (associated_unit_mul_left A.det result.U.det hU))

/--
The normalized endomorphism invariant factors over standard `Rat[X]`.

The list includes unit factors.  Its length is exactly the matrix dimension;
the empty endomorphism therefore has no factors.
-/
public def endomorphismInvariantFactors
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    List Rat[X] :=
  (List.finRange n).map (endomorphismInvariantFactor A)

@[simp]
public theorem endomorphismInvariantFactors_length
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    (endomorphismInvariantFactors A).length = n := by
  simp [endomorphismInvariantFactors]

@[simp]
public theorem endomorphismInvariantFactors_eq_diagonal
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    endomorphismInvariantFactors A =
      (List.finRange n).map
        (endomorphismInvariantFactor A) := by
  rfl

/--
The product of all normalized endomorphism invariant factors, including unit
factors, is exactly the characteristic polynomial.
-/
public theorem endomorphismInvariantFactors_product
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    (endomorphismInvariantFactors A).prod = A.charpoly := by
  let rt := runtimeAlgebra
  let presentation := endomorphismPresentationMatrixRuntime A
  let result := endomorphismSmithResultRuntime rt A
  let S :=
    @SNFResultFin.S n n RuntimePolynomial
      rt.euclidean rt.normalization rt.decidableEq
      presentation result
  let hSmith :=
    @SNFResultFin.isSmith n n RuntimePolynomial
      rt.euclidean rt.normalization rt.decidableEq
      presentation result
  have hAssociatedSource :
      @Associated RuntimePolynomial rt.euclidean.toMonoid
        (@_root_.Matrix.det (Fin n) inferInstance inferInstance
          RuntimePolynomial rt.euclidean.toCommRing S)
        (@_root_.Matrix.det (Fin n) inferInstance inferInstance
          RuntimePolynomial rt.euclidean.toCommRing presentation) :=
    @smithDet_associated n RuntimePolynomial
      rt.euclidean rt.normalization rt.decidableEq
      presentation result
  have hAssociatedMapped :
      Associated
        (runtimePolynomialEquiv
          (@_root_.Matrix.det (Fin n) inferInstance inferInstance
            RuntimePolynomial rt.euclidean.toCommRing S))
        (runtimePolynomialEquiv
          (@_root_.Matrix.det (Fin n) inferInstance inferInstance
            RuntimePolynomial rt.euclidean.toCommRing presentation)) :=
    runtimePolynomialEquiv_associated hAssociatedSource
  have hMapDetS :
      runtimePolynomialEquiv
          (@_root_.Matrix.det (Fin n) inferInstance inferInstance
            RuntimePolynomial rt.euclidean.toCommRing S) =
        (S.map runtimePolynomialEquiv).det := by
    exact runtimePolynomialEquiv_det S
  have hMapDetPresentation :
      runtimePolynomialEquiv
          (@_root_.Matrix.det (Fin n) inferInstance inferInstance
            RuntimePolynomial rt.euclidean.toCommRing presentation) =
        A.charpoly := by
    calc
      runtimePolynomialEquiv
          (@_root_.Matrix.det (Fin n) inferInstance inferInstance
            RuntimePolynomial rt.euclidean.toCommRing presentation) =
          (presentation.map runtimePolynomialEquiv).det := by
            exact runtimePolynomialEquiv_det presentation
      _ = A.charmatrix.det := by
        rw [endomorphismPresentationMatrixRuntime_eq_charmatrix]
      _ = A.charpoly := rfl
  let hdiag :=
    @Internal.isSmithNormalFormFin_toDiag n n
      RuntimePolynomial rt.euclidean rt.normalization
      rt.decidableEq S hSmith
  have hMappedIsDiag :
      (S.map runtimePolynomialEquiv).IsDiag := by
    intro i j hij
    change runtimePolynomialEquiv (S i j) = 0
    have hzero :=
      hdiag.1 i j (fun h => hij (Fin.ext h))
    rw [hzero]
    exact runtimePolynomialEquiv_runtimeZero
  have hMappedEntryNormalized :
      ∀ i : Fin n,
        normalize (runtimePolynomialEquiv (S i i)) =
          runtimePolynomialEquiv (S i i) := by
    intro i
    have hi : i.1 < Nat.min n n := by
      exact (Nat.lt_min).2 ⟨i.2, i.2⟩
    have hsource :
        S i i =
          @_root_.normalize RuntimePolynomial
            rt.euclidean.toMonoidWithZero rt.normalization
            (S i i) := by
      simpa [Internal.diagEntry] using
        hdiag.2.1 i.1 hi
    have hmapped :=
      congrArg runtimePolynomialEquiv hsource
    rw [runtimePolynomialEquiv_normalize] at hmapped
    exact hmapped.symm
  have hMappedDetProduct :
      runtimePolynomialEquiv
          (@_root_.Matrix.det (Fin n) inferInstance inferInstance
            RuntimePolynomial rt.euclidean.toCommRing S) =
        ((List.finRange n).map fun i =>
          runtimePolynomialEquiv (S i i)).prod := by
    calc
      runtimePolynomialEquiv
          (@_root_.Matrix.det (Fin n) inferInstance inferInstance
            RuntimePolynomial rt.euclidean.toCommRing S) =
          (S.map runtimePolynomialEquiv).det :=
        hMapDetS
      _ = ∏ i, runtimePolynomialEquiv (S i i) := by
        rw [← hMappedIsDiag.diagonal_diag,
          _root_.Matrix.det_diagonal]
        simp
      _ =
          ((List.finRange n).map fun i =>
            runtimePolynomialEquiv (S i i)).prod :=
        Fin.prod_univ_def _
  have hProductNormalized :
      normalize
          (((List.finRange n).map fun i =>
            runtimePolynomialEquiv (S i i)).prod) =
        ((List.finRange n).map fun i =>
          runtimePolynomialEquiv (S i i)).prod := by
    induction List.finRange n with
    | nil =>
        exact normalize_one
    | cons i indices ih =>
        simp only [List.map_cons, List.prod_cons]
        rw [normalize_mul, hMappedEntryNormalized i, ih]
  have hAssociatedProduct :
      Associated
        (((List.finRange n).map fun i =>
          runtimePolynomialEquiv (S i i)).prod)
        A.charpoly := by
    rw [← hMappedDetProduct, ← hMapDetPresentation]
    exact hAssociatedMapped
  have hCharpolyNormalized :
      normalize A.charpoly = A.charpoly :=
    (A.charpoly_monic).normalize_eq_self
  change
    (((List.finRange n).map fun i =>
      runtimePolynomialEquiv (S i i)).prod) =
      A.charpoly
  calc
    ((List.finRange n).map fun i =>
        runtimePolynomialEquiv (S i i)).prod =
        normalize
          (((List.finRange n).map fun i =>
            runtimePolynomialEquiv (S i i)).prod) :=
      hProductNormalized.symm
    _ = normalize A.charpoly :=
      normalize_eq_normalize_iff_associated.mpr
        hAssociatedProduct
    _ = A.charpoly :=
      hCharpolyNormalized

/--
The largest invariant factor, when the endomorphism has positive dimension.
The zero-dimensional case returns `none`.
-/
public def largestInvariantFactor?
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    Option Rat[X] :=
  (endomorphismInvariantFactors A).getLast?

@[simp]
public theorem largestInvariantFactor?_empty
    (A : _root_.Matrix (Fin 0) (Fin 0) Rat) :
    largestInvariantFactor? A = none := by
  simp [largestInvariantFactor?, endomorphismInvariantFactors]

private theorem finRange_getLast?_succ
    (k : Nat) :
    (List.finRange (k + 1)).getLast? =
      some (Fin.last k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.finRange_succ]
      rw [List.getLast?_cons_of_ne_nil (by simp)]
      rw [List.getLast?_map, ih]
      simp [Fin.succ_last]

@[simp]
public theorem largestInvariantFactor?_succ
    {k : Nat}
    (A : _root_.Matrix (Fin (k + 1)) (Fin (k + 1)) Rat) :
    largestInvariantFactor? A =
      some (endomorphismInvariantFactor A (Fin.last k)) := by
  simp only [largestInvariantFactor?,
    endomorphismInvariantFactors, List.getLast?_map,
    finRange_getLast?_succ, Option.map_some]

end NormalForms.RationalCanonical
