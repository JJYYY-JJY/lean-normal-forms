/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Endomorphism Presentation Matrices

The finite, executable `XI - A` matrix used by the rational canonical form
application.  Its coefficients are assembled directly rather than through
mathlib's noncomputable polynomial subtraction instance.  The theorem
`endomorphismPresentationMatrix_eq_charmatrix` supplies the semantic bridge.
-/

namespace NormalForms.RationalCanonical

open Polynomial

private def finsuppOfCandidates
    {K : Type u} [CommRing K] [DecidableEq K]
    (support : Finset Nat) (coefficient : Nat → K)
    (supported : ∀ degree, coefficient degree ≠ 0 → degree ∈ support) :
    Nat →₀ K where
  support :=
    support.filter fun degree => decide (coefficient degree ≠ 0)
  toFun := coefficient
  mem_support_toFun := by
    intro degree
    simp only [Finset.mem_filter, decide_eq_true_eq]
    exact
      ⟨fun member => member.2,
        fun nonzero => ⟨supported degree nonzero, nonzero⟩⟩

private def polynomialOfCoefficients
    {K : Type u} [CommRing K] [DecidableEq K]
    (support : Finset Nat) (coefficient : Nat → K)
    (supported : ∀ degree, coefficient degree ≠ 0 → degree ∈ support) :
    K[X] :=
  .ofFinsupp (.ofCoeff
    (finsuppOfCandidates support coefficient supported))

@[simp]
private theorem polynomialOfCoefficients_coeff
    {K : Type u} [CommRing K] [DecidableEq K]
    (support : Finset Nat) (coefficient : Nat → K)
    (supported : ∀ degree, coefficient degree ≠ 0 → degree ∈ support)
    (degree : Nat) :
    (polynomialOfCoefficients support coefficient supported).coeff degree =
      coefficient degree :=
  rfl

private def variableMinusConstant
    {K : Type u} [CommRing K] [DecidableEq K] (a : K) : K[X] :=
  polynomialOfCoefficients {0, 1}
    (fun degree =>
      if degree = 0 then -a
      else if degree = 1 then 1
      else 0) (by
        intro degree nonzero
        by_cases hzero : degree = 0
        · simp [hzero]
        · by_cases hone : degree = 1
          · simp [hone]
          · simp [hzero, hone] at nonzero)

private def negativeConstant
    {K : Type u} [CommRing K] [DecidableEq K] (a : K) : K[X] :=
  polynomialOfCoefficients {0}
    (fun degree => if degree = 0 then -a else 0) (by
      intro degree nonzero
      by_cases hzero : degree = 0
      · simp [hzero]
      · simp [hzero] at nonzero)

@[simp]
private theorem variableMinusConstant_eq
    {K : Type u} [CommRing K] [DecidableEq K] (a : K) :
    variableMinusConstant a = X - C a := by
  apply Polynomial.coeff_injective
  funext degree
  simp only [variableMinusConstant, polynomialOfCoefficients_coeff,
    coeff_sub, coeff_X, coeff_C]
  by_cases hzero : degree = 0
  · simp [hzero]
  · by_cases hone : degree = 1
    · simp [hone]
    · simp [hzero, hone, Ne.symm hone]

@[simp]
private theorem negativeConstant_eq
    {K : Type u} [CommRing K] [DecidableEq K] (a : K) :
    negativeConstant a = -C a := by
  apply Polynomial.coeff_injective
  funext degree
  simp only [negativeConstant, polynomialOfCoefficients_coeff,
    coeff_neg, coeff_C]
  by_cases hzero : degree = 0
  · simp [hzero]
  · simp [hzero]

/--
The polynomial presentation matrix `XI - A` of an endomorphism matrix `A`.

Rows and columns use the same canonical `Fin n` order.  This entrywise
definition is executable whenever the coefficient-ring operations are.
-/
public def endomorphismPresentationMatrix
    {K : Type u} [CommRing K] [DecidableEq K] {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) K) :
    _root_.Matrix (Fin n) (Fin n) K[X] :=
  fun i j =>
    if i = j then
      variableMinusConstant (A i j)
    else
      negativeConstant (A i j)

@[simp]
public theorem endomorphismPresentationMatrix_apply_eq
    {K : Type u} [CommRing K] [DecidableEq K] {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) K) (i : Fin n) :
    endomorphismPresentationMatrix A i i = X - C (A i i) := by
  simp [endomorphismPresentationMatrix]

@[simp]
public theorem endomorphismPresentationMatrix_apply_ne
    {K : Type u} [CommRing K] [DecidableEq K] {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) K) {i j : Fin n}
    (h : i ≠ j) :
    endomorphismPresentationMatrix A i j = -C (A i j) := by
  simp [endomorphismPresentationMatrix, h]

/--
The executable presentation matrix is exactly mathlib's characteristic
matrix, with no reindexing or transpose.
-/
public theorem endomorphismPresentationMatrix_eq_charmatrix
    {K : Type u} [CommRing K] [DecidableEq K] {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) K) :
    endomorphismPresentationMatrix A = A.charmatrix := by
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- The determinant of `XI - A` is the characteristic polynomial of `A`. -/
public theorem endomorphismPresentationMatrix_det
    {K : Type u} [CommRing K] [DecidableEq K] {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) K) :
    (endomorphismPresentationMatrix A).det = A.charpoly := by
  rw [endomorphismPresentationMatrix_eq_charmatrix]
  rfl

end NormalForms.RationalCanonical
