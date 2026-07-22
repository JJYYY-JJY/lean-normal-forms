/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Companion Matrices

An executable companion matrix uses the power-basis convention
`1, X, ..., X^(d - 1)`: ones lie directly below the diagonal and the last
column is the negated lower coefficient vector.

For a monic polynomial, this file identifies the explicit matrix with
multiplication by `AdjoinRoot.root` in mathlib's canonical power basis and
proves that its characteristic polynomial is exactly the input polynomial.
-/

namespace NormalForms.RationalCanonical

open Polynomial

public def companionMatrix
    {R : Type _} [Ring R]
    (p : R[X]) :
    Matrix (Fin p.natDegree) (Fin p.natDegree) R :=
  fun i j =>
    if j.1 + 1 < p.natDegree then
      if i.1 = j.1 + 1 then 1 else 0
    else
      -p.coeff i.1

private theorem modByMonic_X_pow_natDegree
    {R : Type _} [CommRing R] [Nontrivial R]
    {p : R[X]}
    (hp : p.Monic) :
    X ^ p.natDegree %ₘ p = -p.eraseLead := by
  have hsum :
      -p.eraseLead + p * 1 = X ^ p.natDegree := by
    have hpdecomp :
        p.eraseLead + X ^ p.natDegree = p := by
      simpa [hp.leadingCoeff] using
        p.eraseLead_add_C_mul_X_pow
    calc
      -p.eraseLead + p * 1 =
          -p.eraseLead + p := by rw [mul_one]
      _ = -p.eraseLead +
          (p.eraseLead + X ^ p.natDegree) :=
        congrArg (fun q => -p.eraseLead + q) hpdecomp.symm
      _ = X ^ p.natDegree := by abel
  have hdegree :
      (-p.eraseLead).degree < p.degree := by
    rw [degree_neg]
    exact p.degree_eraseLead_lt hp.ne_zero
  exact (div_modByMonic_unique 1 (-p.eraseLead) hp
    ⟨hsum, hdegree⟩).2

private theorem modByMonic_X_pow_of_lt
    {R : Type _} [CommRing R] [Nontrivial R]
    {p : R[X]}
    (hp : p.Monic)
    {k : Nat}
    (hk : k < p.natDegree) :
    X ^ k %ₘ p = X ^ k := by
  apply (modByMonic_eq_self_iff hp).2
  rw [degree_X_pow, degree_eq_natDegree hp.ne_zero]
  exact_mod_cast hk

public theorem companionMatrix_eq_toMatrix
    {R : Type _} [CommRing R] [Nontrivial R]
    (p : R[X])
    (hp : p.Monic) :
    companionMatrix p =
      LinearMap.toMatrix
        (AdjoinRoot.powerBasis' hp).basis
        (AdjoinRoot.powerBasis' hp).basis
        ((Algebra.lmul R (AdjoinRoot p))
          (AdjoinRoot.root p)) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  change
    companionMatrix p i j =
      ((AdjoinRoot.powerBasisAux' hp).repr
        (AdjoinRoot.root p *
          AdjoinRoot.root p ^ (j : Nat))) i
  rw [← pow_succ']
  change
    companionMatrix p i j =
      ((AdjoinRoot.powerBasisAux' hp).repr
        ((AdjoinRoot.mk p) (X ^ (j.1 + 1)))) i
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]
  by_cases hj : j.1 + 1 < p.natDegree
  · rw [modByMonic_X_pow_of_lt hp hj]
    simp [companionMatrix, hj, coeff_X_pow]
  · have hjEq : j.1 + 1 = p.natDegree := by
      omega
    rw [hjEq, modByMonic_X_pow_natDegree hp]
    have hi : i.1 ≠ p.natDegree := by
      omega
    simp [companionMatrix, hj, coeff_neg, eraseLead_coeff,
      hi]

public theorem companionMatrix_charpoly
    {K : Type _} [Field K]
    (p : K[X])
    (hp : p.Monic) :
    (companionMatrix p).charpoly = p := by
  rw [companionMatrix_eq_toMatrix p hp]
  rw [← Algebra.leftMulMatrix_apply]
  change
    ((Algebra.leftMulMatrix
      (AdjoinRoot.powerBasis' hp).basis)
      (AdjoinRoot.powerBasis' hp).gen).charpoly = p
  rw [charpoly_leftMulMatrix, AdjoinRoot.powerBasis'_gen,
    AdjoinRoot.minpoly_root hp.ne_zero, hp.leadingCoeff,
    inv_one, C_1, mul_one]

end NormalForms.RationalCanonical
