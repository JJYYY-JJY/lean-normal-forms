/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Constructive finite matrix algebra

The corresponding general-purpose mathlib lemmas currently pass through
`Classical.choice`.  The executable normal-form kernels use the finite,
decidable versions below so their proof payload stays inside the strict core
axiom boundary.
-/

set_option linter.privateModule false

namespace NormalForms.Matrix.Constructive

open scoped Matrix BigOperators

set_option linter.unusedDecidableInType false

@[expose] public section

theorem finRange_nodup : ∀ n, (List.finRange n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.finRange_succ]
      apply List.Nodup.cons
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨i, _, hi⟩
        exact Fin.succ_ne_zero i hi
      · exact (finRange_nodup n).map (Fin.succ_injective n)

/--
The standard `Fin.fintype` currently inherits a choice-bearing nodup proof.
This definition has the same enumeration and a constructive proof payload.
-/
abbrev finFintype (n : Nat) : Fintype (Fin n) where
  elems := ⟨List.finRange n, finRange_nodup n⟩
  complete := List.mem_finRange

attribute [instance 10000] finFintype

theorem sum_univ_succ {M : Type*} [AddCommMonoid M] {n : Nat}
    (f : Fin (n + 1) → M) :
    (∑ i, f i) = f 0 + ∑ i : Fin n, f i.succ := by
  change
    (List.map f (List.finRange (n + 1))).sum =
      f 0 + (List.map (fun i : Fin n => f i.succ) (List.finRange n)).sum
  rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map]
  rfl

theorem sum_univ_two {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) :
    (∑ i, f i) = f 0 + f 1 := by
  rw [sum_univ_succ, sum_univ_succ]
  change f 0 + (f 1 + 0) = f 0 + f 1
  rw [add_zero]

theorem sum_comm {α β γ : Type*} [AddCommMonoid β]
    [DecidableEq α] [DecidableEq γ]
    (s : Finset γ) (t : Finset α) (f : γ → α → β) :
    (∑ x ∈ s, ∑ y ∈ t, f x y) = ∑ y ∈ t, ∑ x ∈ s, f x y := by
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact (Finset.sum_const_zero).symm
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, ih]
      simp only [Finset.sum_insert hx]
      exact Finset.sum_add_distrib.symm

theorem sum_ite_eq {ι M : Type*} [AddCommMonoid M] [DecidableEq ι]
    (s : Finset ι) (a : ι) (b : ι → M) :
    (∑ x ∈ s, if a = x then b x else 0) =
      if a ∈ s then b a else 0 := by
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      rfl
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, ih]
      by_cases h : a = x
      · subst x
        simp only [if_pos, Finset.mem_insert, true_or, hx, if_false, add_zero]
      · simp only [h, if_false, Finset.mem_insert, false_or, zero_add]

theorem sum_ite_eq_right {ι M : Type*} [AddCommMonoid M] [DecidableEq ι]
    (s : Finset ι) (a : ι) (b : ι → M) :
    (∑ x ∈ s, if x = a then b x else 0) =
      if a ∈ s then b a else 0 := by
  simpa only [eq_comm] using sum_ite_eq s a b

theorem one_mul {m n α : Type*} [NonAssocSemiring α]
    [Fintype m] [DecidableEq m] (M : _root_.Matrix m n α) :
    (1 : _root_.Matrix m m α) * M = M := by
  ext i j
  simp only [_root_.Matrix.mul_apply, _root_.Matrix.one_apply, ite_mul,
    _root_.one_mul, zero_mul]
  rw [sum_ite_eq]
  simp only [Finset.mem_univ, if_true]

theorem mul_one {m n α : Type*} [NonAssocSemiring α]
    [Fintype n] [DecidableEq n] (M : _root_.Matrix m n α) :
    M * (1 : _root_.Matrix n n α) = M := by
  ext i j
  simp only [_root_.Matrix.mul_apply, _root_.Matrix.one_apply, mul_ite,
    _root_.mul_one, mul_zero]
  rw [sum_ite_eq_right]
  simp only [Finset.mem_univ, if_true]

theorem one_mulVec {m α : Type*} [NonAssocSemiring α]
    [Fintype m] [DecidableEq m] (v : m → α) :
    _root_.Matrix.mulVec (1 : _root_.Matrix m m α) v = v := by
  funext i
  simp only [_root_.Matrix.mulVec, dotProduct, _root_.Matrix.one_apply,
    ite_mul, _root_.one_mul, zero_mul]
  rw [sum_ite_eq]
  simp only [Finset.mem_univ, if_true]

theorem one_mul_mul_one {m n α : Type*} [NonAssocSemiring α]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : _root_.Matrix m n α) :
    (1 : _root_.Matrix m m α) * M *
        (1 : _root_.Matrix n n α) = M := by
  rw [one_mul, mul_one]

theorem mul_assoc {l m n o α : Type*} [NonUnitalSemiring α]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (L : _root_.Matrix l m α) (M : _root_.Matrix m n α)
    (N : _root_.Matrix n o α) :
    L * M * N = L * (M * N) := by
  ext i j
  simp only [_root_.Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
    _root_.mul_assoc]
  exact sum_comm Finset.univ Finset.univ
    (fun x y => L i y * (M y x * N x j))

theorem updateRow_mul {l m n α : Type*} [NonUnitalNonAssocSemiring α]
    [Fintype m] [DecidableEq l]
    (L : _root_.Matrix l m α) (i : l) (row : m → α)
    (M : _root_.Matrix m n α) :
    _root_.Matrix.updateRow L i row * M =
      _root_.Matrix.updateRow (L * M) i (_root_.Matrix.vecMul row M) := by
  ext r c
  by_cases h : r = i
  · subst r
    simp only [_root_.Matrix.mul_apply, _root_.Matrix.updateRow_self,
      _root_.Matrix.vecMul, dotProduct]
  · simp only [_root_.Matrix.mul_apply, _root_.Matrix.updateRow_ne h]

theorem mul_updateCol {l m n α : Type*} [NonUnitalNonAssocSemiring α]
    [Fintype m] [DecidableEq n]
    (L : _root_.Matrix l m α) (M : _root_.Matrix m n α)
    (j : n) (column : m → α) :
    L * _root_.Matrix.updateCol M j column =
      _root_.Matrix.updateCol (L * M) j (_root_.Matrix.mulVec L column) := by
  ext r c
  by_cases h : c = j
  · subst c
    simp only [_root_.Matrix.mul_apply, _root_.Matrix.updateCol_self,
      _root_.Matrix.mulVec, dotProduct]
  · simp only [_root_.Matrix.mul_apply, _root_.Matrix.updateCol_ne h]

end

end NormalForms.Matrix.Constructive
