/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Presentation

/-!
# Finite Free Integer Chain Complexes

This module fixes the matrix orientation used by the homology application.
`boundary n` represents

`d_(n+1) : C_(n+1) → C_n`,

so its rows index the degree-`n` basis and its columns index the
degree-`n+1` basis.
-/

public section

namespace NormalForms.Applications.Homology

open scoped Matrix

/--
A bounded-above chain complex of finite free integer modules with named
standard bases.

The rank function remains total so degree-zero and out-of-support formulas do
not need partial indices. `finiteSupport` records that all groups above
`topDegree` have rank zero.
-/
public structure IntChainComplex where
  topDegree : Nat
  rank : Nat → Nat
  finiteSupport : ∀ n, topDegree < n → rank n = 0
  boundary :
    (n : Nat) →
      _root_.Matrix (Fin (rank n)) (Fin (rank (n + 1))) Int
  boundary_squared :
    ∀ n, boundary n * boundary (n + 1) = 0

namespace IntChainComplex

/--
Construct a chain complex concentrated in degrees `0`, `1`, and `2`.

`d₁` has shape `rank₀ × rank₁`; `d₂` has shape `rank₁ × rank₂`.
-/
@[expose] public def ofLengthTwo
    (rank₀ rank₁ rank₂ : Nat)
    (d₁ : _root_.Matrix (Fin rank₀) (Fin rank₁) Int)
    (d₂ : _root_.Matrix (Fin rank₁) (Fin rank₂) Int)
    (squared : d₁ * d₂ = 0) :
    IntChainComplex where
  topDegree := 2
  rank
    | 0 => rank₀
    | 1 => rank₁
    | 2 => rank₂
    | _ => 0
  finiteSupport := by
    intro n hn
    rcases n with _ | n
    · omega
    rcases n with _ | n
    · omega
    rcases n with _ | n
    · omega
    rfl
  boundary
    | 0 => d₁
    | 1 => d₂
    | _ + 2 => 0
  boundary_squared := by
    intro n
    rcases n with _ | n
    · exact squared
    rcases n with _ | n
    · simp
    simp

@[simp] public theorem ofLengthTwo_rank_zero
    (rank₀ rank₁ rank₂ : Nat)
    (d₁ : _root_.Matrix (Fin rank₀) (Fin rank₁) Int)
    (d₂ : _root_.Matrix (Fin rank₁) (Fin rank₂) Int)
    (squared : d₁ * d₂ = 0) :
    (ofLengthTwo rank₀ rank₁ rank₂ d₁ d₂ squared).rank 0 = rank₀ :=
  rfl

@[simp] public theorem ofLengthTwo_rank_one
    (rank₀ rank₁ rank₂ : Nat)
    (d₁ : _root_.Matrix (Fin rank₀) (Fin rank₁) Int)
    (d₂ : _root_.Matrix (Fin rank₁) (Fin rank₂) Int)
    (squared : d₁ * d₂ = 0) :
    (ofLengthTwo rank₀ rank₁ rank₂ d₁ d₂ squared).rank 1 = rank₁ :=
  rfl

@[simp] public theorem ofLengthTwo_rank_two
    (rank₀ rank₁ rank₂ : Nat)
    (d₁ : _root_.Matrix (Fin rank₀) (Fin rank₁) Int)
    (d₂ : _root_.Matrix (Fin rank₁) (Fin rank₂) Int)
    (squared : d₁ * d₂ = 0) :
    (ofLengthTwo rank₀ rank₁ rank₂ d₁ d₂ squared).rank 2 = rank₂ :=
  rfl

@[simp] public theorem ofLengthTwo_boundary_zero
    (rank₀ rank₁ rank₂ : Nat)
    (d₁ : _root_.Matrix (Fin rank₀) (Fin rank₁) Int)
    (d₂ : _root_.Matrix (Fin rank₁) (Fin rank₂) Int)
    (squared : d₁ * d₂ = 0) :
    (ofLengthTwo rank₀ rank₁ rank₂ d₁ d₂ squared).boundary 0 = d₁ :=
  rfl

@[simp] public theorem ofLengthTwo_boundary_one
    (rank₀ rank₁ rank₂ : Nat)
    (d₁ : _root_.Matrix (Fin rank₀) (Fin rank₁) Int)
    (d₂ : _root_.Matrix (Fin rank₁) (Fin rank₂) Int)
    (squared : d₁ * d₂ = 0) :
    (ofLengthTwo rank₀ rank₁ rank₂ d₁ d₂ squared).boundary 1 = d₂ :=
  rfl

/-- Rank of the target of the outgoing boundary in degree `n`. -/
@[expose] public def previousRank (complex : IntChainComplex) : Nat → Nat
  | 0 => 0
  | n + 1 => complex.rank n

/--
The outgoing differential `d_n : C_n → C_(n-1)`, with `d_0` represented by
the unique `0 × rank 0` matrix.
-/
@[expose] public def outgoingBoundary
    (complex : IntChainComplex) :
    (n : Nat) →
      _root_.Matrix
        (Fin (complex.previousRank n))
        (Fin (complex.rank n)) Int
  | 0 => 0
  | n + 1 => complex.boundary n

/-- The incoming differential `d_(n+1) : C_(n+1) → C_n`. -/
@[expose] public def incomingBoundary
    (complex : IntChainComplex) (n : Nat) :
    _root_.Matrix
      (Fin (complex.rank n))
      (Fin (complex.rank (n + 1))) Int :=
  complex.boundary n

@[simp] public theorem previousRank_zero (complex : IntChainComplex) :
    complex.previousRank 0 = 0 :=
  rfl

@[simp] public theorem previousRank_succ
    (complex : IntChainComplex) (n : Nat) :
    complex.previousRank (n + 1) = complex.rank n :=
  rfl

@[simp] public theorem outgoingBoundary_zero (complex : IntChainComplex) :
    complex.outgoingBoundary 0 =
      (0 : _root_.Matrix (Fin 0) (Fin (complex.rank 0)) Int) :=
  rfl

@[simp] public theorem outgoingBoundary_succ
    (complex : IntChainComplex) (n : Nat) :
    complex.outgoingBoundary (n + 1) = complex.boundary n :=
  rfl

@[simp] public theorem incomingBoundary_eq
    (complex : IntChainComplex) (n : Nat) :
    complex.incomingBoundary n = complex.boundary n :=
  rfl

/--
The matrix form of `d_n d_(n+1) = 0`, including the degree-zero boundary.
-/
public theorem outgoing_mul_incoming
    (complex : IntChainComplex) (n : Nat) :
    complex.outgoingBoundary n * complex.incomingBoundary n = 0 := by
  cases n with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ n =>
      exact complex.boundary_squared n

/-- Degree-`n` cycles inside the chosen standard basis of `C_n`. -/
public abbrev cycles
    (complex : IntChainComplex) (n : Nat) :
    Submodule Int (Fin (complex.rank n) → Int) :=
  LinearMap.ker (complex.outgoingBoundary n).mulVecLin

/--
The incoming boundary map with codomain restricted to degree-`n` cycles.
-/
@[expose] public def boundaryCycleMap
    (complex : IntChainComplex) (n : Nat) :
    (Fin (complex.rank (n + 1)) → Int) →ₗ[Int] complex.cycles n :=
  LinearMap.codRestrict
    (complex.cycles n)
    (complex.incomingBoundary n).mulVecLin
    (by
      intro vector
      change
        (complex.outgoingBoundary n).mulVec
            ((complex.incomingBoundary n).mulVec vector) =
          0
      rw [Matrix.mulVec_mulVec, complex.outgoing_mul_incoming]
      exact Matrix.zero_mulVec vector)

/-- Degree-`n` boundaries, represented as a submodule of the cycle module. -/
public abbrev boundaries
    (complex : IntChainComplex) (n : Nat) :
    Submodule Int (complex.cycles n) :=
  LinearMap.range (complex.boundaryCycleMap n)

/-- The ordinary homology quotient `ker d_n / im d_(n+1)`. -/
public abbrev homology
    (complex : IntChainComplex) (n : Nat) :=
  complex.cycles n ⧸ complex.boundaries n

@[simp] public theorem boundaryCycleMap_coe
    (complex : IntChainComplex) (n : Nat)
    (vector : Fin (complex.rank (n + 1)) → Int) :
    ((complex.boundaryCycleMap n vector :
        complex.cycles n) :
      Fin (complex.rank n) → Int) =
      (complex.incomingBoundary n).mulVec vector := by
  rfl

end IntChainComplex

end NormalForms.Applications.Homology
