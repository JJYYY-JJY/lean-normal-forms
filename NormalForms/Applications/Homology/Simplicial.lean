/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.Homology.Runtime

/-!
# Finite Normalized Simplicial Data

This module provides the explicit v1.2.1 frontend for finite normalized
simplicial chains. Only nondegenerate simplices receive indices. A face is
either another nondegenerate simplex or `none`, meaning that the face is
degenerate and vanishes in normalized chains.

Boundary matrices are derived from the face table with the alternating
integer sign. The data structure requires the resulting adjacent matrices to
multiply to zero; it does not duplicate a separately supplied matrix.
-/

public section

namespace NormalForms.Applications.Homology

open scoped Matrix

/-- Alternating sign of the `i`th simplicial face. -/
@[expose] public def simplicialFaceSign (i : Nat) : Int :=
  (-1 : Int) ^ i

@[simp] public theorem simplicialFaceSign_even (i : Nat) (hi : Even i) :
    simplicialFaceSign i = 1 := by
  rcases hi with ⟨i, rfl⟩
  simp [simplicialFaceSign]

@[simp] public theorem simplicialFaceSign_odd (i : Nat) (hi : Odd i) :
    simplicialFaceSign i = -1 := by
  rcases hi with ⟨i, rfl⟩
  simp [simplicialFaceSign, pow_add]

/--
Contribution of one face to one normalized boundary-matrix entry.

`none` is the explicit degeneracy-elimination case. Repeated nondegenerate
faces remain separate summands, so their alternating signs can cancel.
-/
@[expose] public def normalizedFaceTerm
    (simplexCount : Nat → Nat)
    (face :
      (n : Nat) →
        Fin (n + 2) →
          Fin (simplexCount (n + 1)) →
            Option (Fin (simplexCount n)))
    (n : Nat)
    (row : Fin (simplexCount n))
    (column : Fin (simplexCount (n + 1)))
    (i : Fin (n + 2)) : Int :=
  match face n i column with
  | none => 0
  | some target =>
      if target = row then simplicialFaceSign i.1 else 0

@[simp] public theorem normalizedFaceTerm_eq_zero_of_degenerate
    (simplexCount : Nat → Nat)
    (face :
      (n : Nat) →
        Fin (n + 2) →
          Fin (simplexCount (n + 1)) →
            Option (Fin (simplexCount n)))
    (n : Nat)
    (row : Fin (simplexCount n))
    (column : Fin (simplexCount (n + 1)))
    (i : Fin (n + 2))
    (hface : face n i column = none) :
    normalizedFaceTerm simplexCount face n row column i = 0 := by
  simp [normalizedFaceTerm, hface]

@[simp] public theorem normalizedFaceTerm_eq_sign
    (simplexCount : Nat → Nat)
    (face :
      (n : Nat) →
        Fin (n + 2) →
          Fin (simplexCount (n + 1)) →
            Option (Fin (simplexCount n)))
    (n : Nat)
    (row : Fin (simplexCount n))
    (column : Fin (simplexCount (n + 1)))
    (i : Fin (n + 2))
    (hface : face n i column = some row) :
    normalizedFaceTerm simplexCount face n row column i =
      simplicialFaceSign i.1 := by
  simp [normalizedFaceTerm, hface]

@[simp] public theorem normalizedFaceTerm_eq_zero_of_other
    (simplexCount : Nat → Nat)
    (face :
      (n : Nat) →
        Fin (n + 2) →
          Fin (simplexCount (n + 1)) →
            Option (Fin (simplexCount n)))
    (n : Nat)
    (row target : Fin (simplexCount n))
    (column : Fin (simplexCount (n + 1)))
    (i : Fin (n + 2))
    (hface : face n i column = some target)
    (hne : target ≠ row) :
    normalizedFaceTerm simplexCount face n row column i = 0 := by
  simp [normalizedFaceTerm, hface, hne]

/--
Normalized boundary matrix derived from finite face data.

Rows are dimension-`n` nondegenerate simplices and columns are
dimension-`n+1` nondegenerate simplices.
-/
@[expose] public def normalizedBoundaryMatrix
    (simplexCount : Nat → Nat)
    (face :
      (n : Nat) →
        Fin (n + 2) →
          Fin (simplexCount (n + 1)) →
            Option (Fin (simplexCount n)))
    (n : Nat) :
    _root_.Matrix
      (Fin (simplexCount n))
      (Fin (simplexCount (n + 1))) Int :=
  fun row column =>
    ∑ i : Fin (n + 2),
      normalizedFaceTerm simplexCount face n row column i

/--
Finite normalized simplicial data with an explicit enumeration of every
nondegenerate simplex.

The `face` result `none` means that the corresponding raw face is degenerate
and is erased by normalized chains. The `boundary_squared` field validates
the derived alternating face sums, including all cancellations caused by
repeated faces and degeneracy elimination.
-/
public structure FiniteNormalizedSimplicialData where
  topDimension : Nat
  simplexCount : Nat → Nat
  finiteSupport : ∀ n, topDimension < n → simplexCount n = 0
  face :
    (n : Nat) →
      Fin (n + 2) →
        Fin (simplexCount (n + 1)) →
          Option (Fin (simplexCount n))
  boundary_squared :
    ∀ n,
      normalizedBoundaryMatrix simplexCount face n *
          normalizedBoundaryMatrix simplexCount face (n + 1) =
        0

namespace FiniteNormalizedSimplicialData

/-- The normalized integer boundary `d_(n+1)`. -/
@[expose] public def boundary
    (data : FiniteNormalizedSimplicialData) (n : Nat) :
    _root_.Matrix
      (Fin (data.simplexCount n))
      (Fin (data.simplexCount (n + 1))) Int :=
  normalizedBoundaryMatrix data.simplexCount data.face n

@[simp] public theorem boundary_apply
    (data : FiniteNormalizedSimplicialData) (n : Nat)
    (row : Fin (data.simplexCount n))
    (column : Fin (data.simplexCount (n + 1))) :
    data.boundary n row column =
      ∑ i : Fin (n + 2),
        normalizedFaceTerm
          data.simplexCount data.face n row column i :=
  rfl

public theorem boundary_mul_boundary
    (data : FiniteNormalizedSimplicialData) (n : Nat) :
    data.boundary n * data.boundary (n + 1) = 0 :=
  data.boundary_squared n

/-- Convert normalized face data to the v1.2.0 finite-free chain interface. -/
@[expose] public def toIntChainComplex
    (data : FiniteNormalizedSimplicialData) :
    IntChainComplex where
  topDegree := data.topDimension
  rank := data.simplexCount
  finiteSupport := data.finiteSupport
  boundary := data.boundary
  boundary_squared := data.boundary_mul_boundary

@[simp] public theorem toIntChainComplex_rank
    (data : FiniteNormalizedSimplicialData) (n : Nat) :
    data.toIntChainComplex.rank n = data.simplexCount n :=
  rfl

@[simp] public theorem toIntChainComplex_boundary
    (data : FiniteNormalizedSimplicialData) (n : Nat) :
    data.toIntChainComplex.boundary n = data.boundary n :=
  rfl

/-- Simplex counts for data concentrated in dimensions zero through two. -/
@[expose] public def dimensionTwoSimplexCount
    (vertices edges triangles : Nat) : Nat → Nat
  | 0 => vertices
  | 1 => edges
  | 2 => triangles
  | _ + 3 => 0

/-- Total normalized face table for data concentrated through dimension two. -/
@[expose] public def dimensionTwoFace
    (vertices edges triangles : Nat)
    (edgeFace :
      Fin 2 → Fin edges → Option (Fin vertices))
    (triangleFace :
      Fin 3 → Fin triangles → Option (Fin edges)) :
    (n : Nat) →
      Fin (n + 2) →
        Fin (dimensionTwoSimplexCount vertices edges triangles (n + 1)) →
          Option
            (Fin (dimensionTwoSimplexCount vertices edges triangles n))
  | 0 => edgeFace
  | 1 => triangleFace
  | _ + 2 => fun _ simplex => Fin.elim0 simplex

/--
Construct normalized simplicial data concentrated in dimensions zero through
two. Only the nontrivial equation `d₁d₂ = 0` must be supplied; every later
product has an empty column type.
-/
@[expose] public def ofDimensionTwo
    (vertices edges triangles : Nat)
    (edgeFace :
      Fin 2 → Fin edges → Option (Fin vertices))
    (triangleFace :
      Fin 3 → Fin triangles → Option (Fin edges))
    (squared :
      normalizedBoundaryMatrix
          (dimensionTwoSimplexCount vertices edges triangles)
          (dimensionTwoFace
            vertices edges triangles edgeFace triangleFace) 0 *
        normalizedBoundaryMatrix
          (dimensionTwoSimplexCount vertices edges triangles)
          (dimensionTwoFace
            vertices edges triangles edgeFace triangleFace) 1 =
        0) :
    FiniteNormalizedSimplicialData where
  topDimension := 2
  simplexCount := dimensionTwoSimplexCount vertices edges triangles
  finiteSupport := by
    intro n hn
    rcases n with _ | n
    · omega
    rcases n with _ | n
    · omega
    rcases n with _ | n
    · omega
    rfl
  face := dimensionTwoFace
    vertices edges triangles edgeFace triangleFace
  boundary_squared := by
    intro n
    cases n with
    | zero => exact squared
    | succ n =>
        ext row column
        exact Fin.elim0 column

end FiniteNormalizedSimplicialData

end NormalForms.Applications.Homology
