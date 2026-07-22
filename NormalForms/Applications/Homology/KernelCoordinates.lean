/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.Homology.ChainComplex
import all NormalForms.Matrix.Smith.Algorithm

/-!
# Kernel Coordinates from Strong Smith Normal Form

For the outgoing differential `d_n`, a strong Smith result has

`U * d_n * V = S`.

The columns of `V` after the nonzero Smith prefix form a basis of
`ker d_n`. Consequently `V⁻¹ * d_(n+1)` is the incoming differential in
Smith-domain coordinates. This module proves that its non-kernel prefix is
zero and exposes the remaining coordinate matrix.
-/

public section

namespace NormalForms.Applications.Homology

open scoped Matrix
open NormalForms.Matrix.Smith

namespace IntChainComplex

theorem smithOffDiagonal
    {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (hA : IsSmithNormalFormFin A) :
    ∀ i j, i.1 ≠ j.1 → A i j = 0 := by
  induction hA with
  | emptyRows A =>
      intro i
      exact Fin.elim0 i
  | emptyCols A =>
      intro i j
      exact Fin.elim0 j
  | zeroLead A hzero hrow hcol hLowerZero =>
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              exact False.elim (hij rfl)
          | succ j =>
              exact hrow j
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              exact hcol i
          | succ j =>
              simpa [NormalForms.Matrix.Hermite.lowerRight] using
                congrFun (congrFun hLowerZero i) j
  | pivot A hpivot hnorm hrow hcol hLower hdiv ih =>
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              exact False.elim (hij rfl)
          | succ j =>
              exact hrow j
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              exact hcol i
          | succ j =>
              exact ih i j (by
                intro hEqual
                exact hij (by simp [hEqual]))

/-- Strong Smith result for the outgoing degree-`n` differential. -/
@[expose] public def outgoingSmithResult
    (complex : IntChainComplex) (n : Nat) :
    SNFResultFin (complex.outgoingBoundary n) :=
  smithNormalFormFin (complex.outgoingBoundary n)

/-- Rank of the outgoing differential, including unit Smith factors. -/
@[expose] public noncomputable def outgoingSmithRank
    (complex : IntChainComplex) (n : Nat) : Nat :=
  (complex.outgoingSmithResult n).smithData.rank

/-- Rank of the free kernel of the outgoing differential. -/
@[expose] public noncomputable def kernelRank
    (complex : IntChainComplex) (n : Nat) : Nat :=
  complex.rank n - complex.outgoingSmithRank n

public theorem outgoingSmithRank_le_chainRank
    (complex : IntChainComplex) (n : Nat) :
    complex.outgoingSmithRank n ≤ complex.rank n := by
  exact
    (complex.outgoingSmithResult n).smithData.rank_le.trans
      (Nat.min_le_right _ _)

public theorem outgoingSmithRank_add_kernelRank
    (complex : IntChainComplex) (n : Nat) :
    complex.outgoingSmithRank n + complex.kernelRank n = complex.rank n := by
  exact Nat.add_sub_of_le (complex.outgoingSmithRank_le_chainRank n)

/-- A nonzero-prefix index viewed as an index of the full Smith domain. -/
@[expose] public noncomputable def leadingColumnIndex
    (complex : IntChainComplex) (n : Nat)
    (i : Fin (complex.outgoingSmithRank n)) :
    Fin (complex.rank n) :=
  Fin.castLE (complex.outgoingSmithRank_le_chainRank n) i

/-- A kernel-tail index viewed as an index of the full Smith domain. -/
@[expose] public noncomputable def kernelColumnIndex
    (complex : IntChainComplex) (n : Nat)
    (i : Fin (complex.kernelRank n)) :
    Fin (complex.rank n) :=
  ⟨complex.outgoingSmithRank n + i.1, by
    have hi : i.1 <
        complex.rank n - complex.outgoingSmithRank n :=
      i.is_lt
    omega⟩

@[simp] public theorem leadingColumnIndex_val
    (complex : IntChainComplex) (n : Nat)
    (i : Fin (complex.outgoingSmithRank n)) :
    (complex.leadingColumnIndex n i).1 = i.1 :=
  rfl

@[simp] public theorem kernelColumnIndex_val
    (complex : IntChainComplex) (n : Nat)
    (i : Fin (complex.kernelRank n)) :
    (complex.kernelColumnIndex n i).1 =
      complex.outgoingSmithRank n + i.1 :=
  rfl

/--
Incoming boundary coordinates in the Smith-domain basis of the outgoing
differential.
-/
@[expose] public def incomingSmithCoordinates
    (complex : IntChainComplex) (n : Nat) :
    _root_.Matrix
      (Fin (complex.rank n))
      (Fin (complex.rank (n + 1))) Int :=
  (complex.outgoingSmithResult n).V_cert.inverse *
    complex.incomingBoundary n

/--
The Smith matrix annihilates the incoming coordinate matrix. This is the
coordinate form of `d_n d_(n+1) = 0`.
-/
public theorem smith_mul_incomingSmithCoordinates
    (complex : IntChainComplex) (n : Nat) :
    (complex.outgoingSmithResult n).S *
        complex.incomingSmithCoordinates n =
      0 := by
  let result := complex.outgoingSmithResult n
  rw [incomingSmithCoordinates, ← result.equation]
  calc
    (result.U * complex.outgoingBoundary n * result.V) *
          (result.V_cert.inverse * complex.incomingBoundary n) =
        result.U * complex.outgoingBoundary n *
          (result.V * result.V_cert.inverse) *
            complex.incomingBoundary n := by
              simp only [Matrix.mul_assoc]
    _ = result.U * complex.outgoingBoundary n *
          complex.incomingBoundary n := by
            rw [result.V_cert.right_inv]
            simp
    _ = result.U *
          (complex.outgoingBoundary n * complex.incomingBoundary n) := by
            rw [Matrix.mul_assoc]
    _ = 0 := by
          rw [complex.outgoing_mul_incoming]
          exact Matrix.mul_zero result.U

theorem smithLeadingCoordinate_eq_zero
    (complex : IntChainComplex) (n : Nat)
    (coordinates : Fin (complex.rank n) → Int)
    (annihilated :
      (complex.outgoingSmithResult n).S.mulVec coordinates = 0)
    (i : Fin (complex.outgoingSmithRank n)) :
    coordinates (complex.leadingColumnIndex n i) = 0 := by
  let result := complex.outgoingSmithResult n
  let data := result.smithData
  let diagonalIndex : Fin
      (Nat.min (complex.previousRank n) (complex.rank n)) :=
    Fin.castLE data.rank_le i
  let rowIndex : Fin (complex.previousRank n) :=
    Fin.castLE (Nat.min_le_left _ _) diagonalIndex
  let columnIndex : Fin (complex.rank n) :=
    Fin.castLE (Nat.min_le_right _ _) diagonalIndex
  have hColumn :
      columnIndex = complex.leadingColumnIndex n i := by
    apply Fin.ext
    rfl
  have hDiagonal :
      result.S rowIndex columnIndex = data.diagonal diagonalIndex := by
    rfl
  have hNonzero : result.S rowIndex columnIndex ≠ 0 := by
    rw [hDiagonal]
    exact data.nonzero_prefix diagonalIndex i.is_lt
  have hProduct : result.S.mulVec coordinates rowIndex = 0 := by
    exact congrFun annihilated rowIndex
  simp only [Matrix.mulVec, dotProduct] at hProduct
  have hOffDiagonal := smithOffDiagonal result.isSmith
  have hSum :
      (∑ k, result.S rowIndex k * coordinates k) =
        result.S rowIndex columnIndex * coordinates columnIndex := by
    apply Finset.sum_eq_single columnIndex
    · intro k _ hk
      have hValues : rowIndex.1 ≠ k.1 := by
        intro hEqual
        apply hk
        apply Fin.ext
        change k.1 = diagonalIndex.1
        exact hEqual.symm
      rw [hOffDiagonal rowIndex k hValues]
      simp
    · simp
  rw [hSum] at hProduct
  have hCoordinate : coordinates columnIndex = 0 :=
    (mul_eq_zero.mp hProduct).resolve_left hNonzero
  simpa [hColumn] using hCoordinate

/--
Every coordinate before the kernel tail is zero. Thus no boundary column has
a component outside the Smith kernel basis.
-/
public theorem incomingSmithCoordinates_leading_zero
    (complex : IntChainComplex) (n : Nat)
    (i : Fin (complex.outgoingSmithRank n))
    (j : Fin (complex.rank (n + 1))) :
    complex.incomingSmithCoordinates n
        (complex.leadingColumnIndex n i) j =
      0 := by
  apply smithLeadingCoordinate_eq_zero complex n
    (fun k => complex.incomingSmithCoordinates n k j)
  funext row
  change
    ((complex.outgoingSmithResult n).S *
        complex.incomingSmithCoordinates n) row j =
      0
  rw [complex.smith_mul_incomingSmithCoordinates n]
  rfl

/--
The incoming boundary restricted to the free kernel coordinates of `d_n`.
-/
@[expose] public noncomputable def kernelCoordinateMatrix
    (complex : IntChainComplex) (n : Nat) :
    _root_.Matrix
      (Fin (complex.kernelRank n))
      (Fin (complex.rank (n + 1))) Int :=
  fun i j =>
    complex.incomingSmithCoordinates n
      (complex.kernelColumnIndex n i) j

@[simp] public theorem kernelCoordinateMatrix_apply
    (complex : IntChainComplex) (n : Nat)
    (i : Fin (complex.kernelRank n))
    (j : Fin (complex.rank (n + 1))) :
    complex.kernelCoordinateMatrix n i j =
      complex.incomingSmithCoordinates n
        (complex.kernelColumnIndex n i) j :=
  rfl

/-- The degree-`n` homology presentation in the explicit Smith kernel basis. -/
@[expose] public noncomputable def homologyPresentation
    (complex : IntChainComplex) (n : Nat) :
    FiniteFreePresentation Int where
  numGenerators := complex.kernelRank n
  numRelations := complex.rank (n + 1)
  relationMatrix := complex.kernelCoordinateMatrix n

@[simp] public theorem homologyPresentation_numGenerators
    (complex : IntChainComplex) (n : Nat) :
    (complex.homologyPresentation n).numGenerators =
      complex.kernelRank n :=
  rfl

@[simp] public theorem homologyPresentation_numRelations
    (complex : IntChainComplex) (n : Nat) :
    (complex.homologyPresentation n).numRelations =
      complex.rank (n + 1) :=
  rfl

@[simp] public theorem homologyPresentation_relationMatrix
    (complex : IntChainComplex) (n : Nat) :
    (complex.homologyPresentation n).relationMatrix =
      complex.kernelCoordinateMatrix n :=
  rfl

end IntChainComplex

end NormalForms.Applications.Homology
