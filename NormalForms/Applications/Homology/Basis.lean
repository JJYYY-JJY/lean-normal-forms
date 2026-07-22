/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.Homology.KernelCoordinates

/-!
# Explicit Kernel Bases

The tail columns of the right Smith transform give an explicit integral basis
of the outgoing kernel. This module packages that statement as a linear
equivalence and identifies the incoming boundary with
`kernelCoordinateMatrix`.
-/

public section

namespace NormalForms.Applications.Homology

open scoped Matrix
open NormalForms.Matrix.Smith

namespace IntChainComplex

/--
Extend a vector of kernel-tail coordinates by a zero nonzero-Smith prefix.
-/
@[expose] public noncomputable def extendKernelCoordinates
    (complex : IntChainComplex) (n : Nat)
    (coordinates : Fin (complex.kernelRank n) → Int) :
    Fin (complex.rank n) → Int :=
  fun i =>
    if hi : i.1 < complex.outgoingSmithRank n then
      0
    else
      coordinates
        ⟨i.1 - complex.outgoingSmithRank n, by
          have hr := complex.outgoingSmithRank_le_chainRank n
          have hi' := i.is_lt
          simp only [kernelRank]
          omega⟩

/-- Restrict full Smith-domain coordinates to their kernel tail. -/
@[expose] public noncomputable def restrictKernelCoordinates
    (complex : IntChainComplex) (n : Nat)
    (coordinates : Fin (complex.rank n) → Int) :
    Fin (complex.kernelRank n) → Int :=
  fun i => coordinates (complex.kernelColumnIndex n i)

@[simp] public theorem extendKernelCoordinates_leading
    (complex : IntChainComplex) (n : Nat)
    (coordinates : Fin (complex.kernelRank n) → Int)
    (i : Fin (complex.outgoingSmithRank n)) :
    complex.extendKernelCoordinates n coordinates
        (complex.leadingColumnIndex n i) =
      0 := by
  simp [extendKernelCoordinates]

@[simp] public theorem extendKernelCoordinates_kernel
    (complex : IntChainComplex) (n : Nat)
    (coordinates : Fin (complex.kernelRank n) → Int)
    (i : Fin (complex.kernelRank n)) :
    complex.extendKernelCoordinates n coordinates
        (complex.kernelColumnIndex n i) =
      coordinates i := by
  simp only [extendKernelCoordinates, kernelColumnIndex_val]
  rw [dif_neg (by omega)]
  apply congrArg coordinates
  apply Fin.ext
  exact Nat.add_sub_cancel_left (complex.outgoingSmithRank n) i.1

@[simp] public theorem restrict_extendKernelCoordinates
    (complex : IntChainComplex) (n : Nat)
    (coordinates : Fin (complex.kernelRank n) → Int) :
    complex.restrictKernelCoordinates n
        (complex.extendKernelCoordinates n coordinates) =
      coordinates := by
  funext i
  exact complex.extendKernelCoordinates_kernel n coordinates i

public theorem extend_restrictKernelCoordinates
    (complex : IntChainComplex) (n : Nat)
    (coordinates : Fin (complex.rank n) → Int)
    (leadingZero :
      ∀ i : Fin (complex.outgoingSmithRank n),
        coordinates (complex.leadingColumnIndex n i) = 0) :
    complex.extendKernelCoordinates n
        (complex.restrictKernelCoordinates n coordinates) =
      coordinates := by
  funext i
  by_cases hi : i.1 < complex.outgoingSmithRank n
  · let leading : Fin (complex.outgoingSmithRank n) := ⟨i.1, hi⟩
    have hIndex : complex.leadingColumnIndex n leading = i := by
      apply Fin.ext
      rfl
    simp only [extendKernelCoordinates, hi, dif_pos]
    simpa [hIndex] using (leadingZero leading).symm
  · rw [extendKernelCoordinates, dif_neg hi]
    change
      coordinates
          (complex.kernelColumnIndex n
            ⟨i.1 - complex.outgoingSmithRank n, _⟩) =
        coordinates i
    apply congrArg coordinates
    apply Fin.ext
    simp only [kernelColumnIndex_val]
    omega

private theorem smithTailColumnZero
    (complex : IntChainComplex) (n : Nat)
    (row : Fin (complex.previousRank n))
    (column : Fin (complex.rank n))
    (rank_le_column :
      complex.outgoingSmithRank n ≤ column.1) :
    (complex.outgoingSmithResult n).S row column = 0 := by
  let result := complex.outgoingSmithResult n
  let data := result.smithData
  change result.S row column = 0
  by_cases hValues : row.1 = column.1
  · have hColumnPrevious : column.1 < complex.previousRank n := by
      simpa [hValues] using row.is_lt
    let diagonalIndex :
        Fin (Nat.min (complex.previousRank n) (complex.rank n)) :=
      ⟨column.1, lt_min hColumnPrevious column.is_lt⟩
    have hzero := data.zero_tail diagonalIndex rank_le_column
    change
      result.S
          (Fin.castLE (Nat.min_le_left _ _) diagonalIndex)
          (Fin.castLE (Nat.min_le_right _ _) diagonalIndex) =
        0 at hzero
    have hRow :
        row = Fin.castLE (Nat.min_le_left _ _) diagonalIndex := by
      apply Fin.ext
      exact hValues
    have hColumn :
        column = Fin.castLE (Nat.min_le_right _ _) diagonalIndex := by
      apply Fin.ext
      rfl
    rw [hRow, hColumn]
    exact hzero
  · exact smithOffDiagonal result.isSmith row column hValues

private theorem smith_mul_extendKernelCoordinates
    (complex : IntChainComplex) (n : Nat)
    (coordinates : Fin (complex.kernelRank n) → Int) :
    (complex.outgoingSmithResult n).S.mulVec
        (complex.extendKernelCoordinates n coordinates) =
      0 := by
  funext row
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro column _
  by_cases hLeading :
      column.1 < complex.outgoingSmithRank n
  · rw [show
        complex.extendKernelCoordinates n coordinates column = 0 by
          simp [extendKernelCoordinates, hLeading]]
    simp
  · rw [smithTailColumnZero complex n row column
      (Nat.le_of_not_gt hLeading)]
    simp

/--
The outgoing differential followed by the Smith-domain basis change equals
the Smith matrix after the certified left inverse.
-/
public theorem outgoing_mul_smithBasis
    (complex : IntChainComplex) (n : Nat) :
    complex.outgoingBoundary n *
        (complex.outgoingSmithResult n).V =
      (complex.outgoingSmithResult n).U_cert.inverse *
        (complex.outgoingSmithResult n).S := by
  let result := complex.outgoingSmithResult n
  calc
    complex.outgoingBoundary n * result.V =
        (result.U_cert.inverse * result.U) *
          (complex.outgoingBoundary n * result.V) := by
            rw [result.U_cert.left_inv, Matrix.one_mul]
    _ = result.U_cert.inverse *
          (result.U * complex.outgoingBoundary n * result.V) := by
            simp only [Matrix.mul_assoc]
    _ = result.U_cert.inverse * result.S := by
          rw [result.equation]

/-- Linear zero-prefix extension into the full Smith-domain coordinates. -/
@[expose] public noncomputable def extendKernelCoordinatesLinearMap
    (complex : IntChainComplex) (n : Nat) :
    (Fin (complex.kernelRank n) → Int) →ₗ[Int]
      (Fin (complex.rank n) → Int) where
  toFun := complex.extendKernelCoordinates n
  map_add' left right := by
    funext i
    by_cases hi : i.1 < complex.outgoingSmithRank n <;>
      simp [extendKernelCoordinates, hi]
  map_smul' scalar coordinates := by
    funext i
    by_cases hi : i.1 < complex.outgoingSmithRank n <;>
      simp [extendKernelCoordinates, hi]

/-- Linear restriction from full Smith coordinates to their kernel tail. -/
@[expose] public noncomputable def restrictKernelCoordinatesLinearMap
    (complex : IntChainComplex) (n : Nat) :
    (Fin (complex.rank n) → Int) →ₗ[Int]
      (Fin (complex.kernelRank n) → Int) where
  toFun := complex.restrictKernelCoordinates n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
The explicit kernel-basis map: extend by zero in Smith coordinates, then
multiply by the certified right transform `V`.
-/
@[expose] public noncomputable def kernelBasisLinearMap
    (complex : IntChainComplex) (n : Nat) :
    (Fin (complex.kernelRank n) → Int) →ₗ[Int] complex.cycles n :=
  LinearMap.codRestrict
    (complex.cycles n)
    ((complex.outgoingSmithResult n).V.mulVecLin.comp
      (complex.extendKernelCoordinatesLinearMap n))
    (by
      intro coordinates
      change
        (complex.outgoingBoundary n).mulVec
            ((complex.outgoingSmithResult n).V.mulVec
              (complex.extendKernelCoordinates n coordinates)) =
          0
      calc
        (complex.outgoingBoundary n).mulVec
            ((complex.outgoingSmithResult n).V.mulVec
              (complex.extendKernelCoordinates n coordinates)) =
            (complex.outgoingBoundary n *
              (complex.outgoingSmithResult n).V).mulVec
                (complex.extendKernelCoordinates n coordinates) :=
                  Matrix.mulVec_mulVec _ _ _
        _ = ((complex.outgoingSmithResult n).U_cert.inverse *
              (complex.outgoingSmithResult n).S).mulVec
                (complex.extendKernelCoordinates n coordinates) := by
                  rw [complex.outgoing_mul_smithBasis n]
        _ = (complex.outgoingSmithResult n).U_cert.inverse.mulVec
              ((complex.outgoingSmithResult n).S.mulVec
                (complex.extendKernelCoordinates n coordinates)) :=
                  (Matrix.mulVec_mulVec _ _ _).symm
        _ = 0 := by
              rw [smith_mul_extendKernelCoordinates]
              exact Matrix.mulVec_zero _)

/-- Read kernel-tail coordinates from a cycle using the certified `V⁻¹`. -/
@[expose] public noncomputable def kernelBasisInverseLinearMap
    (complex : IntChainComplex) (n : Nat) :
    complex.cycles n →ₗ[Int]
      (Fin (complex.kernelRank n) → Int) :=
  (complex.restrictKernelCoordinatesLinearMap n).comp
    ((complex.outgoingSmithResult n).V_cert.inverse.mulVecLin.comp
      (complex.cycles n).subtype)

private theorem cycleSmithCoordinatesLeadingZero
    (complex : IntChainComplex) (n : Nat)
    (cycle : complex.cycles n)
    (i : Fin (complex.outgoingSmithRank n)) :
    ((complex.outgoingSmithResult n).V_cert.inverse.mulVec cycle.1)
        (complex.leadingColumnIndex n i) =
      0 := by
  apply smithLeadingCoordinate_eq_zero complex n
  let result := complex.outgoingSmithResult n
  calc
    result.S.mulVec (result.V_cert.inverse.mulVec cycle.1) =
        (result.S * result.V_cert.inverse).mulVec cycle.1 :=
          Matrix.mulVec_mulVec _ _ _
    _ = ((result.U * complex.outgoingBoundary n * result.V) *
          result.V_cert.inverse).mulVec cycle.1 := by
            rw [result.equation]
    _ = (result.U * complex.outgoingBoundary n *
          (result.V * result.V_cert.inverse)).mulVec cycle.1 := by
            simp only [Matrix.mul_assoc]
    _ = (result.U * complex.outgoingBoundary n).mulVec cycle.1 := by
          rw [result.V_cert.right_inv, Matrix.mul_one]
    _ = result.U.mulVec
          ((complex.outgoingBoundary n).mulVec cycle.1) :=
            (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by
          have hCycle := cycle.property
          change
            (complex.outgoingBoundary n).mulVec cycle.1 = 0
              at hCycle
          rw [hCycle]
          exact Matrix.mulVec_zero result.U

/--
The tail columns of `V` form an explicit integral basis of `ker d_n`.
-/
@[expose] public noncomputable def kernelBasisEquiv
    (complex : IntChainComplex) (n : Nat) :
    (Fin (complex.kernelRank n) → Int) ≃ₗ[Int] complex.cycles n where
  toFun := complex.kernelBasisLinearMap n
  invFun := complex.kernelBasisInverseLinearMap n
  map_add' := (complex.kernelBasisLinearMap n).map_add
  map_smul' := (complex.kernelBasisLinearMap n).map_smul
  left_inv coordinates := by
    change
      complex.restrictKernelCoordinates n
          ((complex.outgoingSmithResult n).V_cert.inverse.mulVec
            ((complex.outgoingSmithResult n).V.mulVec
              (complex.extendKernelCoordinates n coordinates))) =
        coordinates
    rw [Matrix.mulVec_mulVec,
      (complex.outgoingSmithResult n).V_cert.left_inv,
      Matrix.one_mulVec]
    exact complex.restrict_extendKernelCoordinates n coordinates
  right_inv cycle := by
    apply Subtype.ext
    change
      (complex.outgoingSmithResult n).V.mulVec
          (complex.extendKernelCoordinates n
            (complex.restrictKernelCoordinates n
              ((complex.outgoingSmithResult n).V_cert.inverse.mulVec
                cycle.1))) =
        cycle.1
    rw [complex.extend_restrictKernelCoordinates n
      ((complex.outgoingSmithResult n).V_cert.inverse.mulVec cycle.1)
      (complex.cycleSmithCoordinatesLeadingZero n cycle)]
    rw [Matrix.mulVec_mulVec,
      (complex.outgoingSmithResult n).V_cert.right_inv,
      Matrix.one_mulVec]

/--
In the explicit kernel basis, the incoming boundary map is exactly
`kernelCoordinateMatrix`.
-/
public theorem kernelBasisEquiv_symm_boundary
    (complex : IntChainComplex) (n : Nat)
    (vector : Fin (complex.rank (n + 1)) → Int) :
    (complex.kernelBasisEquiv n).symm
        (complex.boundaryCycleMap n vector) =
      (complex.kernelCoordinateMatrix n).mulVec vector := by
  change
    complex.restrictKernelCoordinates n
        ((complex.outgoingSmithResult n).V_cert.inverse.mulVec
          ((complex.incomingBoundary n).mulVec vector)) =
      (complex.kernelCoordinateMatrix n).mulVec vector
  funext i
  change
    ((complex.outgoingSmithResult n).V_cert.inverse.mulVec
        ((complex.incomingBoundary n).mulVec vector))
        (complex.kernelColumnIndex n i) =
      (complex.kernelCoordinateMatrix n).mulVec vector i
  rw [Matrix.mulVec_mulVec]
  rfl

end IntChainComplex

end NormalForms.Applications.Homology
