/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalPreparation
public import NormalForms.Research.KannanBachem.Hermite.PrincipalBitComplexity
import all NormalForms.Research.KannanBachem.Hermite.PrincipalPolynomialBound

/-!
# Bit Complexity of the Prepared Principal Kernel

The deterministic row preparation removes the public `PrincipalReady`
precondition from the principal-kernel bound. The preparation now scans every
candidate minor through the certified charged Bird evaluator. This module
accumulates the actual scan charges across the recursive permutation, proves a
closed bound in the original input width, and composes it with the principal
kernel cost.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

namespace Principal

open DivisionFreeDeterminant

public theorem principalPolynomialBitLengthBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    principalPolynomialBitLengthBound dimension smaller ≤
      principalPolynomialBitLengthBound dimension larger := by
  unfold principalPolynomialBitLengthBound stageBoundaryPolynomialBits
  apply Nat.add_le_add
  · omega
  · apply stagePolynomialBitLengthBound_mono le_rfl
    gcongr

public theorem principalTransitionBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    principalTransitionBitOperationBound dimension smaller ≤
      principalTransitionBitOperationBound dimension larger := by
  unfold principalTransitionBitOperationBound
    principalXGCDTransitionBitOperationBound
    principalDivModTransitionBitOperationBound
    principalNormalizeTransitionBitOperationBound
    principalRowCoefficientBitLengthBound
    boundedIntXGCDUniformBitOperationBound
    NormalForms.Research.BitCost.boundedXGCDStepCostBound
    NormalForms.Research.BitCost.boundedXGCDEuclideanUpdateCostBound
    NormalForms.Research.BitCost.boundedXGCDReductionCostBound
    NormalForms.Research.BitCost.boundedXGCDRawCoefficientBitLengthBound
    NormalForms.Research.BitCost.boundedXGCDCoefficientBitLengthBound
    integerDivModBitOperationBound
    NormalForms.Research.BitCost.divisionCostForBitLengths
    NormalForms.Research.BitCost.multiplicationCostForBitLengths
    NormalForms.Research.BitCost.additionCostForBitLengths
  dsimp only
  gcongr

/-- Actual charged determinant work performed by recursive preparation. -/
@[expose] public def preparationDeterminantScanBitOperationCost :
    {n : Nat} →
      (A : _root_.Matrix (Fin n) (Fin n) Int) → A.det ≠ 0 → Nat
  | 0, _A, _hdet => 0
  | _n + 1, A, hdet =>
      let pivot := lastColumnPivot A hdet
      let minor := lastColumnMinor A pivot
      let minorNonzero := lastColumnPivot_spec A hdet
      (lastColumnScan A).cost +
        preparationDeterminantScanBitOperationCost minor minorNonzero

/-- Closed recursive budget for all preparation determinant scans. -/
@[expose] public def preparationDeterminantScanBitOperationBound :
    Nat → Nat → Nat
  | 0, _inputBits => 0
  | n + 1, inputBits =>
      (n + 1) *
          (determinantBitOperationBound n inputBits + 1) +
        preparationDeterminantScanBitOperationBound n inputBits

public theorem preparationDeterminantScanBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    preparationDeterminantScanBitOperationBound dimension smaller ≤
      preparationDeterminantScanBitOperationBound dimension larger := by
  induction dimension with
  | zero => simp [preparationDeterminantScanBitOperationBound]
  | succ dimension ih =>
      rw [preparationDeterminantScanBitOperationBound,
        preparationDeterminantScanBitOperationBound]
      exact Nat.add_le_add
        (Nat.mul_le_mul_left (dimension + 1)
          (Nat.add_le_add_right
            (determinantBitOperationBound_mono_right dimension hle) 1))
        ih

/-- The recursive scan budget is bounded by one uniform quadratic scan count. -/
public theorem preparationDeterminantScanBitOperationBound_le_closed
    (dimension inputBits : Nat) :
    preparationDeterminantScanBitOperationBound dimension inputBits ≤
      dimension * dimension *
        (determinantBitOperationBound dimension inputBits + 1) := by
  induction dimension with
  | zero => simp [preparationDeterminantScanBitOperationBound]
  | succ dimension ih =>
      rw [preparationDeterminantScanBitOperationBound]
      let uniform :=
        determinantBitOperationBound (dimension + 1) inputBits + 1
      have determinantMono :
          determinantBitOperationBound dimension inputBits + 1 ≤ uniform :=
        Nat.add_le_add_right
          (determinantBitOperationBound_mono_dimension inputBits
            (Nat.le_succ dimension)) 1
      have recursiveMono :
          dimension * dimension *
              (determinantBitOperationBound dimension inputBits + 1) ≤
            dimension * dimension * uniform := by
        gcongr
      calc
        (dimension + 1) *
              (determinantBitOperationBound dimension inputBits + 1) +
            preparationDeterminantScanBitOperationBound dimension inputBits ≤
          (dimension + 1) * uniform +
            dimension * dimension * uniform :=
          Nat.add_le_add (Nat.mul_le_mul_left _ determinantMono)
            (ih.trans recursiveMono)
        _ ≤ (dimension + 1) * (dimension + 1) * uniform := by
          nlinarith

/-- Every recursive charged scan stays within the original input-width bound. -/
public theorem preparationDeterminantScanBitOperationCost_le :
    {n : Nat} →
      (A : _root_.Matrix (Fin n) (Fin n) Int) →
        (hdet : A.det ≠ 0) →
          preparationDeterminantScanBitOperationCost A hdet ≤
            preparationDeterminantScanBitOperationBound n
              (matrixBitLength A)
  | 0, A, hdet => by
      simp [preparationDeterminantScanBitOperationCost,
        preparationDeterminantScanBitOperationBound]
  | n + 1, A, hdet => by
      let pivot := lastColumnPivot A hdet
      let minor := lastColumnMinor A pivot
      let minorNonzero : minor.det ≠ 0 := lastColumnPivot_spec A hdet
      have currentCost := lastColumnScan_cost_le A
      have recursiveCost :=
        preparationDeterminantScanBitOperationCost_le minor minorNonzero
      have minorWidth : matrixBitLength minor ≤ matrixBitLength A := by
        exact submatrix_bitLength_le A pivot.succAbove
          (Fin.last n).succAbove
      rw [preparationDeterminantScanBitOperationCost,
        preparationDeterminantScanBitOperationBound]
      change (lastColumnScan A).cost +
          preparationDeterminantScanBitOperationCost minor minorNonzero ≤ _
      calc
        (lastColumnScan A).cost +
              preparationDeterminantScanBitOperationCost minor minorNonzero ≤
            (n + 1) *
                (determinantBitOperationBound n (matrixBitLength A) + 1) +
              preparationDeterminantScanBitOperationBound n
                (matrixBitLength minor) :=
          Nat.add_le_add currentCost recursiveCost
        _ ≤ (n + 1) *
                (determinantBitOperationBound n (matrixBitLength A) + 1) +
              preparationDeterminantScanBitOperationBound n
                (matrixBitLength A) :=
          Nat.add_le_add_left
            (preparationDeterminantScanBitOperationBound_mono_right n
              minorWidth) _

end Principal

public theorem principalHNFBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    principalHNFBitOperationBound dimension smaller ≤
      principalHNFBitOperationBound dimension larger := by
  unfold principalHNFBitOperationBound
  apply Nat.mul_le_mul_left
  apply Principal.principalTransitionBitOperationBound_mono_right
  exact Principal.principalPolynomialBitLengthBound_mono_right dimension hle

public theorem prepare_matrixBitLength_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    matrixBitLength (Principal.prepare A hdet).matrix ≤ matrixBitLength A :=
  submatrix_bitLength_le A (Principal.prepare A hdet).rowPermutation id

/-- The prepared principal kernel has a closed bound for every nonsingular input. -/
public theorem preparedPrincipalKernelBitOperationCost_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    principalHNFBitOperationCost (Principal.prepare A hdet).matrix ≤
      principalHNFBitOperationBound n (matrixBitLength A) := by
  exact
    (principalHNFBitOperationCost_le_of_ready
      (Principal.prepare A hdet).matrix (Principal.prepare A hdet).ready).trans
      (principalHNFBitOperationBound_mono_right n
        (prepare_matrixBitLength_le A hdet))

/-- Determinant-scan arithmetic plus the prepared principal-kernel arithmetic. -/
@[expose] public def preparedPrincipalHNFBitOperationCost {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) : Nat :=
  Principal.preparationDeterminantScanBitOperationCost A hdet +
    principalHNFBitOperationCost (Principal.prepare A hdet).matrix

/-- Closed end-to-end arithmetic budget for prepared nonsingular HNF. -/
@[expose] public def preparedPrincipalHNFBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  dimension * dimension *
      (DivisionFreeDeterminant.determinantBitOperationBound
        dimension inputBits + 1) +
    principalHNFBitOperationBound dimension inputBits

/-- The complete preparation-plus-kernel arithmetic cost is polynomially bounded. -/
public theorem preparedPrincipalHNFBitOperationCost_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    preparedPrincipalHNFBitOperationCost A hdet ≤
      preparedPrincipalHNFBitOperationBound n (matrixBitLength A) :=
  Nat.add_le_add
    ((Principal.preparationDeterminantScanBitOperationCost_le A hdet).trans
      (Principal.preparationDeterminantScanBitOperationBound_le_closed n
        (matrixBitLength A)))
    (preparedPrincipalKernelBitOperationCost_le A hdet)

end NormalForms.Research.KannanBachem.Hermite
