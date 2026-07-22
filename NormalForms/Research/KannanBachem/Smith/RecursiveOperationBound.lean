/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.Recursive
public import NormalForms.Research.KannanBachem.Smith.OperationBound
import all NormalForms.Research.KannanBachem.Hermite.PrincipalPolynomialBound

/-!
# Polynomial Ring-operation Bound for Kannan--Bachem SNF

The exact counter mirrors total square Smith recursion.  Determinant magnitude
is invariant under every certified two-sided transform, while each recursive
lower-right determinant is no larger.  Consequently all active dimensions
share the original determinant-width budget.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms.Matrix.Hermite
open NormalForms.Research.KannanBachem.Hermite

/-- Removing a nonzero stable pivot cannot increase determinant magnitude. -/
public theorem lowerRight_det_natAbs_le_of_stable {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (stable : StablePivot A) :
    (lowerRight A).det.natAbs ≤ A.det.natAbs := by
  rw [det_eq_pivot_mul_lowerRight A stable.firstRowCleared,
    Int.natAbs_mul]
  exact Nat.le_mul_of_pos_left _
    (Int.natAbs_pos.mpr stable.pivot_ne_zero)

/-- One stabilized lower-right block is bounded by the input determinant. -/
public theorem stabilization_lowerRight_det_natAbs_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (lowerRight (stabilize A hdet).certificate.result).det.natAbs ≤
      A.det.natAbs := by
  calc
    (lowerRight (stabilize A hdet).certificate.result).det.natAbs ≤
        (stabilize A hdet).certificate.result.det.natAbs :=
      lowerRight_det_natAbs_le_of_stable _ (stabilize A hdet).stable
    _ = A.det.natAbs :=
      certificate_result_det_natAbs (stabilize A hdet).certificate

/-- Exact algebraic charge following the same recursion as `smith`. -/
@[expose] public def smithOperationCount : {n : Nat} →
    (A : _root_.Matrix (Fin n) (Fin n) Int) → A.det ≠ 0 →
      SmithOperationCount
  | 0, _A, _hdet => {}
  | _n + 1, A, hdet =>
      let stabilized := stabilize A hdet
      let transformed := stabilized.certificate.result
      let transformedDet : transformed.det ≠ 0 :=
        stabilized.result_det_ne_zero hdet
      let lowerDet : (lowerRight transformed).det ≠ 0 :=
        stable_lowerRight_det_ne_zero transformed stabilized.stable
          transformedDet
      (stabilizeOperationCount A hdet).add <|
        smithOperationCount (lowerRight transformed) lowerDet

/-- Determinant-sensitive closed bound for the exact recursive count. -/
@[expose] public def smithRingOperationBound
    (dimension inputBits : Nat) : Nat :=
  dimension * (inputBits + 1) *
    stabilizationLevelOperationBound dimension

/-- Full square SNF uses polynomially many ring and Euclidean primitives. -/
public theorem smithOperationCount_total_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smithOperationCount A hdet).total ≤
      smithRingOperationBound n (integerBitLength A.det) := by
  induction n with
  | zero =>
      simp [smithOperationCount, smithRingOperationBound,
        SmithOperationCount.total]
  | succ n ih =>
      rw [smithOperationCount, SmithOperationCount.total_add]
      let stabilized := stabilize A hdet
      let transformed := stabilized.certificate.result
      let transformedDet : transformed.det ≠ 0 :=
        stabilized.result_det_ne_zero hdet
      let lowerDet : (lowerRight transformed).det ≠ 0 :=
        stable_lowerRight_det_ne_zero transformed stabilized.stable
          transformedDet
      have topBound := stabilizeOperationCount_total_le A hdet
      have lowerBitLength :
          integerBitLength (lowerRight transformed).det ≤
            integerBitLength A.det :=
        Nat.size_le_size (by
          dsimp only [transformed, stabilized]
          exact stabilization_lowerRight_det_natAbs_le A hdet)
      have recursiveBound := ih (lowerRight transformed) lowerDet
      have recursiveUniform :
          (smithOperationCount (lowerRight transformed) lowerDet).total ≤
            n * (integerBitLength A.det + 1) *
              stabilizationLevelOperationBound (n + 1) := by
        refine recursiveBound.trans ?_
        unfold smithRingOperationBound
        gcongr
        exact stabilizationLevelOperationBound_mono (Nat.le_succ n)
      unfold smithRingOperationBound
      calc
        (stabilizeOperationCount A hdet).total +
              (smithOperationCount (lowerRight transformed) lowerDet).total ≤
            (integerBitLength A.det + 1) *
                stabilizationLevelOperationBound (n + 1) +
              n * (integerBitLength A.det + 1) *
                stabilizationLevelOperationBound (n + 1) :=
          Nat.add_le_add topBound recursiveUniform
        _ = (n + 1) * (integerBitLength A.det + 1) *
              stabilizationLevelOperationBound (n + 1) := by ring

/-- Expanded polynomial in dimension and the original input coefficient width. -/
@[expose] public def smithPolynomialRingOperationBound
    (dimension inputBits : Nat) : Nat :=
  dimension * (dimension * (dimension + inputBits) + 3) *
    stabilizationLevelPolynomialBound dimension

/-- Input-size form of the full polynomial ring-operation theorem. -/
public theorem smithOperationCount_total_le_polynomial {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smithOperationCount A hdet).total ≤
      smithPolynomialRingOperationBound n (matrixBitLength A) := by
  refine (smithOperationCount_total_le A hdet).trans ?_
  have determinantBits :
      integerBitLength A.det + 1 ≤
        n * (n + matrixBitLength A) + 3 := by
    have direct := determinant_bitLength_le A
    have polynomial :=
      Principal.determinantBitLengthBound_le_polynomial
        n (matrixBitLength A)
    omega
  unfold smithRingOperationBound smithPolynomialRingOperationBound
  exact Nat.mul_le_mul
    (Nat.mul_le_mul_left n determinantBits)
    (stabilizationLevelOperationBound_le_polynomial n)

end NormalForms.Research.KannanBachem.Smith
