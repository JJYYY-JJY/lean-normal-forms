/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.BoundedColumnSize
public import NormalForms.Research.KannanBachem.Smith.Totality
import all NormalForms.Research.KannanBachem.Smith.BoundedColumn
import all NormalForms.Research.KannanBachem.Smith.PassCorrectness
import all NormalForms.Research.KannanBachem.Smith.Clear
import all NormalForms.Research.KannanBachem.Smith.Totality
import all NormalForms.Research.KannanBachem.Hermite.PrincipalMultiplierBound

/-!
# Polynomial coefficient bounds for Kannan--Bachem stabilization

This layer bounds every Step-4 coefficient, both explicit transformation
inverses, every pass, and the complete well-founded pivot-stabilization loop.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Research.KannanBachem.Hermite

theorem matrixHeight_transpose {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    matrixHeight A.transpose = matrixHeight A := by
  apply le_antisymm
  · apply matrixHeight_le
    intro row column
    exact entry_natAbs_le_matrixHeight A column row
  · apply matrixHeight_le
    intro row column
    exact entry_natAbs_le_matrixHeight A.transpose column row

theorem matrixBitLength_transpose {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    matrixBitLength A.transpose = matrixBitLength A := by
  simp [matrixBitLength, matrixHeight_transpose]

theorem preparation_det_natAbs {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (Principal.prepare A hdet).matrix.det.natAbs = A.det.natAbs := by
  rw [Principal.Preparation.matrix, Matrix.det_permute, Int.natAbs_mul]
  simp only [Int.cast_id]
  rw [Int.units_natAbs, one_mul]

theorem preparedPrincipal_result_height_le_input_det {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    matrixHeight (Principal.preparedPrincipalHermiteNormalForm A hdet).H ≤
      A.det.natAbs := by
  let preparation := Principal.prepare A hdet
  have core := principal_result_height_le_input_det preparation.matrix
    (preparation.det_ne hdet)
  change matrixHeight (principalRun preparation.matrix).matrix ≤ A.det.natAbs
  exact core.trans_eq (preparation_det_natAbs A hdet)

theorem preparedPrincipal_result_bitLength_le_input_det {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    matrixBitLength (Principal.preparedPrincipalHermiteNormalForm A hdet).H ≤
      integerBitLength A.det := by
  exact Nat.size_le_size (preparedPrincipal_result_height_le_input_det A hdet)

theorem rightHermitePhase_result_bitLength_le_input_det {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0) :
    matrixBitLength (rightHermitePhase A hdet).result ≤
      integerBitLength A.det := by
  simpa [rightHermitePhase, rightHermiteResult, matrixBitLength_transpose] using
    preparedPrincipal_result_bitLength_le_input_det A.transpose (by simpa using hdet)

theorem pass_result_bitLength_le_determinant {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0) :
    matrixBitLength (pass A hdet).result ≤ integerBitLength A.det := by
  let left := leftHermitePhase A
  have right := rightHermitePhase_result_bitLength_le_input_det left.result
    (result_det_ne_zero left hdet)
  exact right.trans_eq <| congrArg Nat.size (certificate_result_det_natAbs left)

@[expose] def preparedMultiplierBits
    (order inputBits determinantBits : Nat) : Nat :=
  Nat.size (order + 1) + determinantBits +
    determinantBitLengthBound order inputBits

@[expose] def preparedInverseBits
    (order inputBits determinantBits : Nat) : Nat :=
  Nat.size (order + 1) + inputBits +
    determinantBitLengthBound order determinantBits

theorem preparedPrincipal_multiplier_bitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0) :
    matrixBitLength (Principal.preparedPrincipalHermiteNormalForm A hdet).U ≤
      preparedMultiplierBits n (matrixBitLength A) (integerBitLength A.det) := by
  let result := Principal.preparedPrincipalHermiteNormalForm A hdet
  have resultBits : matrixBitLength result.H ≤ integerBitLength A.det := by
    simpa [result] using preparedPrincipal_result_bitLength_le_input_det A hdet
  have cramer := leftMultiplier_bitLength_le_of_mul_eq
    A result.U result.H result.equation hdet
  exact cramer.trans <| by
    unfold preparedMultiplierBits
    omega

theorem preparedPrincipal_inverse_bitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0) :
    matrixBitLength
        (Principal.preparedPrincipalHermiteNormalForm A hdet).U_cert.inverse ≤
      preparedInverseBits n (matrixBitLength A) (integerBitLength A.det) := by
  let result := Principal.preparedPrincipalHermiteNormalForm A hdet
  have resultBits : matrixBitLength result.H ≤ integerBitLength A.det := by
    simpa [result] using preparedPrincipal_result_bitLength_le_input_det A hdet
  have inverseEquation := Principal.preparedPrincipalHermiteNormalForm_inverse_equation
    A hdet
  have resultDet : result.H.det ≠ 0 := by
    intro resultDetZero
    apply hdet
    rw [← inverseEquation, Matrix.det_mul, resultDetZero, mul_zero]
  have cramer := leftMultiplier_bitLength_le_of_mul_eq
    result.H result.U_cert.inverse A inverseEquation resultDet
  have determinantBits :
      determinantBitLengthBound n (matrixBitLength result.H) ≤
        determinantBitLengthBound n (integerBitLength A.det) := by
    unfold determinantBitLengthBound
    gcongr
  exact cramer.trans <| by
    unfold preparedInverseBits
    omega

@[expose] def certificateTransformBitLength {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (certificate : TwoSidedCertificate A) : Nat :=
  max (matrixBitLength certificate.U)
    (max (matrixBitLength certificate.U_cert.inverse)
      (max (matrixBitLength certificate.V)
        (matrixBitLength certificate.V_cert.inverse)))

@[expose] def passTransformBitLengthBound
    (order inputBits determinantBits : Nat) : Nat :=
  max
    (boundedColumnMultiplierPolynomialBitLengthBound (order + 1) inputBits)
    (max
      (boundedColumnInversePolynomialBitLengthBound (order + 1) inputBits)
      (max (preparedMultiplierBits order
          (boundedColumnIntermediatePolynomialBitLengthBound (order + 1) inputBits)
          determinantBits)
        (preparedInverseBits order
          (boundedColumnIntermediatePolynomialBitLengthBound (order + 1) inputBits)
          determinantBits)))

theorem boundedColumn_result_U_bitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0) :
    matrixBitLength (leftHermiteResult A).U ≤
      boundedColumnMultiplierPolynomialBitLengthBound
        (n + 1) (matrixBitLength A) := by
  have prefixHeight := RowTrace.accumulator_height_le_intermediateMultiplierHeight
    (boundedColumnTrace A)
  have prefixBits := Nat.size_le_size prefixHeight
  have allBits := boundedColumnIntermediateMultiplierBitLength_le_polynomial A hdet
  change matrixBitLength (BoundedColumn.compute A).U ≤ _
  rw [← (BoundedColumn.compute A).accumulator_eq]
  exact prefixBits.trans allBits

theorem boundedColumn_result_inverse_bitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0) :
    matrixBitLength (leftHermiteResult A).U_cert.inverse ≤
      boundedColumnInversePolynomialBitLengthBound
        (n + 1) (matrixBitLength A) := by
  have prefixHeight :=
    RowTrace.inverseAccumulator_height_le_intermediateInverseMultiplierHeight
      (boundedColumnTrace A)
  have prefixBits := Nat.size_le_size prefixHeight
  have allBits := boundedColumnIntermediateInverseBitLength_le_polynomial A hdet
  change matrixBitLength (BoundedColumn.compute A).U_cert.inverse ≤ _
  rw [← (BoundedColumn.compute A).inverseAccumulator_eq]
  exact prefixBits.trans allBits

theorem leftHermitePhase_result_bitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    matrixBitLength (leftHermitePhase A).result ≤
      boundedColumnIntermediatePolynomialBitLengthBound
        (n + 1) (matrixBitLength A) := by
  have finalHeight := RowTrace.replay_height_le_intermediateMatrixHeight A
    (boundedColumnTrace A)
  have finalBits := (Nat.size_le_size finalHeight).trans
    (boundedColumnIntermediateMatrixBitLength_le_polynomial A)
  have replay : (boundedColumnTrace A).replay A = (leftHermitePhase A).result := by
    rw [RowTrace.replay_eq_accumulator_mul]
    change (BoundedColumn.compute A).steps.accumulator * A =
      (leftHermiteResult A).U * A
    rw [(BoundedColumn.compute A).accumulator_eq]
    rfl
  rw [replay] at finalBits
  exact finalBits

theorem pass_transformBitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0) :
    certificateTransformBitLength (pass A hdet) ≤
      passTransformBitLengthBound n (matrixBitLength A)
        (integerBitLength A.det) := by
  let left := leftHermitePhase A
  let leftDet : left.result.det ≠ 0 := result_det_ne_zero left hdet
  have leftBits := leftHermitePhase_result_bitLength_le A
  have leftU := boundedColumn_result_U_bitLength_le A hdet
  have leftInv := boundedColumn_result_inverse_bitLength_le A hdet
  have rightU := preparedPrincipal_multiplier_bitLength_le
    left.result.transpose (by simpa using leftDet)
  have rightInv := preparedPrincipal_inverse_bitLength_le
    left.result.transpose (by simpa using leftDet)
  have leftDetBits : integerBitLength left.result.transpose.det =
      integerBitLength A.det := by
    simp only [Matrix.det_transpose]
    exact congrArg Nat.size (certificate_result_det_natAbs left)
  have rightUUniform :
      matrixBitLength
          (Principal.preparedPrincipalHermiteNormalForm left.result.transpose
            (by simpa using leftDet)).U ≤
        preparedMultiplierBits n
          (boundedColumnIntermediatePolynomialBitLengthBound
            (n + 1) (matrixBitLength A))
          (integerBitLength A.det) :=
    rightU.trans <| by
      unfold preparedMultiplierBits
      rw [matrixBitLength_transpose, leftDetBits]
      apply Nat.add_le_add_left
      unfold determinantBitLengthBound
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left n (Nat.add_le_add_left leftBits (Nat.size n))) 2
  have rightInvUniform :
      matrixBitLength
          (Principal.preparedPrincipalHermiteNormalForm left.result.transpose
            (by simpa using leftDet)).U_cert.inverse ≤
        preparedInverseBits n
          (boundedColumnIntermediatePolynomialBitLengthBound
            (n + 1) (matrixBitLength A))
          (integerBitLength A.det) :=
    rightInv.trans <| by
      unfold preparedInverseBits
      rw [matrixBitLength_transpose, leftDetBits]
      exact Nat.add_le_add_right
        (Nat.add_le_add_left leftBits (Nat.size (n + 1))) _
  have passUEq : (pass A hdet).U = (leftHermiteResult A).U := by
    simp [pass, compose, rightHermitePhase, leftHermitePhase]
  have passUInvEq : (pass A hdet).U_cert.inverse =
      (leftHermiteResult A).U_cert.inverse := by
    simp [pass, compose, rightHermitePhase, leftHermitePhase,
      MatrixInverseCertificate.mul, MatrixInverseCertificate.one]
  have passVEq : (pass A hdet).V =
      (Principal.preparedPrincipalHermiteNormalForm left.result.transpose
        (by simpa using leftDet)).U.transpose := by
    simp [pass, compose, rightHermitePhase, rightHermiteResult,
      left, leftHermitePhase]
  have passVInvEq : (pass A hdet).V_cert.inverse =
      (Principal.preparedPrincipalHermiteNormalForm left.result.transpose
        (by simpa using leftDet)).U_cert.inverse.transpose := by
    simp [pass, compose, rightHermitePhase, rightHermiteResult,
      left, leftHermitePhase, MatrixInverseCertificate.mul,
      MatrixInverseCertificate.transpose, MatrixInverseCertificate.one]
  unfold certificateTransformBitLength
  unfold passTransformBitLengthBound
  apply max_le
  · rw [passUEq]
    exact leftU.trans (le_max_left _ _)
  · apply max_le
    · rw [passUInvEq]
      exact leftInv.trans <| (le_max_left _ _).trans (le_max_right _ _)
    · apply max_le
      · rw [passVEq, matrixBitLength_transpose]
        exact rightUUniform.trans <|
          (le_max_left _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
      · rw [passVInvEq, matrixBitLength_transpose]
        exact rightInvUniform.trans <|
          (le_max_right _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)

theorem compose_transformBitLength_le {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (first : TwoSidedCertificate A)
    (second : TwoSidedCertificate first.result) :
    certificateTransformBitLength (compose first second) ≤
      Nat.size n + certificateTransformBitLength first +
        certificateTransformBitLength second := by
  have firstU : matrixBitLength first.U ≤ certificateTransformBitLength first :=
    le_max_left _ _
  have firstUInv : matrixBitLength first.U_cert.inverse ≤
      certificateTransformBitLength first :=
    (le_max_left _ _).trans (le_max_right _ _)
  have firstV : matrixBitLength first.V ≤ certificateTransformBitLength first :=
    (le_max_left _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
  have firstVInv : matrixBitLength first.V_cert.inverse ≤
      certificateTransformBitLength first :=
    (le_max_right _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
  have secondU : matrixBitLength second.U ≤ certificateTransformBitLength second :=
    le_max_left _ _
  have secondUInv : matrixBitLength second.U_cert.inverse ≤
      certificateTransformBitLength second :=
    (le_max_left _ _).trans (le_max_right _ _)
  have secondV : matrixBitLength second.V ≤ certificateTransformBitLength second :=
    (le_max_left _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
  have secondVInv : matrixBitLength second.V_cert.inverse ≤
      certificateTransformBitLength second :=
    (le_max_right _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
  unfold certificateTransformBitLength compose
  apply max_le
  · exact (matrix_mul_bitLength_le second.U first.U).trans <| by
      omega
  · apply max_le
    · exact
        (matrix_mul_bitLength_le first.U_cert.inverse second.U_cert.inverse).trans <| by
          omega
    · apply max_le
      · exact (matrix_mul_bitLength_le first.V second.V).trans <| by
          omega
      · exact
          (matrix_mul_bitLength_le second.V_cert.inverse first.V_cert.inverse).trans <| by
            omega

theorem firstColumnClearCoefficient_natAbs_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (row : Fin n) :
    (firstColumnClearCoefficient A row).natAbs ≤ matrixHeight A + 1 := by
  unfold firstColumnClearCoefficient
  rw [Int.natAbs_neg]
  exact (Principal.intQuotient_natAbs_le_succ (A row.succ 0) (A 0 0)).trans <|
    Nat.add_le_add_right (entry_natAbs_le_matrixHeight A row.succ 0) 1

theorem firstColumnShear_height_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    matrixHeight (firstColumnShear (firstColumnClearCoefficient A)) ≤
      matrixHeight A + 1 := by
  apply matrixHeight_le
  intro row column
  cases row using Fin.cases with
  | zero =>
      cases column using Fin.cases <;> simp
  | succ row =>
      cases column using Fin.cases with
      | zero => exact firstColumnClearCoefficient_natAbs_le A row
      | succ column =>
          by_cases equality : row = column <;>
            simp [equality]

theorem clear_transformBitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    certificateTransformBitLength (clearDivisibleFirstColumn A) ≤
      matrixBitLength A + 1 := by
  have forwardHeight := firstColumnShear_height_le A
  have backwardHeight :
      matrixHeight (firstColumnShear (-firstColumnClearCoefficient A)) ≤
        matrixHeight A + 1 := by
    apply matrixHeight_le
    intro row column
    cases row using Fin.cases with
    | zero =>
        cases column using Fin.cases <;> simp
    | succ row =>
        cases column using Fin.cases with
        | zero =>
            simpa using firstColumnClearCoefficient_natAbs_le A row
        | succ column =>
            by_cases equality : row = column <;>
              simp [equality]
  have successorSize := Principal.natSize_succ_le (matrixHeight A)
  have oneBits : matrixBitLength
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) ≤ 1 := by
    unfold matrixBitLength
    apply Nat.size_le.2
    have heightLe : matrixHeight
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) ≤ 1 := by
      apply matrixHeight_le
      intro row column
      by_cases equality : row = column <;>
        simp [Matrix.one_apply, equality]
    exact heightLe.trans_lt (by decide)
  unfold certificateTransformBitLength clearDivisibleFirstColumn
    firstColumnShearCertificate
  simp only [MatrixInverseCertificate.one, matrixBitLength]
  change Nat.size (matrixHeight
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)) ≤ 1 at oneBits
  apply max_le
  · exact (Nat.size_le_size forwardHeight).trans successorSize
  · apply max_le
    · exact (Nat.size_le_size backwardHeight).trans successorSize
    · exact max_le (oneBits.trans (by omega)) (oneBits.trans (by omega))

theorem clear_result_height_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hrow : FirstRowCleared A)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0) :
    matrixHeight (clearDivisibleFirstColumn A).result ≤ matrixHeight A := by
  apply matrixHeight_le
  intro row column
  cases row using Fin.cases with
  | zero =>
      rw [clearDivisibleFirstColumn_apply_zero]
      exact entry_natAbs_le_matrixHeight A 0 column
  | succ row =>
      cases column using Fin.cases with
      | zero =>
          rw [clearDivisibleFirstColumn_apply_succ_zero A row (hdiv row)]
          simp
      | succ column =>
          rw [clearDivisibleFirstColumn_lowerRight A hrow]
          exact entry_natAbs_le_matrixHeight A row.succ column.succ

theorem injection_transformBitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (column : Fin n) :
    certificateTransformBitLength (injectLowerWitness A column) ≤ 1 := by
  have oneBits : matrixBitLength
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) ≤ 1 := by
    unfold matrixBitLength
    apply Nat.size_le.2
    have heightLe : matrixHeight
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) ≤ 1 := by
      apply matrixHeight_le
      intro row target
      by_cases equality : row = target <;>
        simp [Matrix.one_apply, equality]
    exact heightLe.trans_lt (by decide)
  have columnAddBits : ∀ coefficient : Int, coefficient.natAbs ≤ 1 →
      matrixBitLength
          (columnOperationMatrix
            (.add column.succ 0 coefficient)) ≤ 1 := by
    intro coefficient coefficientBound
    unfold matrixBitLength
    apply Nat.size_le.2
    have heightLe : matrixHeight
        (columnOperationMatrix
          (.add column.succ 0 coefficient)) ≤ 1 := by
      apply matrixHeight_le
      intro row target
      unfold columnOperationMatrix
      by_cases targetZero : target = 0
      · subst target
        by_cases rowZero : row = 0
        · subst row
          have zeroNe : (0 : Fin (n + 1)) ≠ column.succ :=
            fun equality => Fin.succ_ne_zero column equality.symm
          simp [Matrix.one_apply, zeroNe]
        · by_cases rowSource : row = column.succ
          · subst row
            simpa using coefficientBound
          · simp [Matrix.one_apply, rowZero, rowSource]
      · by_cases rowTarget : row = target <;>
          simp [Matrix.one_apply, targetZero, rowTarget]
    exact heightLe.trans_lt (by decide)
  unfold certificateTransformBitLength injectLowerWitness columnAddCertificate
    MatrixInverseCertificate.one
  apply max_le
  · exact oneBits
  · apply max_le
    · exact oneBits
    · apply max_le
      · exact columnAddBits 1 (by decide)
      · exact columnAddBits (-1) (by decide)

theorem injection_result_height_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (column : Fin n) :
    matrixHeight (injectLowerWitness A column).result ≤ 2 * matrixHeight A := by
  apply matrixHeight_le
  intro row target
  by_cases equality : target = 0
  · subst target
    simp only [injectLowerWitness, applyColumnOperation, if_pos]
    calc
      (A row 0 + 1 * A row column.succ).natAbs ≤
          (A row 0).natAbs + (A row column.succ).natAbs := by
        simpa using Int.natAbs_add_le (A row 0) (A row column.succ)
      _ ≤ matrixHeight A + matrixHeight A :=
        Nat.add_le_add (entry_natAbs_le_matrixHeight A row 0)
          (entry_natAbs_le_matrixHeight A row column.succ)
      _ = 2 * matrixHeight A := by ring
  · simp only [injectLowerWitness, applyColumnOperation, if_neg equality]
    exact (entry_natAbs_le_matrixHeight A row target).trans (by omega)

theorem injection_result_bitLength_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (column : Fin n) :
    matrixBitLength (injectLowerWitness A column).result ≤
      matrixBitLength A + 1 := by
  unfold matrixBitLength
  exact (Nat.size_le_size (injection_result_height_le A column)).trans <| by
    rw [Nat.size_le]
    have inputLt : matrixHeight A < 2 ^ Nat.size (matrixHeight A) :=
      Nat.lt_size_self _
    calc
      2 * matrixHeight A < 2 * 2 ^ Nat.size (matrixHeight A) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 inputLt
      _ = 2 ^ (Nat.size (matrixHeight A) + 1) := by
        rw [pow_succ]
        ring

theorem passTransformBitLengthBound_mono {order smallerInput largerInput
    smallerDet largerDet : Nat}
    (inputLe : smallerInput ≤ largerInput)
    (detLe : smallerDet ≤ largerDet) :
    passTransformBitLengthBound order smallerInput smallerDet ≤
      passTransformBitLengthBound order largerInput largerDet := by
  have determinantMono (inputSmall inputLarge : Nat)
      (hle : inputSmall ≤ inputLarge) :
      determinantBitLengthBound order inputSmall ≤
        determinantBitLengthBound order inputLarge := by
    unfold determinantBitLengthBound
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left order (Nat.add_le_add_left hle _)) 2
  have intermediateMono :
      boundedColumnIntermediatePolynomialBitLengthBound
          (order + 1) smallerInput ≤
        boundedColumnIntermediatePolynomialBitLengthBound
          (order + 1) largerInput := by
    simp only [boundedColumnIntermediatePolynomialBitLengthBound]
    have factorMono :
        Nat.size (order + 1) + 2 * (smallerInput + 1) + 6 ≤
          Nat.size (order + 1) + 2 * (largerInput + 1) + 6 := by
      omega
    exact Nat.add_le_add_right
      (Nat.add_le_add inputLe (Nat.mul_le_mul_left order factorMono)) 1
  have multiplierMono :
      boundedColumnMultiplierPolynomialBitLengthBound
          (order + 1) smallerInput ≤
        boundedColumnMultiplierPolynomialBitLengthBound
          (order + 1) largerInput := by
    simp only [boundedColumnMultiplierPolynomialBitLengthBound]
    exact Nat.add_le_add
      (Nat.add_le_add_left intermediateMono _)
      (determinantMono _ _ inputLe)
  have inverseMono :
      boundedColumnInversePolynomialBitLengthBound
          (order + 1) smallerInput ≤
        boundedColumnInversePolynomialBitLengthBound
          (order + 1) largerInput := by
    simp only [boundedColumnInversePolynomialBitLengthBound]
    exact Nat.add_le_add
      (Nat.add_le_add_left inputLe _)
      (determinantMono _ _ intermediateMono)
  unfold passTransformBitLengthBound preparedMultiplierBits preparedInverseBits
  exact max_le
    (multiplierMono.trans (le_max_left _ _)) <| max_le
      (inverseMono.trans <| (le_max_left _ _).trans (le_max_right _ _)) <|
        max_le
          (Nat.add_le_add
            (Nat.add_le_add_left detLe _)
            (determinantMono _ _ intermediateMono) |>.trans <|
              (le_max_left _ _).trans <|
                (le_max_right _ _).trans (le_max_right _ _))
          (Nat.add_le_add
            (Nat.add_le_add_left intermediateMono _)
            (determinantMono _ _ detLe) |>.trans <|
              (le_max_right _ _).trans <|
                (le_max_right _ _).trans (le_max_right _ _))

@[expose] def stabilizationFactorBitLengthBound
    (order workBits : Nat) : Nat :=
  max (passTransformBitLengthBound order (workBits + 1) workBits)
    (workBits + 1)

@[expose] def stabilizationCompositionBitLength
    (order workBits : Nat) : Nat :=
  Nat.size (order + 1) + stabilizationFactorBitLengthBound order workBits

private theorem threeFactorCompositions
    (matrixBits factorBits continuation : Nat) :
    matrixBits + (matrixBits + factorBits + factorBits) +
        (matrixBits + factorBits + continuation) =
      3 * (matrixBits + factorBits) + continuation := by
  omega

private theorem threeCompositionSteps (measure composition : Nat) :
    3 * composition + (3 * measure + 1) * composition =
      (3 * measure + 4) * composition := by
  ring

private theorem threeCompositionCoefficient_lt {smaller larger : Nat}
    (hlt : smaller < larger) :
    3 * smaller + 4 ≤ 3 * larger + 1 := by
  omega

theorem pass_transformBitLength_le_uniform {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0)
    (matrixBound : matrixBitLength A ≤ workBits + 1)
    (detBound : integerBitLength A.det ≤ workBits) :
    certificateTransformBitLength (pass A hdet) ≤
      stabilizationFactorBitLengthBound n workBits := by
  exact (pass_transformBitLength_le A hdet).trans <|
    (passTransformBitLengthBound_mono matrixBound detBound).trans
      (le_max_left _ _)

theorem clear_transformBitLength_le_uniform {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (matrixBound : matrixBitLength A ≤ workBits) :
    certificateTransformBitLength (clearDivisibleFirstColumn A) ≤
      stabilizationFactorBitLengthBound n workBits :=
  (clear_transformBitLength_le A).trans <|
    (Nat.add_le_add_right matrixBound 1).trans (le_max_right _ _)

theorem injection_transformBitLength_le_uniform {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (column : Fin n) :
    certificateTransformBitLength (injectLowerWitness A column) ≤
      stabilizationFactorBitLengthBound n workBits :=
  (injection_transformBitLength_le A column).trans <|
    (by omega : 1 ≤ workBits + 1).trans (le_max_right _ _)

theorem stabilizeFrom_transformBitLength_le {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = normalize (A 0 0))
    (hrow : FirstRowCleared A)
    (matrixBound : matrixBitLength A ≤ workBits)
    (detBound : integerBitLength A.det ≤ workBits) :
    certificateTransformBitLength
        (stabilizeFrom A hdet hpivot hnormalized hrow).certificate ≤
      (3 * (A 0 0).natAbs.size + 1) *
        stabilizationCompositionBitLength n workBits := by
  generalize measureEq : (A 0 0).natAbs.size = measure
  induction measure using Nat.strong_induction_on generalizing A with
  | h measure ih =>
      rw [stabilizeFrom.eq_1]
      split
      next row hbadColumn =>
        dsimp only
        let current := pass A hdet
        have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
          A hdet hpivot row.succ
            (firstUndivisibleBelow?_some_not_dvd A hbadColumn)
        have decreaseMeasure :
            (current.result 0 0).natAbs.size < measure := by
          simpa [current, measureEq] using decrease
        have currentMatrixBound : matrixBitLength current.result ≤ workBits := by
          exact (pass_result_bitLength_le_determinant A hdet).trans detBound
        have currentDetBits :
            integerBitLength current.result.det = integerBitLength A.det :=
          congrArg Nat.size (certificate_result_det_natAbs current)
        have nextBound := ih _ decreaseMeasure current.result
          (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
          (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
          currentMatrixBound (currentDetBits ▸ detBound) rfl
        have currentBound :
            certificateTransformBitLength current ≤
              stabilizationFactorBitLengthBound n workBits :=
          pass_transformBitLength_le_uniform A hdet
            (matrixBound.trans (by omega)) detBound
        have compositionBound := compose_transformBitLength_le
          current
          (stabilizeFrom current.result
            (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
            (pass_shape A hdet).2.1 (pass_shape A hdet).2.2).certificate
        calc
          certificateTransformBitLength
              (compose current
                (stabilizeFrom current.result
                  (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
                  (pass_shape A hdet).2.1
                  (pass_shape A hdet).2.2).certificate) ≤
              Nat.size (n + 1) +
                certificateTransformBitLength current +
                certificateTransformBitLength
                  (stabilizeFrom current.result
                    (pass_result_det_ne_zero A hdet)
                    (pass_shape A hdet).1 (pass_shape A hdet).2.1
                    (pass_shape A hdet).2.2).certificate :=
            compositionBound
          _ ≤ stabilizationCompositionBitLength n workBits +
                (3 * (current.result 0 0).natAbs.size + 1) *
                  stabilizationCompositionBitLength n workBits := by
            unfold stabilizationCompositionBitLength
            exact Nat.add_le_add
              (Nat.add_le_add_left currentBound _)
              nextBound
          _ = (3 * (current.result 0 0).natAbs.size + 2) *
                stabilizationCompositionBitLength n workBits := by ring
          _ ≤ (3 * measure + 1) *
                stabilizationCompositionBitLength n workBits := by
            apply Nat.mul_le_mul_right
            omega
      next hnoBadColumn =>
        dsimp only
        split
        next _hnoBadLower =>
          have clearBound := clear_transformBitLength_le_uniform
            A matrixBound
          calc
            certificateTransformBitLength (clearDivisibleFirstColumn A) ≤
                stabilizationFactorBitLengthBound n workBits := clearBound
            _ ≤ stabilizationCompositionBitLength n workBits := by
              unfold stabilizationCompositionBitLength
              omega
            _ = 1 * stabilizationCompositionBitLength n workBits := by simp
            _ ≤ (3 * measure + 1) *
                  stabilizationCompositionBitLength n workBits := by
              exact Nat.mul_le_mul_right _ (by omega)
        next position hbadLower =>
          let cleared := clearDivisibleFirstColumn A
          let hdiv := firstUndivisibleBelow?_eq_none A hnoBadColumn
          let hclearedColumn :=
            clearDivisibleFirstColumn_firstColumnCleared A hdiv
          let hclearedRow :=
            clearDivisibleFirstColumn_firstRowCleared A hrow
          let injection := injectLowerWitness cleared.result position.2
          let accumulated := compose cleared injection
          let accumulatedDet := result_det_ne_zero accumulated hdet
          let current := pass accumulated.result accumulatedDet
          have accumulatedPivot : accumulated.result 0 0 = A 0 0 := by
            exact (injectLowerWitness_pivot cleared.result position.2
              hclearedRow).trans (clearDivisibleFirstColumn_pivot A)
          have target : accumulated.result position.1.succ 0 =
              cleared.result position.1.succ position.2.succ :=
            injectLowerWitness_target cleared.result position.1 position.2
              hclearedColumn
          have hnot : ¬ accumulated.result 0 0 ∣
              accumulated.result position.1.succ 0 := by
            rw [accumulatedPivot, target]
            have original := firstUndivisibleLower?_some_not_dvd
              cleared.result hbadLower
            rw [← show cleared.result 0 0 = A 0 0 by
              exact clearDivisibleFirstColumn_pivot A]
            exact original
          have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
            accumulated.result accumulatedDet
            (by simpa [accumulatedPivot] using hpivot) position.1.succ hnot
          have decreaseMeasure :
              (current.result 0 0).natAbs.size < measure := by
            simpa [current, accumulatedPivot, measureEq] using decrease
          have clearedHeight := clear_result_height_le A hrow hdiv
          have clearedMatrixBound :
              matrixBitLength cleared.result ≤ workBits :=
            (Nat.size_le_size clearedHeight).trans matrixBound
          have injectionMatrixBound :
              matrixBitLength injection.result ≤ workBits + 1 :=
            (injection_result_bitLength_le cleared.result position.2).trans <| by
              omega
          have accumulatedResult : accumulated.result = injection.result := rfl
          have accumulatedDetBits :
              integerBitLength accumulated.result.det = integerBitLength A.det :=
            congrArg Nat.size (certificate_result_det_natAbs accumulated)
          have currentMatrixBound : matrixBitLength current.result ≤ workBits := by
            exact (pass_result_bitLength_le_determinant
              accumulated.result accumulatedDet).trans <| by
                rw [accumulatedDetBits]
                exact detBound
          have currentDetBits :
              integerBitLength current.result.det = integerBitLength A.det := by
            rw [show integerBitLength current.result.det =
                integerBitLength accumulated.result.det from
              congrArg Nat.size (certificate_result_det_natAbs current)]
            exact accumulatedDetBits
          have nextBound := ih _ decreaseMeasure current.result
            (pass_result_det_ne_zero accumulated.result accumulatedDet)
            (pass_shape accumulated.result accumulatedDet).1
            (pass_shape accumulated.result accumulatedDet).2.1
            (pass_shape accumulated.result accumulatedDet).2.2
            currentMatrixBound (currentDetBits ▸ detBound) rfl
          have clearBound : certificateTransformBitLength cleared ≤
              stabilizationFactorBitLengthBound n workBits :=
            clear_transformBitLength_le_uniform A matrixBound
          have injectionBound : certificateTransformBitLength injection ≤
              stabilizationFactorBitLengthBound n workBits :=
            injection_transformBitLength_le_uniform cleared.result position.2
          have currentBound : certificateTransformBitLength current ≤
              stabilizationFactorBitLengthBound n workBits := by
            apply pass_transformBitLength_le_uniform
              accumulated.result accumulatedDet
            · simpa [accumulatedResult] using injectionMatrixBound
            · rw [accumulatedDetBits]
              exact detBound
          have accumulatedBound := compose_transformBitLength_le
            cleared injection
          have innerBound := compose_transformBitLength_le current
            (stabilizeFrom current.result
              (pass_result_det_ne_zero accumulated.result accumulatedDet)
              (pass_shape accumulated.result accumulatedDet).1
              (pass_shape accumulated.result accumulatedDet).2.1
              (pass_shape accumulated.result accumulatedDet).2.2).certificate
          have outerBound := compose_transformBitLength_le accumulated
            (compose current
              (stabilizeFrom current.result
                (pass_result_det_ne_zero accumulated.result accumulatedDet)
                (pass_shape accumulated.result accumulatedDet).1
                (pass_shape accumulated.result accumulatedDet).2.1
                (pass_shape accumulated.result accumulatedDet).2.2).certificate)
          have accumulatedUniform :
              certificateTransformBitLength accumulated ≤
                Nat.size (n + 1) +
                  stabilizationFactorBitLengthBound n workBits +
                  stabilizationFactorBitLengthBound n workBits :=
            accumulatedBound.trans <| Nat.add_le_add
              (Nat.add_le_add_left clearBound _)
              injectionBound
          have innerUniform :
              certificateTransformBitLength
                  (compose current
                    (stabilizeFrom current.result
                      (pass_result_det_ne_zero accumulated.result accumulatedDet)
                      (pass_shape accumulated.result accumulatedDet).1
                      (pass_shape accumulated.result accumulatedDet).2.1
                      (pass_shape accumulated.result accumulatedDet).2.2).certificate) ≤
                Nat.size (n + 1) +
                  stabilizationFactorBitLengthBound n workBits +
                  (3 * (current.result 0 0).natAbs.size + 1) *
                    stabilizationCompositionBitLength n workBits :=
            innerBound.trans <| Nat.add_le_add
              (Nat.add_le_add_left currentBound _)
              nextBound
          calc
            certificateTransformBitLength
                (compose accumulated
                  (compose current
                    (stabilizeFrom current.result
                      (pass_result_det_ne_zero accumulated.result accumulatedDet)
                      (pass_shape accumulated.result accumulatedDet).1
                      (pass_shape accumulated.result accumulatedDet).2.1
                      (pass_shape accumulated.result accumulatedDet).2.2).certificate)) ≤
                Nat.size (n + 1) +
                  certificateTransformBitLength accumulated +
                  certificateTransformBitLength
                    (compose current
                      (stabilizeFrom current.result
                        (pass_result_det_ne_zero accumulated.result accumulatedDet)
                        (pass_shape accumulated.result accumulatedDet).1
                        (pass_shape accumulated.result accumulatedDet).2.1
                        (pass_shape accumulated.result accumulatedDet).2.2).certificate) :=
              outerBound
            _ ≤ Nat.size (n + 1) +
                  (Nat.size (n + 1) +
                    stabilizationFactorBitLengthBound n workBits +
                    stabilizationFactorBitLengthBound n workBits) +
                  (Nat.size (n + 1) +
                    stabilizationFactorBitLengthBound n workBits +
                    (3 * (current.result 0 0).natAbs.size + 1) *
                      stabilizationCompositionBitLength n workBits) := by
              exact Nat.add_le_add
                (Nat.add_le_add_left accumulatedUniform _)
                innerUniform
            _ = 3 * stabilizationCompositionBitLength n workBits +
                  (3 * (current.result 0 0).natAbs.size + 1) *
                    stabilizationCompositionBitLength n workBits := by
              exact threeFactorCompositions _ _ _
            _ = (3 * (current.result 0 0).natAbs.size + 4) *
                  stabilizationCompositionBitLength n workBits :=
              threeCompositionSteps _ _
            _ ≤ (3 * measure + 1) *
                  stabilizationCompositionBitLength n workBits := by
              exact Nat.mul_le_mul_right _
                (threeCompositionCoefficient_lt decreaseMeasure)

theorem stabilizeFrom_result_bitLength_le {n workBits : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = normalize (A 0 0))
    (hrow : FirstRowCleared A)
    (matrixBound : matrixBitLength A ≤ workBits)
    (detBound : integerBitLength A.det ≤ workBits) :
    matrixBitLength
        (stabilizeFrom A hdet hpivot hnormalized hrow).certificate.result ≤
      workBits := by
  generalize measureEq : (A 0 0).natAbs.size = measure
  induction measure using Nat.strong_induction_on generalizing A with
  | h measure ih =>
      rw [stabilizeFrom.eq_1]
      split
      next row hbadColumn =>
        dsimp only
        let current := pass A hdet
        have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
          A hdet hpivot row.succ
            (firstUndivisibleBelow?_some_not_dvd A hbadColumn)
        have decreaseMeasure :
            (current.result 0 0).natAbs.size < measure := by
          simpa [current, measureEq] using decrease
        have currentMatrixBound : matrixBitLength current.result ≤ workBits :=
          (pass_result_bitLength_le_determinant A hdet).trans detBound
        have currentDetBits :
            integerBitLength current.result.det = integerBitLength A.det :=
          congrArg Nat.size (certificate_result_det_natAbs current)
        exact ih _ decreaseMeasure current.result
          (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
          (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
          currentMatrixBound (currentDetBits ▸ detBound) rfl
      next hnoBadColumn =>
        dsimp only
        split
        next _hnoBadLower =>
          exact (Nat.size_le_size <|
            clear_result_height_le A hrow
              (firstUndivisibleBelow?_eq_none A hnoBadColumn)).trans
            matrixBound
        next position hbadLower =>
          let cleared := clearDivisibleFirstColumn A
          let hdiv := firstUndivisibleBelow?_eq_none A hnoBadColumn
          let hclearedColumn :=
            clearDivisibleFirstColumn_firstColumnCleared A hdiv
          let hclearedRow :=
            clearDivisibleFirstColumn_firstRowCleared A hrow
          let injection := injectLowerWitness cleared.result position.2
          let accumulated := compose cleared injection
          let accumulatedDet := result_det_ne_zero accumulated hdet
          let current := pass accumulated.result accumulatedDet
          have accumulatedPivot : accumulated.result 0 0 = A 0 0 := by
            exact (injectLowerWitness_pivot cleared.result position.2
              hclearedRow).trans (clearDivisibleFirstColumn_pivot A)
          have target : accumulated.result position.1.succ 0 =
              cleared.result position.1.succ position.2.succ :=
            injectLowerWitness_target cleared.result position.1 position.2
              hclearedColumn
          have hnot : ¬ accumulated.result 0 0 ∣
              accumulated.result position.1.succ 0 := by
            rw [accumulatedPivot, target]
            have original := firstUndivisibleLower?_some_not_dvd
              cleared.result hbadLower
            rw [← show cleared.result 0 0 = A 0 0 by
              exact clearDivisibleFirstColumn_pivot A]
            exact original
          have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
            accumulated.result accumulatedDet
            (by simpa [accumulatedPivot] using hpivot) position.1.succ hnot
          have decreaseMeasure :
              (current.result 0 0).natAbs.size < measure := by
            simpa [current, accumulatedPivot, measureEq] using decrease
          have accumulatedDetBits :
              integerBitLength accumulated.result.det = integerBitLength A.det :=
            congrArg Nat.size (certificate_result_det_natAbs accumulated)
          have currentMatrixBound : matrixBitLength current.result ≤ workBits :=
            (pass_result_bitLength_le_determinant
              accumulated.result accumulatedDet).trans <| by
                rw [accumulatedDetBits]
                exact detBound
          have currentDetBits :
              integerBitLength current.result.det = integerBitLength A.det := by
            rw [show integerBitLength current.result.det =
                integerBitLength accumulated.result.det from
              congrArg Nat.size (certificate_result_det_natAbs current)]
            exact accumulatedDetBits
          exact ih _ decreaseMeasure current.result
            (pass_result_det_ne_zero accumulated.result accumulatedDet)
            (pass_shape accumulated.result accumulatedDet).1
            (pass_shape accumulated.result accumulatedDet).2.1
            (pass_shape accumulated.result accumulatedDet).2.2
            currentMatrixBound (currentDetBits ▸ detBound) rfl

@[expose] def stabilizationCertificatePolynomialBitLengthBound
    (dimension inputBits : Nat) : Nat :=
  let determinantBits := determinantBitLengthBound dimension inputBits
  let workBits := max inputBits determinantBits
  (3 * determinantBits + 2) *
    stabilizationCompositionBitLength (dimension - 1) workBits

theorem stabilize_result_bitLength_le_determinant {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    matrixBitLength (stabilize A hdet).certificate.result ≤
      integerBitLength A.det := by
  let initial := pass A hdet
  have initialMatrixBound :
      matrixBitLength initial.result ≤ integerBitLength A.det :=
    pass_result_bitLength_le_determinant A hdet
  have initialDetBits :
      integerBitLength initial.result.det = integerBitLength A.det :=
    congrArg Nat.size (certificate_result_det_natAbs initial)
  change matrixBitLength
    (stabilizeFrom initial.result (pass_result_det_ne_zero A hdet)
      (pass_shape A hdet).1 (pass_shape A hdet).2.1
      (pass_shape A hdet).2.2).certificate.result ≤ _
  exact stabilizeFrom_result_bitLength_le initial.result
    (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
    (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
    initialMatrixBound (initialDetBits.le)

theorem stabilize_transformBitLength_le_polynomial {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    certificateTransformBitLength (stabilize A hdet).certificate ≤
      stabilizationCertificatePolynomialBitLengthBound
        (n + 1) (matrixBitLength A) := by
  let determinantBits :=
    determinantBitLengthBound (n + 1) (matrixBitLength A)
  let workBits := max (matrixBitLength A) determinantBits
  let initial := pass A hdet
  have inputBound : matrixBitLength A ≤ workBits := le_max_left _ _
  have detBound : integerBitLength A.det ≤ workBits :=
    (determinant_bitLength_le A).trans (le_max_right _ _)
  have initialMatrixBound : matrixBitLength initial.result ≤ workBits :=
    (pass_result_bitLength_le_determinant A hdet).trans detBound
  have initialDetBits :
      integerBitLength initial.result.det = integerBitLength A.det :=
    congrArg Nat.size (certificate_result_det_natAbs initial)
  have initialBound : certificateTransformBitLength initial ≤
      stabilizationFactorBitLengthBound n workBits :=
    pass_transformBitLength_le_uniform A hdet
      (inputBound.trans (by omega)) detBound
  have restBound := stabilizeFrom_transformBitLength_le initial.result
    (pass_result_det_ne_zero A hdet) (pass_shape A hdet).1
    (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
    initialMatrixBound (initialDetBits ▸ detBound)
  have compositionBound := compose_transformBitLength_le initial
    (stabilizeFrom initial.result (pass_result_det_ne_zero A hdet)
      (pass_shape A hdet).1 (pass_shape A hdet).2.1
      (pass_shape A hdet).2.2).certificate
  have pivotBound : (initial.result 0 0).natAbs.size ≤ determinantBits :=
    (pass_pivotBitLength_le_determinant A hdet).trans <|
      determinant_bitLength_le A
  change certificateTransformBitLength
      (compose initial
        (stabilizeFrom initial.result (pass_result_det_ne_zero A hdet)
          (pass_shape A hdet).1 (pass_shape A hdet).2.1
          (pass_shape A hdet).2.2).certificate) ≤ _
  unfold stabilizationCertificatePolynomialBitLengthBound
  simp only [Nat.add_sub_cancel]
  calc
    certificateTransformBitLength
        (compose initial
          (stabilizeFrom initial.result (pass_result_det_ne_zero A hdet)
            (pass_shape A hdet).1 (pass_shape A hdet).2.1
            (pass_shape A hdet).2.2).certificate) ≤
        Nat.size (n + 1) + certificateTransformBitLength initial +
          certificateTransformBitLength
            (stabilizeFrom initial.result (pass_result_det_ne_zero A hdet)
              (pass_shape A hdet).1 (pass_shape A hdet).2.1
              (pass_shape A hdet).2.2).certificate := compositionBound
    _ ≤ stabilizationCompositionBitLength n workBits +
          (3 * (initial.result 0 0).natAbs.size + 1) *
            stabilizationCompositionBitLength n workBits := by
      unfold stabilizationCompositionBitLength
      exact Nat.add_le_add
        (Nat.add_le_add_left initialBound _)
        restBound
    _ = (3 * (initial.result 0 0).natAbs.size + 2) *
          stabilizationCompositionBitLength n workBits := by ring
    _ ≤ (3 * determinantBits + 2) *
          stabilizationCompositionBitLength n workBits := by
      apply Nat.mul_le_mul_right
      omega

end NormalForms.Research.KannanBachem.Smith
