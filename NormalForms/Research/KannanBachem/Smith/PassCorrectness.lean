/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.Pass

/-! Structural invariants established by one Kannan--Bachem Smith pass. -/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms.Matrix.Hermite
open NormalForms.Research.KannanBachem.Hermite

/-- The active first column is zero below its pivot. -/
@[expose] public def FirstColumnCleared {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Prop :=
  ∀ row : Fin n, A row.succ 0 = 0

/-- The active first row is zero to the right of its pivot. -/
@[expose] public def FirstRowCleared {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Prop :=
  ∀ column : Fin n, A 0 column.succ = 0

/-- The current pivot divides every entry of the strict lower-right block. -/
@[expose] public def PivotDividesLower {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Prop :=
  ∀ row column : Fin n, A 0 0 ∣ A row.succ column.succ

/-- A nonsingular matrix cannot have a zero first column. -/
public theorem firstColumn_ne_zero_of_det_ne {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    firstColumn A ≠ 0 := by
  intro hzero
  apply hdet
  apply _root_.Matrix.det_eq_zero_of_column_eq_zero 0
  intro row
  have entry := congrFun (congrFun hzero row) 0
  simpa [firstColumn] using entry

/-- A nonzero one-column HNF consists of one normalized pivot and zero tail. -/
public theorem singleColumnHermite_shape {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin 1) Int}
    (hHermite : IsHermiteNormalFormFin A) (hne : A ≠ 0) :
    A 0 0 ≠ 0 ∧ A 0 0 = _root_.normalize (A 0 0) ∧
      ∀ row : Fin n, A row.succ 0 = 0 := by
  cases hHermite with
  | zeroCol A hzero _ =>
      exact False.elim <| hne <| by
        ext row column
        fin_cases column
        exact hzero row
  | pivot A hpivot hnormalized hbelow _ _ =>
      exact ⟨hpivot, hnormalized, hbelow⟩

/-- Step 4 clears the first column and leaves a normalized nonzero pivot. -/
public theorem leftHermitePhase_shape {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (leftHermitePhase A).result 0 0 ≠ 0 ∧
      (leftHermitePhase A).result 0 0 =
        _root_.normalize ((leftHermitePhase A).result 0 0) ∧
      FirstColumnCleared (leftHermitePhase A).result := by
  have resultDet : (leftHermitePhase A).result.det ≠ 0 :=
    result_det_ne_zero (leftHermitePhase A) hdet
  have columnNonzero :=
    firstColumn_ne_zero_of_det_ne (leftHermitePhase A).result resultDet
  exact singleColumnHermite_shape
    (leftHermitePhase_isHermite A) columnNonzero

/-- A nonsingular square HNF has a normalized nonzero first pivot and zero tail. -/
public theorem nonsingularHermite_firstPivot {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (hHermite : IsHermiteNormalFormFin A) (hdet : A.det ≠ 0) :
    A 0 0 ≠ 0 ∧ A 0 0 = _root_.normalize (A 0 0) ∧
      FirstColumnCleared A := by
  cases hHermite with
  | zeroCol A hzero _ =>
      exact False.elim <| hdet <|
        _root_.Matrix.det_eq_zero_of_column_eq_zero 0 hzero
  | pivot A hpivot hnormalized hbelow _ _ =>
      exact ⟨hpivot, hnormalized, hbelow⟩

/-- Step 5 clears the first row and leaves a normalized nonzero pivot. -/
public theorem pass_shape {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (pass A hdet).result 0 0 ≠ 0 ∧
      (pass A hdet).result 0 0 =
        _root_.normalize ((pass A hdet).result 0 0) ∧
      FirstRowCleared (pass A hdet).result := by
  have transposeDet : (pass A hdet).result.transpose.det ≠ 0 := by
    simpa using pass_result_det_ne_zero A hdet
  obtain ⟨pivotNonzero, pivotNormalized, columnCleared⟩ :=
    nonsingularHermite_firstPivot (pass_transpose_isHermite A hdet)
      transposeDet
  exact ⟨pivotNonzero, pivotNormalized, columnCleared⟩

/--
If an invertible row transform produces a column with only its first entry
nonzero, that entry divides every entry of the original column.
-/
public theorem firstPivot_dvd_column_of_inverse {n : Nat}
    {columns : Type}
    {A H : _root_.Matrix (Fin (n + 1)) columns Int}
    (inverse : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hinverse : inverse * H = A) (column : columns)
    (hbelow : ∀ row : Fin n, H row.succ column = 0)
    (row : Fin (n + 1)) : H 0 column ∣ A row column := by
  refine ⟨inverse row 0, ?_⟩
  rw [← hinverse, _root_.Matrix.mul_apply, Fin.sum_univ_succ]
  simp [hbelow, mul_comm]

/-- The Step-4 pivot divides every input entry in the active first column. -/
public theorem leftHermitePhase_pivot_dvd_entry {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (row : Fin (n + 1)) :
    (leftHermitePhase A).result 0 0 ∣ A row 0 := by
  obtain ⟨_pivotNonzero, _pivotNormalized, hbelow⟩ :=
    leftHermitePhase_shape A hdet
  have hinverse :
      (leftHermiteResult A).U_cert.inverse *
          (leftHermiteResult A).H = firstColumn A := by
    rw [← (leftHermiteResult A).equation, ← _root_.Matrix.mul_assoc,
      (leftHermiteResult A).U_cert.left_inv, _root_.Matrix.one_mul]
  have hdvd := firstPivot_dvd_column_of_inverse
    (leftHermiteResult A).U_cert.inverse hinverse 0
    (fun i => by
      rw [← leftHermitePhase_firstColumn A]
      exact hbelow i) row
  have hpivot : (leftHermitePhase A).result 0 0 =
      (leftHermiteResult A).H 0 0 := by
    exact congrFun (congrFun (leftHermitePhase_firstColumn A) 0) 0
  rw [hpivot]
  simpa [firstColumn] using hdvd

/-- The Step-5 pivot divides every entry in the input first row. -/
public theorem rightHermitePhase_pivot_dvd_entry {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (column : Fin (n + 1)) :
    (rightHermitePhase A hdet).result 0 0 ∣ A 0 column := by
  have resultDet :
      (rightHermitePhase A hdet).result.transpose.det ≠ 0 := by
    simpa using result_det_ne_zero (rightHermitePhase A hdet) hdet
  obtain ⟨_pivotNonzero, _pivotNormalized, hbelow⟩ :=
    nonsingularHermite_firstPivot
      (rightHermitePhase_transpose_isHermite A hdet) resultDet
  have hinverse :
      (rightHermiteResult A hdet).U_cert.inverse *
          (rightHermiteResult A hdet).H = A.transpose :=
    Principal.preparedPrincipalHermiteNormalForm_inverse_equation A.transpose
      (by simpa using hdet)
  have hdvd := firstPivot_dvd_column_of_inverse
    (A := A.transpose) (H := (rightHermiteResult A hdet).H)
    (rightHermiteResult A hdet).U_cert.inverse hinverse 0
    (fun i => by simpa [rightHermitePhase] using hbelow i) column
  simpa [rightHermitePhase] using hdvd

/-- The final pivot of a full pass divides the intermediate Step-4 pivot. -/
public theorem pass_pivot_dvd_leftPivot {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (pass A hdet).result 0 0 ∣ (leftHermitePhase A).result 0 0 := by
  simpa [pass, compose] using rightHermitePhase_pivot_dvd_entry
    (leftHermitePhase A).result
    (result_det_ne_zero (leftHermitePhase A) hdet) 0

/-- The final pivot of a full pass divides every original first-column entry. -/
public theorem pass_pivot_dvd_entry {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (row : Fin (n + 1)) :
    (pass A hdet).result 0 0 ∣ A row 0 :=
  dvd_trans (pass_pivot_dvd_leftPivot A hdet)
    (leftHermitePhase_pivot_dvd_entry A hdet row)

/-- A common divisor of the first column divides the determinant. -/
public theorem dvd_det_of_dvd_column_zero {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) {divisor : Int}
    (hdivides : ∀ row, divisor ∣ A row 0) : divisor ∣ A.det := by
  rw [_root_.Matrix.det_succ_column_zero]
  apply Finset.dvd_sum
  intro row _membership
  rcases hdivides row with ⟨coefficient, equality⟩
  refine ⟨(-1 : Int) ^ (row : Nat) * coefficient *
    (A.submatrix row.succAbove Fin.succ).det, ?_⟩
  rw [equality]
  ring

/-- The pivot produced by a full pass divides the input determinant. -/
public theorem pass_pivot_dvd_det {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (pass A hdet).result 0 0 ∣ A.det :=
  dvd_det_of_dvd_column_zero A (pass_pivot_dvd_entry A hdet)

/-- The first pass pivot fits within the input determinant's binary length. -/
public theorem pass_pivotBitLength_le_determinant {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    ((pass A hdet).result 0 0).natAbs.size ≤
      integerBitLength A.det := by
  have absLe : ((pass A hdet).result 0 0).natAbs ≤ A.det.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hdet)
      (Int.natAbs_dvd_natAbs.mpr (pass_pivot_dvd_det A hdet))
  exact Nat.size_le_size absLe

/-- A common proper divisor has strictly smaller absolute value. -/
public theorem natAbs_lt_of_dvd_dvd_not_dvd {pivot next entry : Int}
    (hpivot : pivot ≠ 0) (next_dvd_pivot : next ∣ pivot)
    (next_dvd_entry : next ∣ entry)
    (pivot_not_dvd_entry : ¬ pivot ∣ entry) :
    next.natAbs < pivot.natAbs := by
  have nextNatDvdPivot : next.natAbs ∣ pivot.natAbs :=
    Int.natAbs_dvd_natAbs.mpr next_dvd_pivot
  have le : next.natAbs ≤ pivot.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hpivot) nextNatDvdPivot
  apply Nat.lt_of_le_of_ne le
  intro equal
  have pivotNatDvdNext : pivot.natAbs ∣ next.natAbs := by
    rw [equal]
  have pivotDvdNext : pivot ∣ next :=
    Int.natAbs_dvd_natAbs.mp pivotNatDvdNext
  exact pivot_not_dvd_entry (dvd_trans pivotDvdNext next_dvd_entry)

/-- Doubling a positive natural strictly raises its binary-size envelope. -/
public theorem natSize_lt_of_two_mul_le {smaller larger : Nat}
    (smaller_pos : 0 < smaller) (double_le : 2 * smaller ≤ larger) :
    smaller.size < larger.size := by
  rw [Nat.lt_size]
  have sizePos : 0 < smaller.size := Nat.size_pos.mpr smaller_pos
  have lowerPower : 2 ^ (smaller.size - 1) ≤ smaller :=
    Nat.lt_size.mp (by omega)
  calc
    2 ^ smaller.size = 2 ^ (smaller.size - 1 + 1) := by
      congr 1
      omega
    _ = 2 ^ (smaller.size - 1) * 2 := by rw [pow_succ]
    _ ≤ smaller * 2 := Nat.mul_le_mul_right 2 lowerPower
    _ = 2 * smaller := by omega
    _ ≤ larger := double_le

/-- A proper nonzero divisor is at most half the dividend in absolute value. -/
public theorem natAbs_two_mul_le_of_dvd_dvd_not_dvd
    {pivot next entry : Int} (hpivot : pivot ≠ 0)
    (next_dvd_pivot : next ∣ pivot) (next_dvd_entry : next ∣ entry)
    (pivot_not_dvd_entry : ¬ pivot ∣ entry) :
    2 * next.natAbs ≤ pivot.natAbs := by
  have nextNatDvdPivot : next.natAbs ∣ pivot.natAbs :=
    Int.natAbs_dvd_natAbs.mpr next_dvd_pivot
  rcases nextNatDvdPivot with ⟨factor, factorEq⟩
  have pivotPos : 0 < pivot.natAbs := Int.natAbs_pos.mpr hpivot
  have nextPos : 0 < next.natAbs := by
    rw [factorEq] at pivotPos
    exact Nat.pos_of_mul_pos_right pivotPos
  have strict := natAbs_lt_of_dvd_dvd_not_dvd hpivot
    next_dvd_pivot next_dvd_entry pivot_not_dvd_entry
  have factorTwo : 2 ≤ factor := by
    by_contra notTwo
    have factorLt : factor < 2 := by omega
    interval_cases factor <;> simp_all
  calc
    2 * next.natAbs ≤ factor * next.natAbs :=
      Nat.mul_le_mul_right next.natAbs factorTwo
    _ = pivot.natAbs := by simpa [mul_comm] using factorEq.symm

/-- A proper nonzero divisor has strictly smaller binary size. -/
public theorem natAbs_size_lt_of_dvd_dvd_not_dvd
    {pivot next entry : Int} (hpivot : pivot ≠ 0)
    (next_dvd_pivot : next ∣ pivot) (next_dvd_entry : next ∣ entry)
    (pivot_not_dvd_entry : ¬ pivot ∣ entry) :
    next.natAbs.size < pivot.natAbs.size := by
  have nextNe : next ≠ 0 := by
    intro nextZero
    subst next
    exact hpivot (zero_dvd_iff.mp next_dvd_pivot)
  exact natSize_lt_of_two_mul_le (Int.natAbs_pos.mpr nextNe)
    (natAbs_two_mul_le_of_dvd_dvd_not_dvd hpivot next_dvd_pivot
      next_dvd_entry pivot_not_dvd_entry)

/--
If one first-column entry is not divisible by the current nonzero pivot, the
next full pass strictly decreases the pivot's absolute value.
-/
public theorem pass_pivot_natAbs_lt_of_not_dvd_entry {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (row : Fin (n + 1)) (hnot : ¬ A 0 0 ∣ A row 0) :
    ((pass A hdet).result 0 0).natAbs < (A 0 0).natAbs :=
  natAbs_lt_of_dvd_dvd_not_dvd hpivot
    (pass_pivot_dvd_entry A hdet 0)
    (pass_pivot_dvd_entry A hdet row) hnot

/-- Every genuine continuation decreases the pivot's binary size by a level. -/
public theorem pass_pivot_natSize_lt_of_not_dvd_entry {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (row : Fin (n + 1)) (hnot : ¬ A 0 0 ∣ A row 0) :
    ((pass A hdet).result 0 0).natAbs.size < (A 0 0).natAbs.size :=
  natAbs_size_lt_of_dvd_dvd_not_dvd hpivot
    (pass_pivot_dvd_entry A hdet 0)
    (pass_pivot_dvd_entry A hdet row) hnot

/-- The first pass pivot cannot exceed the input matrix's binary width. -/
public theorem pass_pivotBitLength_le_input {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    ((pass A hdet).result 0 0).natAbs.size ≤
      matrixBitLength A := by
  have columnNonzero := firstColumn_ne_zero_of_det_ne A hdet
  have existsEntry : ∃ row : Fin (n + 1), A row 0 ≠ 0 := by
    by_contra noEntry
    push Not at noEntry
    apply columnNonzero
    ext row column
    fin_cases column
    exact noEntry row
  obtain ⟨row, entryNonzero⟩ := existsEntry
  have pivotDvdEntry := pass_pivot_dvd_entry A hdet row
  have absLe : ((pass A hdet).result 0 0).natAbs ≤ (A row 0).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr entryNonzero)
      (Int.natAbs_dvd_natAbs.mpr pivotDvdEntry)
  exact (Nat.size_le_size absLe).trans
    (entry_bitLength_le_matrixBitLength A row 0)

end NormalForms.Research.KannanBachem.Smith
