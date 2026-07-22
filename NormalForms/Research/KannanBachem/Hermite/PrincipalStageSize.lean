/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalPrefix
public import NormalForms.Research.KannanBachem.Hermite.PrincipalFinalSize
import all NormalForms.Research.KannanBachem.Hermite.PrincipalFinalSize
import all NormalForms.Research.KannanBachem.Hermite.PrincipalPrefix
import all NormalForms.Research.KannanBachem.Hermite.PrincipalCorrectness
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal

/-! Polynomial reset bounds at the beginning of every principal stage. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix BigOperators
open NormalForms.Matrix.Certificates

namespace Principal

/-- Bit-length budget for the completed leading HNF block of a stage. -/
@[expose] public def stageLeadingBitLengthBound
    (k inputBits : Nat) : Nat :=
  determinantBitLengthBound k inputBits

/-- Bit-length budget for the leading block of the accumulated multiplier. -/
@[expose] public def stageLeadingMultiplierBitLengthBound
    (k inputBits : Nat) : Nat :=
  match k with
  | 0 => 0
  | order + 1 =>
      Nat.size (order + 1) +
        stageLeadingBitLengthBound (order + 1) inputBits +
        determinantBitLengthBound order inputBits

/-- Bit-length budget for all processed rows at a stage boundary. -/
@[expose] public def stageProcessedRowsBitLengthBound
    (k inputBits : Nat) : Nat :=
  match k with
  | 0 => 0
  | _ + 1 =>
      Nat.size k + stageLeadingMultiplierBitLengthBound k inputBits + inputBits

/-- Uniform bit-length reset budget for a complete stage-boundary matrix. -/
@[expose] public def stageStartBitLengthBound
    (k inputBits : Nat) : Nat :=
  max inputBits (stageProcessedRowsBitLengthBound k inputBits)

theorem stageLoop_refl_leading_det_natAbs_eq {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n) :
    (leadingSubmatrix hk
        (stageLoop k hk (State.refl A)).transform.B).det.natAbs =
      (leadingSubmatrix hk A).det.natAbs := by
  let stage := stageLoop k hk (State.refl A)
  let leadingU := leadingSubmatrix hk stage.transform.U
  let leadingA := leadingSubmatrix hk A
  let leadingB := leadingSubmatrix hk stage.transform.B
  have equation : leadingU * leadingA = leadingB :=
    stageLoop_refl_leadingSquare_equation A hk
  have unitDet : IsUnit leadingU.det :=
    (stage.transform.leadingSubmatrixCertificate hk
      (stageLoop_refl_actsWithinPrefix A hk)).unimodular
  change leadingB.det.natAbs = leadingA.det.natAbs
  calc
    leadingB.det.natAbs = (leadingU * leadingA).det.natAbs := by
      rw [equation]
    _ = leadingU.det.natAbs * leadingA.det.natAbs := by
      rw [_root_.Matrix.det_mul, Int.natAbs_mul]
    _ = leadingA.det.natAbs := by
      rw [Int.isUnit_iff_natAbs_eq.mp unitDet, one_mul]

/-- The completed leading HNF block obeys the input-minor determinant bound. -/
theorem stageLoop_refl_leading_bitLength_le {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n)
    (ready : PrincipalReady A) :
    matrixBitLength
        (leadingSubmatrix hk
          (stageLoop k hk (State.refl A)).transform.B) ≤
      stageLeadingBitLengthBound k (matrixBitLength A) := by
  let leadingB := leadingSubmatrix hk
    (stageLoop k hk (State.refl A)).transform.B
  let leadingA := leadingSubmatrix hk A
  have hprefix : PrefixHermite k leadingB :=
    stageLoop_refl_leading_prefix A hk
  have det_ne : leadingB.det ≠ 0 :=
    stageLoop_refl_leading_det_ne A hk ready
  have heightBound : matrixHeight leadingB ≤ leadingB.det.natAbs :=
    hprefix.matrixHeight_le_det_natAbs
      (hprefix.diagonal_ne_of_det_ne det_ne)
  have inputSubmatrixBits : matrixBitLength leadingA ≤ matrixBitLength A :=
    submatrix_bitLength_le A (Fin.castLE hk) (Fin.castLE hk)
  change matrixBitLength leadingB ≤
    determinantBitLengthBound k (matrixBitLength A)
  calc
    matrixBitLength leadingB ≤ integerBitLength leadingB.det :=
      Nat.size_le_size heightBound
    _ = integerBitLength leadingA.det := by
      exact congrArg Nat.size (stageLoop_refl_leading_det_natAbs_eq A hk)
    _ ≤ determinantBitLengthBound k (matrixBitLength leadingA) :=
      determinant_bitLength_le leadingA
    _ ≤ determinantBitLengthBound k (matrixBitLength A) := by
      unfold determinantBitLengthBound
      gcongr

/-- Cramer's rule bounds the leading multiplier at every ready stage boundary. -/
theorem stageLoop_refl_leading_multiplier_bitLength_le {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n)
    (ready : PrincipalReady A) :
    matrixBitLength
        (leadingSubmatrix hk
          (stageLoop k hk (State.refl A)).transform.U) ≤
      stageLeadingMultiplierBitLengthBound k (matrixBitLength A) := by
  cases k with
  | zero =>
      have hzero : leadingSubmatrix hk
          (stageLoop 0 hk (State.refl A)).transform.U =
          (0 : _root_.Matrix (Fin 0) (Fin 0) Int) :=
        Subsingleton.elim _ _
      rw [hzero, matrixBitLength_zero]
      rfl
  | succ order =>
      let stage := stageLoop (order + 1) hk (State.refl A)
      let leadingU := leadingSubmatrix hk stage.transform.U
      let leadingA := leadingSubmatrix hk A
      let leadingB := leadingSubmatrix hk stage.transform.B
      have equation : leadingU * leadingA = leadingB :=
        stageLoop_refl_leadingSquare_equation A hk
      have multiplier := leftMultiplier_bitLength_le_of_mul_eq
        leadingA leadingU leadingB equation (ready (order + 1) hk)
      have leadingBits := stageLoop_refl_leading_bitLength_le A hk ready
      change matrixBitLength leadingB ≤
        determinantBitLengthBound (order + 1) (matrixBitLength A)
        at leadingBits
      have inputSubmatrixBits : matrixBitLength leadingA ≤ matrixBitLength A :=
        submatrix_bitLength_le A (Fin.castLE hk) (Fin.castLE hk)
      have previousMinorBits :
          determinantBitLengthBound order (matrixBitLength leadingA) ≤
            determinantBitLengthBound order (matrixBitLength A) := by
        unfold determinantBitLengthBound
        gcongr
      change matrixBitLength leadingU ≤ _
      exact multiplier.trans <| by
        simp only [stageLeadingMultiplierBitLengthBound,
          stageLeadingBitLengthBound]
        omega

/-- All processed rows inherit the leading multiplier's Cramer bound. -/
theorem stageLoop_refl_processedRows_bitLength_le {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n)
    (ready : PrincipalReady A) :
    matrixBitLength
        ((stageLoop k hk (State.refl A)).transform.B.submatrix
          (Fin.castLE hk) id) ≤
      stageProcessedRowsBitLengthBound k (matrixBitLength A) := by
  cases k with
  | zero =>
      have hzero :
          (stageLoop 0 hk (State.refl A)).transform.B.submatrix
              (Fin.castLE hk) id =
            (0 : _root_.Matrix (Fin 0) (Fin n) Int) :=
        Subsingleton.elim _ _
      rw [hzero, matrixBitLength_zero]
      rfl
  | succ order =>
      let stage := stageLoop (order + 1) hk (State.refl A)
      let leadingU := leadingSubmatrix hk stage.transform.U
      let inputRows := A.submatrix (Fin.castLE hk) id
      let processedRows := stage.transform.B.submatrix (Fin.castLE hk) id
      have equation : leadingU * inputRows = processedRows :=
        stage.transform.leadingSubmatrix_equation hk
          (stageLoop_refl_actsWithinPrefix A hk)
      have multiplierBits :=
        stageLoop_refl_leading_multiplier_bitLength_le A hk ready
      change matrixBitLength leadingU ≤
        stageLeadingMultiplierBitLengthBound (order + 1)
          (matrixBitLength A) at multiplierBits
      have inputRowsBits : matrixBitLength inputRows ≤ matrixBitLength A :=
        submatrix_bitLength_le A (Fin.castLE hk) id
      change matrixBitLength processedRows ≤ _
      rw [← equation]
      exact (matrix_mul_bitLength_le leadingU inputRows).trans <| by
        simp only [stageProcessedRowsBitLengthBound]
        omega

theorem stageLoop_refl_height_le_input_max_processed {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n) :
    matrixHeight (stageLoop k hk (State.refl A)).transform.B ≤
      max (matrixHeight A)
        (matrixHeight
          ((stageLoop k hk (State.refl A)).transform.B.submatrix
            (Fin.castLE hk) id)) := by
  apply matrixHeight_le
  intro row column
  by_cases hrow : row.val < k
  · let prefixRow : Fin k := ⟨row.val, hrow⟩
    have castRow : Fin.castLE hk prefixRow = row := Fin.ext rfl
    rw [← castRow]
    exact (entry_natAbs_le_matrixHeight
      ((stageLoop k hk (State.refl A)).transform.B.submatrix
        (Fin.castLE hk) id) prefixRow column).trans (le_max_right _ _)
  · rw [stageLoop_refl_unprocessed_row A hk row column (by omega)]
    exact (entry_natAbs_le_matrixHeight A row column).trans (le_max_left _ _)

theorem natSize_max (left right : Nat) :
    Nat.size (max left right) = max (Nat.size left) (Nat.size right) := by
  rcases le_total left right with h | h
  · rw [max_eq_right h, max_eq_right (Nat.size_le_size h)]
  · rw [max_eq_left h, max_eq_left (Nat.size_le_size h)]

/-- Every stage boundary resets the full matrix to a polynomial bit budget. -/
theorem stageLoop_refl_bitLength_le {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n)
    (ready : PrincipalReady A) :
    matrixBitLength (stageLoop k hk (State.refl A)).transform.B ≤
      stageStartBitLengthBound k (matrixBitLength A) := by
  have heightBound := stageLoop_refl_height_le_input_max_processed A hk
  have processedBits := stageLoop_refl_processedRows_bitLength_le A hk ready
  unfold matrixBitLength at heightBound ⊢
  unfold stageStartBitLengthBound
  exact (Nat.size_le_size heightBound).trans <| by
    rw [natSize_max]
    exact max_le_max le_rfl processedBits

end Principal

end NormalForms.Research.KannanBachem.Hermite
