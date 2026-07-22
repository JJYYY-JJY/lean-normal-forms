/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Shape
import all NormalForms.Research.ModularHNF.Shape
import all NormalForms.Matrix.Smith.Uniqueness

/-!
# Canonical-reference facts for modular HNF

The correctness proof compares the raw modular candidate with the certified
core HNF.  This file establishes the full-column shape and suffix-determinant
facts needed by that comparison, without exposing the core algorithm inside
the modular kernel.
-/

public section

namespace NormalForms.Research.ModularHNF

open scoped BigOperators Matrix
open NormalForms.Matrix.Hermite

theorem lowerRight_cols_linearIndependent {m n : Nat}
    (M : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) Rat)
    (topLeftNonzero : M 0 0 ≠ 0)
    (belowZero : ∀ i : Fin m, M i.succ 0 = 0)
    (independent : LinearIndependent Rat M.col) :
    LinearIndependent Rat
      (fun j : Fin n => fun i : Fin m => M i.succ j.succ) := by
  rw [Fintype.linearIndependent_iff] at independent ⊢
  intro coeff combinationZero column
  let topSum := ∑ j : Fin n, coeff j * M 0 j.succ
  let lifted : Fin (n + 1) → Rat :=
    Fin.cases (-topSum / M 0 0) coeff
  have liftedZero : ∑ j : Fin (n + 1), lifted j • M.col j = 0 := by
    ext row
    cases row using Fin.cases with
    | zero =>
        rw [Fin.sum_univ_succ]
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          _root_.Matrix.col, Pi.zero_apply]
        change lifted 0 * M 0 0 + ∑ j : Fin n, lifted j.succ * M 0 j.succ = 0
        simp only [lifted, Fin.cases_zero, Fin.cases_succ]
        change (-topSum / M 0 0) * M 0 0 + topSum = 0
        rw [div_mul_cancel₀ _ topLeftNonzero]
        ring
    | succ row =>
        rw [Fin.sum_univ_succ]
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          _root_.Matrix.col, Pi.zero_apply]
        change lifted 0 * M row.succ 0 +
          ∑ j : Fin n, lifted j.succ * M row.succ j.succ = 0
        simp only [lifted, Fin.cases_zero, Fin.cases_succ, belowZero, mul_zero,
          zero_add]
        have entry := congrFun combinationZero row
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] using entry
  have coefficientZero := independent lifted liftedZero column.succ
  simpa [lifted] using coefficientZero

/-- A full-column-rank HNF has a positive pivot in every column and a zero row tail. -/
theorem hnf_fullColumnShape :
    ∀ {m n : Nat} (H : _root_.Matrix (Fin m) (Fin n) Int)
      (columns_le_rows : n ≤ m),
      IsHermiteNormalFormFin H →
      LinearIndependent Rat (H.map (Int.castRingHom Rat)).col →
      PrefixRowsZero H n ∧
        ∀ column,
          ColumnHermiteShape H (Fin.castLE columns_le_rows column) column := by
  intro m n
  induction n generalizing m with
  | zero =>
      intro H columns_le_rows _isHermite _independent
      constructor
      · intro _ _ column
        exact Fin.elim0 column
      · intro column
        exact Fin.elim0 column
  | succ n ih =>
      intro H columns_le_rows isHermite independent
      cases m with
      | zero => omega
      | succ m =>
          cases isHermite with
          | zeroCol _A firstZero _tailHermite =>
              have mappedFirstZero :
                  (H.map (Int.castRingHom Rat)).col 0 = 0 := by
                ext row
                simp [firstZero]
              exact False.elim
                ((independent.ne_zero 0) mappedFirstZero)
          | pivot _A pivotNonzero pivotNormalized belowZero lowerHermite reduced =>
              have lowerColumnsLeRows : n ≤ m := by omega
              have mappedTopLeftNonzero :
                  (H.map (Int.castRingHom Rat)) 0 0 ≠ 0 := by
                simpa using pivotNonzero
              have mappedBelowZero : ∀ row : Fin m,
                  (H.map (Int.castRingHom Rat)) row.succ 0 = 0 := by
                intro row
                simp [belowZero]
              have lowerIndependent : LinearIndependent Rat
                  ((lowerRight H).map (Int.castRingHom Rat)).col := by
                have lower := lowerRight_cols_linearIndependent
                  (H.map (Int.castRingHom Rat)) mappedTopLeftNonzero
                    mappedBelowZero independent
                change LinearIndependent Rat
                  (fun j : Fin n => fun i : Fin m =>
                    (Int.castRingHom Rat) (H i.succ j.succ))
                exact lower
              have lowerSpec := ih (lowerRight H) lowerColumnsLeRows
                lowerHermite lowerIndependent
              have lowerZeroTail := lowerSpec.1
              have lowerShape := lowerSpec.2
              constructor
              · intro row rowAfter column columnBefore
                cases row using Fin.cases with
                | zero => simp at rowAfter
                | succ row =>
                    cases column using Fin.cases with
                    | zero => exact belowZero row
                    | succ column =>
                        exact lowerZeroTail row
                          (Nat.le_of_succ_le_succ rowAfter) column
                          (Nat.lt_of_succ_lt_succ columnBefore)
              · intro column
                cases column using Fin.cases with
                | zero =>
                    have pivotEq :
                        Fin.castLE columns_le_rows (0 : Fin (n + 1)) =
                          (0 : Fin (m + 1)) := by
                      apply Fin.ext
                      rfl
                    rw [pivotEq]
                    refine
                      { pivot_positive := ?_
                        pivot_normalized := pivotNormalized
                        below_zero := ?_
                        above_reduced := ?_ }
                    · have nonnegative : 0 ≤ H 0 0 :=
                        Int.nonneg_of_normalize_eq_self pivotNormalized.symm
                      exact lt_of_le_of_ne nonnegative (Ne.symm pivotNonzero)
                    · intro row zeroBeforeRow
                      cases row using Fin.cases with
                      | zero => exact (lt_irrefl _ zeroBeforeRow).elim
                      | succ row => exact belowZero row
                    · intro row rowBeforeZero
                      exact (Fin.not_lt_zero row rowBeforeZero).elim
                | succ column =>
                    let lowerPivot := Fin.castLE lowerColumnsLeRows column
                    have pivotEq :
                        Fin.castLE columns_le_rows column.succ =
                          lowerPivot.succ := by
                      apply Fin.ext
                      rfl
                    rw [pivotEq]
                    have thisShape := lowerShape column
                    refine
                      { pivot_positive := by
                          simpa [lowerRight] using thisShape.pivot_positive
                        pivot_normalized := by
                          simpa [lowerRight] using thisShape.pivot_normalized
                        below_zero := ?_
                        above_reduced := ?_ }
                    · intro row pivotBeforeRow
                      cases row using Fin.cases with
                      | zero =>
                          exact (Fin.not_lt_zero lowerPivot.succ pivotBeforeRow).elim
                      | succ row =>
                          have lowerBefore : lowerPivot < row :=
                            Fin.succ_lt_succ_iff.mp pivotBeforeRow
                          simpa [lowerRight] using
                            thisShape.below_zero row lowerBefore
                    · intro row rowBeforePivot
                      cases row using Fin.cases with
                      | zero =>
                          have lowerPivotNonzero :
                              (fun current : Fin n =>
                                H lowerPivot.succ current.succ) column ≠ 0 := by
                            simpa [lowerRight] using
                              ne_of_gt thisShape.pivot_positive
                          have lowerPrefixZero : ∀ current, current < column →
                              H lowerPivot.succ current.succ = 0 := by
                            intro current currentBefore
                            have currentShape := lowerShape current
                            have currentPivotBefore :
                                Fin.castLE lowerColumnsLeRows current < lowerPivot := by
                              change current.val < column.val
                              exact currentBefore
                            simpa [lowerRight] using
                              currentShape.below_zero lowerPivot currentPivotBefore
                          have firstNonzero :=
                            firstNonzero?_eq_some_of_prefix_zero
                              (fun current : Fin n =>
                                H lowerPivot.succ current.succ)
                              column lowerPivotNonzero lowerPrefixZero
                          have topReduced := reduced lowerPivot
                          rw [firstNonzero] at topReduced
                          simpa [lowerRight] using topReduced
                      | succ row =>
                          have lowerBefore : row < lowerPivot :=
                            Fin.succ_lt_succ_iff.mp rowBeforePivot
                          simpa [lowerRight] using
                            thisShape.above_reduced row lowerBefore

theorem cols_linearIndependent_of_rank_eq_width {m n : Nat}
    (M : _root_.Matrix (Fin m) (Fin n) Rat)
    (rankEq : M.rank = n) :
    LinearIndependent Rat M.col := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  rw [Fintype.card_fin]
  simpa [Set.finrank, ← _root_.Matrix.rank_eq_finrank_span_cols] using rankEq.symm

/-- The certified HNF of a full-column-rank matrix still has rational rank `n`. -/
theorem reference_rank_eq_width {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A) :
    let result := hermiteNormalFormFin A
    (result.H.map (Int.castRingHom Rat)).rank = n := by
  let result := hermiteNormalFormFin A
  let inverseRat := result.U_cert.inverse.map (Int.castRingHom Rat)
  let hermiteRat := result.H.map (Int.castRingHom Rat)
  have recover : result.U_cert.inverse * result.H = A := by
    calc
      result.U_cert.inverse * result.H =
          result.U_cert.inverse * (result.U * A) := by rw [result.equation]
      _ = (result.U_cert.inverse * result.U) * A := by
        rw [_root_.Matrix.mul_assoc]
      _ = A := by rw [result.U_cert.left_inv]; simp
  have mappedRecover : inverseRat * hermiteRat =
      A.map (Int.castRingHom Rat) := by
    change result.U_cert.inverse.map (Int.castRingHom Rat) *
        result.H.map (Int.castRingHom Rat) = A.map (Int.castRingHom Rat)
    rw [← _root_.Matrix.map_mul]
    exact congrArg (fun M => M.map (Int.castRingHom Rat)) recover
  have lower : n ≤ hermiteRat.rank := by
    calc
      n = (A.map (Int.castRingHom Rat)).rank :=
        fullRank.rational_rank_eq.symm
      _ = (inverseRat * hermiteRat).rank := by rw [mappedRecover]
      _ ≤ hermiteRat.rank :=
        _root_.Matrix.rank_mul_le_right inverseRat hermiteRat
  exact le_antisymm (_root_.Matrix.rank_le_width hermiteRat) lower

/-- Square diagonal suffix cut from the first `n` rows of a tall matrix. -/
@[expose] def suffixSquare {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (k : Nat) :
    _root_.Matrix (SuffixIndex n k) (SuffixIndex n k) Int :=
  A.submatrix
    (fun row => Fin.castLE columns_le_rows row.1)
    (fun column => column.1)

/-- A suffix determinant times a live coordinate vector lies in the row lattice. -/
theorem suffixDet_smul_single_mem_rowSpan {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (k : Nat)
    (prefixZero : PrefixRowsZero A k)
    (column : SuffixIndex n k) :
    (suffixSquare A columns_le_rows k).det •
        Pi.single column.1 (1 : Int) ∈ rowSpan A := by
  let B := suffixSquare A columns_le_rows k
  let basis : Fin n → Int := Pi.single column.1 (1 : Int)
  change B.det • basis ∈ rowSpan A
  have equality :
      B.det • basis =
        ∑ row : SuffixIndex n k,
          B.adjugate column row •
            A.row (Fin.castLE columns_le_rows row.1) := by
    ext currentColumn
    by_cases before : currentColumn.val < k
    · have currentNe : currentColumn ≠ column.1 := by
        intro equal
        subst equal
        omega
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_zero]
      · simp [basis, currentNe]
      · intro row _
        have selectedAfter : k ≤
            (Fin.castLE columns_le_rows row.1).val := by
          simpa using row.2
        change B.adjugate column row *
          A (Fin.castLE columns_le_rows row.1) currentColumn = 0
        rw [prefixZero (Fin.castLE columns_le_rows row.1) selectedAfter
          currentColumn before]
        simp
    · let currentSuffix : SuffixIndex n k :=
        ⟨currentColumn, Nat.le_of_not_gt before⟩
      have entry := congrArg
        (fun M : _root_.Matrix (SuffixIndex n k) (SuffixIndex n k) Int =>
          M column currentSuffix)
        (_root_.Matrix.adjugate_mul B)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        _root_.Matrix.row]
      change B.det * basis currentColumn =
        ∑ row : SuffixIndex n k,
          B.adjugate column row * A (Fin.castLE columns_le_rows row.1)
            currentColumn
      have entry' :
          ∑ row : SuffixIndex n k,
              B.adjugate column row * B row currentSuffix =
            B.det * (1 : _root_.Matrix (SuffixIndex n k)
              (SuffixIndex n k) Int) column currentSuffix := by
        simpa [_root_.Matrix.mul_apply, Pi.smul_apply, smul_eq_mul] using entry
      have selectedEq : ∀ row : SuffixIndex n k,
          A (Fin.castLE columns_le_rows row.1) currentColumn =
            B row currentSuffix := by
        intro row
        rfl
      simp_rw [selectedEq]
      rw [entry']
      by_cases currentEq : currentColumn = column.1
      · subst currentColumn
        simp [basis, currentSuffix]
      · have subtypeNe : column ≠ currentSuffix := by
          intro equal
          apply currentEq
          exact congrArg Subtype.val equal.symm
        simp [basis, currentEq, subtypeNe]
  rw [equality]
  exact Submodule.sum_mem _ fun row _ =>
    Submodule.smul_mem _ _
      (row_mem_rowSpan A (Fin.castLE columns_le_rows row.1))

/-- The suffix determinant is the product of the remaining positive pivots. -/
theorem suffixSquare_det_eq_prod {m n k : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m)
    (shape : ProcessedHermiteShape columns_le_rows A n) :
    (suffixSquare A columns_le_rows k).det =
      ∏ column : SuffixIndex n k,
        A (Fin.castLE columns_le_rows column.1) column.1 := by
  apply _root_.Matrix.det_of_upperTriangular
  intro row column columnBeforeRow
  have originalShape := shape column.1 column.1.isLt
  have pivotBeforeRow :
      Fin.castLE columns_le_rows column.1 <
        Fin.castLE columns_le_rows row.1 := by
    change column.1.val < row.1.val
    exact columnBeforeRow
  exact originalShape.below_zero
    (Fin.castLE columns_le_rows row.1) pivotBeforeRow

theorem suffixSquare_det_step {m n k : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m)
    (shape : ProcessedHermiteShape columns_le_rows A n)
    (beforeEnd : k < n) :
    (suffixSquare A columns_le_rows k).det =
      A (Fin.castLE columns_le_rows ⟨k, beforeEnd⟩) ⟨k, beforeEnd⟩ *
        (suffixSquare A columns_le_rows (k + 1)).det := by
  let pivot : Fin n := ⟨k, beforeEnd⟩
  let diagonal : Fin n → Int := fun column =>
    A (Fin.castLE columns_le_rows column) column
  have productAt :
      (∏ column : SuffixIndex n k, diagonal column.1) =
        ∏ column ∈ Finset.univ.filter (fun column : Fin n => k ≤ column.val),
          diagonal column := by
    symm
    exact Finset.prod_subtype
      (Finset.univ.filter (fun column : Fin n => k ≤ column.val))
      (fun column => by simp) diagonal
  have productNext :
      (∏ column : SuffixIndex n (k + 1), diagonal column.1) =
        ∏ column ∈
          Finset.univ.filter (fun column : Fin n => k + 1 ≤ column.val),
          diagonal column := by
    symm
    exact Finset.prod_subtype
      (Finset.univ.filter (fun column : Fin n => k + 1 ≤ column.val))
      (fun column => by simp) diagonal
  have filterEq :
      Finset.univ.filter (fun column : Fin n => k ≤ column.val) =
        insert pivot
          (Finset.univ.filter (fun column : Fin n => k + 1 ≤ column.val)) := by
    ext column
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro after
      by_cases equal : column = pivot
      · exact Or.inl equal
      · exact Or.inr (by
          have valueNe : column.val ≠ k := by
            intro valueEq
            apply equal
            apply Fin.ext
            simpa [pivot] using valueEq
          omega)
    · rintro (equal | after)
      · subst column
        simp [pivot]
      · omega
  have pivotNotNext :
      pivot ∉ Finset.univ.filter
        (fun column : Fin n => k + 1 ≤ column.val) := by
    simp [pivot]
  rw [suffixSquare_det_eq_prod A columns_le_rows shape,
    suffixSquare_det_eq_prod A columns_le_rows shape,
    productAt, productNext, filterEq, Finset.prod_insert pivotNotNext]

theorem suffixSquare_det_positive {m n k : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m)
    (shape : ProcessedHermiteShape columns_le_rows A n) :
    0 < (suffixSquare A columns_le_rows k).det := by
  rw [suffixSquare_det_eq_prod A columns_le_rows shape]
  exact Finset.prod_pos fun column _ =>
    (shape column.1 column.1.isLt).pivot_positive

/-- The full suffix determinant divides every full-width minor of its HNF. -/
theorem suffixDet_dvd_rowMinor {m n : Nat}
    (H : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m)
    (zeroTail : PrefixRowsZero H n)
    (shape : ProcessedHermiteShape columns_le_rows H n)
    (rows : Fin n ↪ Fin m) :
    (suffixSquare H columns_le_rows 0).det ∣
      (H.submatrix rows id).det := by
  by_cases allTop : ∀ row : Fin n, (rows row).val < n
  · let rowFin : Fin n → Fin n := fun row => ⟨(rows row).val, allTop row⟩
    have rowFinInjective : Function.Injective rowFin := by
      intro left right equal
      apply rows.injective
      apply Fin.ext
      simpa [rowFin] using congrArg Fin.val equal
    have rowFinBijective : Function.Bijective rowFin :=
      (Fintype.bijective_iff_injective_and_card rowFin).2
        ⟨rowFinInjective, by simp⟩
    let permutation : Equiv.Perm (Fin n) :=
      Equiv.ofBijective rowFin rowFinBijective
    let topSquare : _root_.Matrix (Fin n) (Fin n) Int :=
      H.submatrix (Fin.castLE columns_le_rows) id
    have matrixEq :
        H.submatrix rows id =
          topSquare.submatrix permutation id := by
      ext row column
      rfl
    rw [matrixEq, _root_.Matrix.det_permute]
    refine dvd_mul_of_dvd_right ?_ _
    rw [suffixSquare_det_eq_prod H columns_le_rows shape]
    change (∏ column : SuffixIndex n 0,
      H (Fin.castLE columns_le_rows column.1) column.1) ∣ topSquare.det
    rw [_root_.Matrix.det_of_upperTriangular]
    · let diagonal : Fin n → Int := fun column =>
        H (Fin.castLE columns_le_rows column) column
      have productAll :
          (∏ column : SuffixIndex n 0, diagonal column.1) =
            ∏ column : Fin n, diagonal column := by
        symm
        exact Finset.prod_subtype Finset.univ (fun column => by simp) diagonal
      simp [topSquare, diagonal, productAll]
    · intro row column columnBeforeRow
      exact (shape column column.isLt).below_zero
        (Fin.castLE columns_le_rows row) (by
          change column.val < row.val
          exact columnBeforeRow)
  · push Not at allTop
    obtain ⟨row, rowAfter⟩ := allTop
    rw [_root_.Matrix.det_eq_zero_of_row_eq_zero row]
    · exact dvd_zero _
    · intro column
      exact zeroTail (rows row) rowAfter column column.isLt

/-- The reference HNF determinant divides the caller-selected input minor. -/
theorem reference_initialDet_dvd_selectedMinor {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A) :
    let result := hermiteNormalFormFin A
    (suffixSquare result.H fullRank.columns_le_rows 0).det ∣
      (selectedSquareMinor A fullRank.rows).det := by
  let result := hermiteNormalFormFin A
  let inverse := result.U_cert.inverse
  let identity : Fin n ↪ Fin n := Function.Embedding.refl _
  have recover : inverse * result.H = A := by
    calc
      inverse * result.H = inverse * (result.U * A) := by
        rw [result.equation]
      _ = (inverse * result.U) * A := by
        rw [_root_.Matrix.mul_assoc]
      _ = A := by
        rw [result.U_cert.left_inv]
        simp
  have referenceShape := hnf_fullColumnShape result.H
    fullRank.columns_le_rows result.isHermite
    (cols_linearIndependent_of_rank_eq_width _
      (reference_rank_eq_width A fullRank))
  change (suffixSquare result.H fullRank.columns_le_rows 0).det ∣
    (A.submatrix fullRank.rows id).det
  have selectedRecover :
      (A.submatrix fullRank.rows id).det =
        ((inverse * result.H).submatrix fullRank.rows id).det :=
    congrArg (fun M => (M.submatrix fullRank.rows id).det) recover.symm
  rw [selectedRecover]
  have transposeDet :
      ((inverse * result.H).submatrix fullRank.rows id).det =
        ((result.H.transpose * inverse.transpose).submatrix
          identity fullRank.rows).det := by
    rw [← _root_.Matrix.det_transpose]
    congr 1
    ext row column
    have entry := congrFun
      (congrFun (_root_.Matrix.transpose_mul inverse result.H) row)
      (fullRank.rows column)
    simpa [identity] using entry
  rw [transposeDet,
    NormalForms.Matrix.Smith.Internal.det_submatrix_mul_sum_embeddings]
  apply Finset.dvd_sum
  intro rows _
  apply dvd_mul_of_dvd_left
  have minorDivides := suffixDet_dvd_rowMinor result.H
    fullRank.columns_le_rows referenceShape.1
      (fun column _ => referenceShape.2 column) rows
  have transposeMinor :
      (result.H.transpose.submatrix identity rows).det =
        (result.H.submatrix rows id).det := by
    rw [← _root_.Matrix.det_transpose]
    congr 1
  simpa [transposeMinor] using minorDivides

/-- The initial live modulus is divisible by the canonical HNF determinant. -/
theorem reference_initialDet_dvd_modulus {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) :
    let result := hermiteNormalFormFin A
    (suffixSquare result.H fullRank.columns_le_rows 0).det ∣ witness.modulus := by
  let result := hermiteNormalFormFin A
  exact dvd_trans
    (reference_initialDet_dvd_selectedMinor A fullRank)
    (Int.natAbs_dvd_natAbs.mp witness.selectedMinor_dvd)

end NormalForms.Research.ModularHNF
