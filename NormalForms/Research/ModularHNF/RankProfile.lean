/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Correctness
import all NormalForms.Matrix.Hermite.Uniqueness

/-!
# Fraction-free rank profiles and the general modular wrapper

A profile consists only of integer data: a nonsingular pivot minor and scaled
column identities.  The identities certify both spanning and the lexicographic
support condition without rational division.  Running the full-column modular
kernel on the selected pivot columns then lifts to a strong HNF result for the
entire rectangular or rank-deficient matrix.
-/

public section

namespace NormalForms.Research.ModularHNF

open scoped BigOperators Matrix
open NormalForms.Matrix.Certificates

public structure FractionFreeRankProfile {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) where
  rank : Nat
  rank_le_rows : rank ≤ m
  rank_le_columns : rank ≤ n
  pivotColumns : Fin rank ↪ Fin n
  pivotColumns_strictMono : StrictMono pivotColumns
  pivotRows : Fin rank ↪ Fin m
  minor_ne_zero : (A.submatrix pivotRows pivotColumns).det ≠ 0
  coefficients : Fin n → Fin rank → Int
  column_identity : ∀ row column,
    (A.submatrix pivotRows pivotColumns).det * A row column =
      ∑ i : Fin rank, coefficients column i * A row (pivotColumns i)
  coefficients_zero_of_before : ∀ column i,
    column < pivotColumns i → coefficients column i = 0

namespace FractionFreeRankProfile

def projected {m n : Nat} {A : _root_.Matrix (Fin m) (Fin n) Int}
    (profile : FractionFreeRankProfile A) :
    _root_.Matrix (Fin m) (Fin profile.rank) Int :=
  A.submatrix id profile.pivotColumns

def fullRank {m n : Nat} {A : _root_.Matrix (Fin m) (Fin n) Int}
    (profile : FractionFreeRankProfile A) :
    FullColumnRankWitness profile.projected :=
  { rows := profile.pivotRows
    det_ne_zero := by
      simpa [projected, selectedSquareMinor] using profile.minor_ne_zero }

def determinantModulus {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (profile : FractionFreeRankProfile A) :
    DeterminantModulusWitness profile.projected profile.fullRank :=
  { modulus := ((A.submatrix profile.pivotRows profile.pivotColumns).det.natAbs : Int)
    positive := by
      exact_mod_cast Int.natAbs_pos.mpr profile.minor_ne_zero
    selectedMinor_dvd := by
      simp [fullRank, projected, selectedSquareMinor] }

theorem column_identity_mul {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (profile : FractionFreeRankProfile A)
    (U : _root_.Matrix (Fin m) (Fin m) Int) (row : Fin m)
    (column : Fin n) :
    (A.submatrix profile.pivotRows profile.pivotColumns).det *
        (U * A) row column =
      ∑ i : Fin profile.rank,
        profile.coefficients column i *
          (U * A) row (profile.pivotColumns i) := by
  simp only [_root_.Matrix.mul_apply]
  calc
    (A.submatrix profile.pivotRows profile.pivotColumns).det *
        ∑ middle, U row middle * A middle column =
      ∑ middle, U row middle *
        ((A.submatrix profile.pivotRows profile.pivotColumns).det *
          A middle column) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro middle _
        ring
    _ = ∑ middle, U row middle *
        (∑ i : Fin profile.rank,
          profile.coefficients column i *
            A middle (profile.pivotColumns i)) := by
      apply Finset.sum_congr rfl
      intro middle _
      rw [profile.column_identity]
    _ = ∑ middle, ∑ i : Fin profile.rank,
        U row middle * (profile.coefficients column i *
          A middle (profile.pivotColumns i)) := by
      apply Finset.sum_congr rfl
      intro middle _
      rw [Finset.mul_sum]
    _ = ∑ i : Fin profile.rank, ∑ middle,
        U row middle * (profile.coefficients column i *
          A middle (profile.pivotColumns i)) := Finset.sum_comm
    _ = ∑ i : Fin profile.rank, profile.coefficients column i *
        ∑ middle, U row middle * A middle (profile.pivotColumns i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro middle _
      ring

end FractionFreeRankProfile

open NormalForms.Matrix.Hermite

theorem isHermite_of_all_zero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (zero : ∀ row column, A row column = 0) :
    IsHermiteNormalFormFin A := by
  induction n generalizing m with
  | zero => exact .emptyCols A
  | succ n ih =>
      cases m with
      | zero => exact .emptyRows A
      | succ m =>
          apply IsHermiteNormalFormFin.zeroCol
          · exact fun row => zero row 0
          · apply ih (tailCols A)
            intro row column
            exact zero row column.succ

theorem isHermite_of_pivotProfile :
    ∀ {m n r : Nat}
      (A : _root_.Matrix (Fin m) (Fin n) Int)
      (rank_le_rows : r ≤ m)
      (pivots : Fin r ↪ Fin n),
      StrictMono pivots →
      (∀ row, r ≤ row.val → ∀ column, A row column = 0) →
      (∀ i : Fin r, 0 < A (Fin.castLE rank_le_rows i) (pivots i)) →
      (∀ i : Fin r, A (Fin.castLE rank_le_rows i) (pivots i) =
        normalize (A (Fin.castLE rank_le_rows i) (pivots i))) →
      (∀ i : Fin r, ∀ column, column < pivots i →
        A (Fin.castLE rank_le_rows i) column = 0) →
      (∀ i : Fin r, ∀ row, Fin.castLE rank_le_rows i < row →
        A row (pivots i) = 0) →
      (∀ i : Fin r, ∀ row, row < Fin.castLE rank_le_rows i →
        A row (pivots i) =
          A row (pivots i) % A (Fin.castLE rank_le_rows i) (pivots i)) →
      IsHermiteNormalFormFin A := by
  intro m n
  induction n generalizing m with
  | zero =>
      intro r A rank_le_rows pivots strict zeroTail positive normalized
        prefixZero belowZero reduced
      exact .emptyCols A
  | succ n ih =>
      intro r A rank_le_rows pivots strict zeroTail positive normalized
        prefixZero belowZero reduced
      cases m with
      | zero => exact .emptyRows A
      | succ m =>
          cases r with
          | zero =>
              apply isHermite_of_all_zero A
              intro row column
              exact zeroTail row (by omega) column
          | succ r =>
              by_cases firstZero : pivots (0 : Fin (r + 1)) = 0
              · have lowerRankLe : r ≤ m := by omega
                have laterPositive : ∀ i : Fin r,
                    0 < (pivots i.succ).val := by
                  intro i
                  have order := strict (show (0 : Fin (r + 1)) < i.succ by simp)
                  rw [firstZero] at order
                  exact order
                let lowerPivots : Fin r ↪ Fin n :=
                  { toFun := fun i =>
                      ⟨(pivots i.succ).val - 1, by
                        have bound := (pivots i.succ).isLt
                        have positiveValue := laterPositive i
                        omega⟩
                    inj' := by
                      intro i j equal
                      apply Fin.succ_injective
                      apply pivots.injective
                      apply Fin.ext
                      have valueEq := congrArg Fin.val equal
                      have leftPositive := laterPositive i
                      have rightPositive := laterPositive j
                      dsimp at valueEq
                      omega }
                have lowerPivotsSucc : ∀ i : Fin r,
                    pivots i.succ = (lowerPivots i).succ := by
                  intro i
                  apply Fin.ext
                  have positiveValue := laterPositive i
                  simp only [Fin.val_succ]
                  dsimp [lowerPivots]
                  omega
                have lowerStrict : StrictMono lowerPivots := by
                  intro i j before
                  have originalBefore := strict
                    (Fin.succ_lt_succ_iff.mpr before)
                  change (pivots i.succ).val - 1 <
                    (pivots j.succ).val - 1
                  have leftPositive := laterPositive i
                  omega
                have lowerHermite :
                    IsHermiteNormalFormFin (lowerRight A) := by
                  apply ih (lowerRight A) lowerRankLe lowerPivots lowerStrict
                  · intro row rowAfter column
                    exact zeroTail row.succ (by
                      change r + 1 ≤ row.val + 1
                      omega) column.succ
                  · intro i
                    have rowEq :
                        Fin.castLE rank_le_rows i.succ =
                          (Fin.castLE lowerRankLe i).succ := by
                      apply Fin.ext
                      rfl
                    change 0 < A (Fin.castLE lowerRankLe i).succ
                      (lowerPivots i).succ
                    rw [← rowEq, ← lowerPivotsSucc i]
                    exact positive i.succ
                  · intro i
                    have rowEq :
                        Fin.castLE rank_le_rows i.succ =
                          (Fin.castLE lowerRankLe i).succ := by
                      apply Fin.ext
                      rfl
                    change A (Fin.castLE lowerRankLe i).succ
                        (lowerPivots i).succ =
                      normalize (A (Fin.castLE lowerRankLe i).succ
                        (lowerPivots i).succ)
                    rw [← rowEq, ← lowerPivotsSucc i]
                    exact normalized i.succ
                  · intro i column columnBefore
                    have rowEq :
                        Fin.castLE rank_le_rows i.succ =
                          (Fin.castLE lowerRankLe i).succ := by
                      apply Fin.ext
                      rfl
                    have originalBefore : column.succ < pivots i.succ := by
                      rw [lowerPivotsSucc i]
                      exact Fin.succ_lt_succ_iff.mpr columnBefore
                    change A (Fin.castLE lowerRankLe i).succ column.succ = 0
                    rw [← rowEq]
                    exact prefixZero i.succ column.succ originalBefore
                  · intro i row pivotBeforeRow
                    have pivotRowEq :
                        Fin.castLE rank_le_rows i.succ =
                          (Fin.castLE lowerRankLe i).succ := by
                      apply Fin.ext
                      rfl
                    have originalBefore :
                        Fin.castLE rank_le_rows i.succ < row.succ := by
                      rw [pivotRowEq]
                      exact Fin.succ_lt_succ_iff.mpr pivotBeforeRow
                    change A row.succ (lowerPivots i).succ = 0
                    rw [← lowerPivotsSucc i]
                    exact belowZero i.succ row.succ originalBefore
                  · intro i row rowBeforePivot
                    have pivotRowEq :
                        Fin.castLE rank_le_rows i.succ =
                          (Fin.castLE lowerRankLe i).succ := by
                      apply Fin.ext
                      rfl
                    have originalBefore :
                        row.succ < Fin.castLE rank_le_rows i.succ := by
                      rw [pivotRowEq]
                      exact Fin.succ_lt_succ_iff.mpr rowBeforePivot
                    change A row.succ (lowerPivots i).succ =
                      A row.succ (lowerPivots i).succ %
                        A (Fin.castLE lowerRankLe i).succ
                          (lowerPivots i).succ
                    rw [← lowerPivotsSucc i, ← pivotRowEq]
                    exact reduced i.succ row.succ originalBefore
                refine IsHermiteNormalFormFin.pivot A ?_ ?_ ?_
                  lowerHermite ?_
                · have topPositive := positive (0 : Fin (r + 1))
                  have topRow : Fin.castLE rank_le_rows (0 : Fin (r + 1)) =
                      (0 : Fin (m + 1)) := by
                    apply Fin.ext
                    rfl
                  simpa [firstZero, topRow] using ne_of_gt topPositive
                · have topNormalized := normalized (0 : Fin (r + 1))
                  have topRow : Fin.castLE rank_le_rows (0 : Fin (r + 1)) =
                      (0 : Fin (m + 1)) := by
                    apply Fin.ext
                    rfl
                  simpa [firstZero, topRow] using topNormalized
                · intro row
                  have topRow : Fin.castLE rank_le_rows (0 : Fin (r + 1)) =
                      (0 : Fin (m + 1)) := by
                    apply Fin.ext
                    rfl
                  simpa [firstZero] using
                    (belowZero 0 row.succ (by simp [topRow]))
                · intro row
                  by_cases rowInRank : row.val < r
                  · let i : Fin r := ⟨row.val, rowInRank⟩
                    have pivotNonzero :
                        (fun column : Fin n => A row.succ column.succ)
                          (lowerPivots i) ≠ 0 := by
                      have rowEq :
                          Fin.castLE rank_le_rows i.succ = row.succ := by
                        apply Fin.ext
                        rfl
                      change A row.succ (lowerPivots i).succ ≠ 0
                      rw [← lowerPivotsSucc i, ← rowEq]
                      exact ne_of_gt (positive i.succ)
                    have rowPrefix : ∀ column, column < lowerPivots i →
                        A row.succ column.succ = 0 := by
                      intro column before
                      have rowEq :
                          Fin.castLE rank_le_rows i.succ = row.succ := by
                        apply Fin.ext
                        rfl
                      have originalBefore : column.succ < pivots i.succ := by
                        rw [lowerPivotsSucc i]
                        exact Fin.succ_lt_succ_iff.mpr before
                      rw [← rowEq]
                      exact prefixZero i.succ column.succ originalBefore
                    have firstNonzero :=
                      firstNonzero?_eq_some_of_prefix_zero
                        (fun column : Fin n => A row.succ column.succ)
                        (lowerPivots i) pivotNonzero rowPrefix
                    rw [firstNonzero]
                    have pivotRowEq :
                        Fin.castLE rank_le_rows i.succ = row.succ := by
                      apply Fin.ext
                      rfl
                    have topBefore :
                        (0 : Fin (m + 1)) <
                          Fin.castLE rank_le_rows i.succ := by
                      rw [pivotRowEq]
                      simp
                    change A 0 (lowerPivots i).succ =
                      A 0 (lowerPivots i).succ % A row.succ (lowerPivots i).succ
                    rw [← lowerPivotsSucc i, ← pivotRowEq]
                    exact reduced i.succ 0 topBefore
                  · have rowAfter : r + 1 ≤ row.succ.val := by
                      change r + 1 ≤ row.val + 1
                      omega
                    have rowZero :
                        (fun column : Fin n => A row.succ column.succ) =
                          fun _ => 0 := by
                      funext column
                      exact zeroTail row.succ rowAfter column.succ
                    rw [rowZero, firstNonzero?_zero]
                    trivial
              · have firstPositive : 0 < (pivots (0 : Fin (r + 1))).val :=
                    Nat.pos_of_ne_zero (by
                      intro valueZero
                      apply firstZero
                      apply Fin.ext
                      exact valueZero)
                have allPositive : ∀ i : Fin (r + 1),
                    0 < (pivots i).val := by
                  intro i
                  have firstLe :
                      pivots (0 : Fin (r + 1)) ≤ pivots i :=
                    strict.monotone (Fin.zero_le i)
                  exact lt_of_lt_of_le firstPositive firstLe
                let tailPivots : Fin (r + 1) ↪ Fin n :=
                  { toFun := fun i =>
                      ⟨(pivots i).val - 1, by
                        have bound := (pivots i).isLt
                        have positiveValue := allPositive i
                        omega⟩
                    inj' := by
                      intro i j equal
                      apply pivots.injective
                      apply Fin.ext
                      have valueEq := congrArg Fin.val equal
                      have leftPositive := allPositive i
                      have rightPositive := allPositive j
                      dsimp at valueEq
                      omega }
                have tailPivotsSucc : ∀ i : Fin (r + 1),
                    pivots i = (tailPivots i).succ := by
                  intro i
                  apply Fin.ext
                  have positiveValue := allPositive i
                  simp only [Fin.val_succ]
                  dsimp [tailPivots]
                  omega
                have tailStrict : StrictMono tailPivots := by
                  intro i j before
                  have originalBefore := strict before
                  change (pivots i).val - 1 < (pivots j).val - 1
                  have leftPositive := allPositive i
                  omega
                have firstColumnZero : ∀ row : Fin (m + 1), A row 0 = 0 := by
                  intro row
                  by_cases rowInRank : row.val < r + 1
                  · let i : Fin (r + 1) := ⟨row.val, rowInRank⟩
                    have rowEq : Fin.castLE rank_le_rows i = row := by
                      apply Fin.ext
                      rfl
                    rw [← rowEq]
                    exact prefixZero i 0 (by
                      change 0 < (pivots i).val
                      exact allPositive i)
                  · exact zeroTail row (Nat.le_of_not_gt rowInRank) 0
                apply IsHermiteNormalFormFin.zeroCol A firstColumnZero
                apply ih (tailCols A) rank_le_rows tailPivots tailStrict
                · intro row rowAfter column
                  exact zeroTail row rowAfter column.succ
                · intro i
                  change 0 < A (Fin.castLE rank_le_rows i)
                    (tailPivots i).succ
                  rw [← tailPivotsSucc i]
                  exact positive i
                · intro i
                  change A (Fin.castLE rank_le_rows i) (tailPivots i).succ =
                    normalize
                      (A (Fin.castLE rank_le_rows i) (tailPivots i).succ)
                  rw [← tailPivotsSucc i]
                  exact normalized i
                · intro i column columnBefore
                  change A (Fin.castLE rank_le_rows i) column.succ = 0
                  apply prefixZero i column.succ
                  rw [tailPivotsSucc i]
                  exact Fin.succ_lt_succ_iff.mpr columnBefore
                · intro i row pivotBeforeRow
                  change A row (tailPivots i).succ = 0
                  rw [← tailPivotsSucc i]
                  exact belowZero i row pivotBeforeRow
                · intro i row rowBeforePivot
                  change A row (tailPivots i).succ =
                    A row (tailPivots i).succ %
                      A (Fin.castLE rank_le_rows i) (tailPivots i).succ
                  rw [← tailPivotsSucc i]
                  exact reduced i row rowBeforePivot

namespace FractionFreeRankProfile

def projectedResult {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (profile : FractionFreeRankProfile A) : HNFResultFin profile.projected :=
  modularHNFFullRank profile.projected profile.fullRank
    profile.determinantModulus

theorem projectedResult_shape {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (profile : FractionFreeRankProfile A) :
    PrefixRowsZero profile.projectedResult.H profile.rank ∧
      ∀ column,
        ColumnHermiteShape profile.projectedResult.H
          (Fin.castLE profile.rank_le_rows column) column := by
  let result := profile.projectedResult
  have rankEq :
      (result.H.map (Int.castRingHom Rat)).rank = profile.rank := by
    have resultEq : result.H = (hermiteNormalFormFin profile.projected).H := by
      simpa [result, projectedResult] using
        (modularHNFFullRank_eq_reference profile.projected profile.fullRank
          profile.determinantModulus)
    rw [resultEq]
    exact reference_rank_eq_width profile.projected profile.fullRank
  exact hnf_fullColumnShape result.H profile.rank_le_rows result.isHermite
    (cols_linearIndependent_of_rank_eq_width _ rankEq)

theorem transformed_selectedColumn {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (profile : FractionFreeRankProfile A)
    (row : Fin m) (i : Fin profile.rank) :
    (profile.projectedResult.U * A) row (profile.pivotColumns i) =
      profile.projectedResult.H row i := by
  have entry := congrFun
    (congrFun profile.projectedResult.equation row) i
  simpa [projected, _root_.Matrix.mul_apply] using entry

theorem transformed_zeroTail {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (profile : FractionFreeRankProfile A)
    (row : Fin m) (rowAfter : profile.rank ≤ row.val)
    (column : Fin n) :
    (profile.projectedResult.U * A) row column = 0 := by
  have identity := profile.column_identity_mul profile.projectedResult.U
    row column
  have rightZero :
      (∑ i : Fin profile.rank, profile.coefficients column i *
        (profile.projectedResult.U * A) row (profile.pivotColumns i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [profile.transformed_selectedColumn]
    rw [(profile.projectedResult_shape.1 row rowAfter i i.isLt)]
    simp
  rw [rightZero] at identity
  exact (mul_eq_zero.mp identity).resolve_left profile.minor_ne_zero

theorem transformed_prefixZero {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (profile : FractionFreeRankProfile A)
    (i : Fin profile.rank) (column : Fin n)
    (before : column < profile.pivotColumns i) :
    (profile.projectedResult.U * A)
        (Fin.castLE profile.rank_le_rows i) column = 0 := by
  have identity := profile.column_identity_mul profile.projectedResult.U
    (Fin.castLE profile.rank_le_rows i) column
  have rightZero :
      (∑ current : Fin profile.rank,
        profile.coefficients column current *
          (profile.projectedResult.U * A)
            (Fin.castLE profile.rank_le_rows i)
            (profile.pivotColumns current)) = 0 := by
    apply Finset.sum_eq_zero
    intro current _
    by_cases currentBefore : current < i
    · rw [profile.transformed_selectedColumn]
      have pivotBeforeRow :
          Fin.castLE profile.rank_le_rows current <
            Fin.castLE profile.rank_le_rows i := by
        change current.val < i.val
        exact currentBefore
      rw [(profile.projectedResult_shape.2 current).below_zero
        (Fin.castLE profile.rank_le_rows i) pivotBeforeRow]
      simp
    · have iLeCurrent : i ≤ current := not_lt.mp currentBefore
      have pivotLe : profile.pivotColumns i ≤
          profile.pivotColumns current :=
        profile.pivotColumns_strictMono.monotone iLeCurrent
      rw [profile.coefficients_zero_of_before column current
        (lt_of_lt_of_le before pivotLe)]
      simp
  rw [rightZero] at identity
  exact (mul_eq_zero.mp identity).resolve_left profile.minor_ne_zero

theorem transformed_isHermite {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (profile : FractionFreeRankProfile A) :
    IsHermiteNormalFormFin (profile.projectedResult.U * A) := by
  let transformed := profile.projectedResult.U * A
  have projectedShape := profile.projectedResult_shape
  apply isHermite_of_pivotProfile transformed profile.rank_le_rows
    profile.pivotColumns profile.pivotColumns_strictMono
  · exact profile.transformed_zeroTail
  · intro i
    change 0 < (profile.projectedResult.U * A)
      (Fin.castLE profile.rank_le_rows i) (profile.pivotColumns i)
    rw [profile.transformed_selectedColumn]
    exact (projectedShape.2 i).pivot_positive
  · intro i
    change (profile.projectedResult.U * A)
        (Fin.castLE profile.rank_le_rows i) (profile.pivotColumns i) =
      normalize ((profile.projectedResult.U * A)
        (Fin.castLE profile.rank_le_rows i) (profile.pivotColumns i))
    rw [profile.transformed_selectedColumn]
    exact (projectedShape.2 i).pivot_normalized
  · exact profile.transformed_prefixZero
  · intro i row pivotBeforeRow
    change (profile.projectedResult.U * A) row
      (profile.pivotColumns i) = 0
    rw [profile.transformed_selectedColumn]
    exact (projectedShape.2 i).below_zero row pivotBeforeRow
  · intro i row rowBeforePivot
    change (profile.projectedResult.U * A) row (profile.pivotColumns i) =
      (profile.projectedResult.U * A) row (profile.pivotColumns i) %
        (profile.projectedResult.U * A)
          (Fin.castLE profile.rank_le_rows i) (profile.pivotColumns i)
    rw [profile.transformed_selectedColumn,
      profile.transformed_selectedColumn]
    exact (projectedShape.2 i).above_reduced row rowBeforePivot

end FractionFreeRankProfile

/-- General rectangular modular HNF from a checked fraction-free rank profile. -/
@[expose] public def integerHermiteNormalFormModularWithProfile {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (profile : FractionFreeRankProfile A) : HNFResultFin A :=
  { U := profile.projectedResult.U
    U_cert := profile.projectedResult.U_cert
    H := profile.projectedResult.U * A
    equation := rfl
    isHermite := profile.transformed_isHermite }

public theorem integerHermiteNormalFormModularWithProfile_eq_reference {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (profile : FractionFreeRankProfile A) :
    (integerHermiteNormalFormModularWithProfile A profile).H =
      (hermiteNormalFormFin A).H := by
  let result := integerHermiteNormalFormModularWithProfile A profile
  let reference := hermiteNormalFormFin A
  let change := reference.U * result.U_cert.inverse
  have changeCert : MatrixInverseCertificate change :=
    reference.U_cert.mul result.U_cert.symm
  have resultRecover : result.U_cert.inverse * result.H = A := by
    rw [← result.equation, ← _root_.Matrix.mul_assoc,
      result.U_cert.left_inv]
    simp
  apply isHermiteNormalFormFin_unique_of_left_equiv
    result.isHermite reference.isHermite changeCert.unimodular
  calc
    change * result.H =
        reference.U * (result.U_cert.inverse * result.H) := by
      rw [_root_.Matrix.mul_assoc]
    _ = reference.U * A := by
      rw [resultRecover]
    _ = reference.H := reference.equation

end NormalForms.Research.ModularHNF
