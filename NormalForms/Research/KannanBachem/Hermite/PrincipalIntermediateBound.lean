/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalMinors
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal
import all NormalForms.Research.KannanBachem.Hermite.PrincipalCorrectness
import all NormalForms.Research.KannanBachem.Hermite.PrincipalMinors

/-! Stagewise polynomial envelopes for the principal-minor HNF kernel. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix
open NormalForms.Matrix.Hermite

namespace Principal

/-- One fixed determinant envelope covers every selected minor in a stage. -/
@[expose] public def stageMinorHeightBound
    (target inputHeight : Nat) : Nat :=
  (target + 1).factorial * (max 1 inputHeight) ^ (target + 1)

/-- Uniform operand envelope for all Bézout pairs in one stage. -/
@[expose] public def stagePairOperandHeightBound
    (target inputHeight : Nat) : Nat :=
  max inputHeight (stageMinorHeightBound target inputHeight)

/-- Uniform envelope for the modified Bézout coefficients in one stage. -/
@[expose] public def stagePairCoefficientHeightBound
    (target inputHeight : Nat) : Nat :=
  (stagePairOperandHeightBound target inputHeight + 1) ^ 2

/-- Uniform envelope for a row freshly produced by a Bézout pair. -/
@[expose] public def stagePairRowHeightBound
    (target inputHeight : Nat) : Nat :=
  2 * stagePairCoefficientHeightBound target inputHeight *
    stagePairOperandHeightBound target inputHeight

/-- Coarse matrix-height envelope after `processed` pair/reduction rounds. -/
@[expose] public def stageIntermediateHeightBound
    (processed target inputHeight : Nat) : Nat :=
  let base := max inputHeight
    (max (stageMinorHeightBound target inputHeight)
      (stagePairRowHeightBound target inputHeight))
  (base + 1) * (stagePairRowHeightBound target inputHeight + 2) ^ processed

/-- Height envelope after normalization and the final off-diagonal reduction. -/
@[expose] public def completedStageHeightBound
    (target inputHeight : Nat) : Nat :=
  (stageIntermediateHeightBound target target inputHeight + 1) *
    (stageMinorHeightBound target inputHeight + 1)

theorem selectedMinor_le_stageMinorHeightBound
    {processed target inputHeight : Nat} (hprocessed : processed ≤ target) :
    (processed + 1).factorial * inputHeight ^ (processed + 1) ≤
      stageMinorHeightBound target inputHeight := by
  have orderLe : processed + 1 ≤ target + 1 := by omega
  have factorialLe := Nat.factorial_le orderLe
  have baseLe : inputHeight ≤ max 1 inputHeight := le_max_right _ _
  have exponentBaseLe : inputHeight ^ (processed + 1) ≤
      (max 1 inputHeight) ^ (processed + 1) :=
    Nat.pow_le_pow_left baseLe _
  have exponentLe : (max 1 inputHeight) ^ (processed + 1) ≤
      (max 1 inputHeight) ^ (target + 1) :=
    Nat.pow_le_pow_right (by omega) orderLe
  unfold stageMinorHeightBound
  exact Nat.mul_le_mul factorialLe (exponentBaseLe.trans exponentLe)

theorem eliminateStageLoop_next_pair_operandHeight_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (processed : Nat) (hprocessed : processed < target.val)
    (state : State A)
    (leading : PrefixHermite target.val state.transform.B)
    (diagonal_ne : ∀ row, row.val < target.val →
      state.transform.B row row ≠ 0) :
    let previous :=
      eliminateStageLoop target processed hprocessed.le state
    let pivot : Fin n := ⟨processed, hprocessed.trans target.isLt⟩
    max (previous.transform.B pivot pivot).natAbs
        (previous.transform.B target pivot).natAbs ≤
      stagePairOperandHeightBound target.val
        (matrixHeight state.transform.B) := by
  let previous := eliminateStageLoop target processed hprocessed.le state
  let pivot : Fin n := ⟨processed, hprocessed.trans target.isLt⟩
  have pivot_ne_target : pivot ≠ target := by
    intro equality
    have values := congrArg Fin.val equality
    dsimp [pivot] at values
    omega
  have pivotUnchanged : previous.transform.B pivot pivot =
      state.transform.B pivot pivot :=
    eliminateStageLoop_row_unchanged target processed hprocessed.le state
      pivot pivot (by simp [pivot]) pivot_ne_target
  have pivotBound : (previous.transform.B pivot pivot).natAbs ≤
      matrixHeight state.transform.B := by
    rw [pivotUnchanged]
    exact entry_natAbs_le_matrixHeight state.transform.B pivot pivot
  have targetMinor : (previous.transform.B target pivot).natAbs ≤
      (processed + 1).factorial *
        matrixHeight state.transform.B ^ (processed + 1) :=
    eliminateStageLoop_target_entry_natAbs_le target processed hprocessed.le
      state leading diagonal_ne pivot (by simp [pivot])
  have targetBound : (previous.transform.B target pivot).natAbs ≤
      stageMinorHeightBound target.val (matrixHeight state.transform.B) :=
    targetMinor.trans
      (selectedMinor_le_stageMinorHeightBound hprocessed.le)
  exact max_le
    (pivotBound.trans (le_max_left _ _))
    (targetBound.trans (le_max_right _ _))

theorem eliminateStageLoop_next_pair_coefficientHeight_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (processed : Nat) (hprocessed : processed < target.val)
    (state : State A)
    (leading : PrefixHermite target.val state.transform.B)
    (diagonal_ne : ∀ row, row.val < target.val →
      state.transform.B row row ≠ 0) :
    let previous :=
      eliminateStageLoop target processed hprocessed.le state
    let pivot : Fin n := ⟨processed, hprocessed.trans target.isLt⟩
    let data := boundedIntXGCD
      (previous.transform.B pivot pivot)
      (previous.transform.B target pivot)
    max data.leftCoeff.natAbs data.rightCoeff.natAbs ≤
      stagePairCoefficientHeightBound target.val
        (matrixHeight state.transform.B) := by
  let previous := eliminateStageLoop target processed hprocessed.le state
  let pivot : Fin n := ⟨processed, hprocessed.trans target.isLt⟩
  let left := previous.transform.B pivot pivot
  let right := previous.transform.B target pivot
  let data := boundedIntXGCD left right
  have operands := eliminateStageLoop_next_pair_operandHeight_le target
    processed hprocessed state leading diagonal_ne
  have coefficients := boundedIntXGCD_coefficient_natAbs_le left right
  change max data.leftCoeff.natAbs data.rightCoeff.natAbs ≤ _
  have exactBound : max data.leftCoeff.natAbs data.rightCoeff.natAbs ≤
      (max left.natAbs right.natAbs + 1) ^ 2 :=
    max_le coefficients.1 coefficients.2
  exact exactBound.trans <| by
    unfold stagePairCoefficientHeightBound
    exact Nat.pow_le_pow_left (Nat.add_le_add_right operands 1) 2

theorem eliminateStageLoop_next_pair_pivot_entry_natAbs_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (processed : Nat) (hprocessed : processed < target.val)
    (state : State A)
    (leading : PrefixHermite target.val state.transform.B)
    (diagonal_ne : ∀ row, row.val < target.val →
      state.transform.B row row ≠ 0)
    (column : Fin n) :
    let previous := eliminateStageLoop target processed hprocessed.le state
    let pivot : Fin n := ⟨processed, hprocessed.trans target.isLt⟩
    let eliminated := previous.gcdEliminate pivot target (by
      change processed < target.val
      exact hprocessed)
    (eliminated.transform.B pivot column).natAbs ≤
      stagePairRowHeightBound target.val
        (matrixHeight state.transform.B) := by
  let previous := eliminateStageLoop target processed hprocessed.le state
  let pivot : Fin n := ⟨processed, hprocessed.trans target.isLt⟩
  have hpivot : pivot < target := by
    change processed < target.val
    exact hprocessed
  let eliminated := previous.gcdEliminate pivot target hpivot
  let left := previous.transform.B pivot pivot
  let right := previous.transform.B target pivot
  let operandBound := stagePairOperandHeightBound target.val
    (matrixHeight state.transform.B)
  let coefficientBound := stagePairCoefficientHeightBound target.val
    (matrixHeight state.transform.B)
  change (eliminated.transform.B pivot column).natAbs ≤
    stagePairRowHeightBound target.val (matrixHeight state.transform.B)
  have pivot_ne_target : pivot ≠ target := hpivot.ne
  have pivotRowUnchanged : previous.transform.B pivot column =
      state.transform.B pivot column :=
    eliminateStageLoop_row_unchanged target processed hprocessed.le state
      pivot column (by simp [pivot]) pivot_ne_target
  have pivotEntryBound : (previous.transform.B pivot column).natAbs ≤
      operandBound := by
    rw [pivotRowUnchanged]
    exact (entry_natAbs_le_matrixHeight state.transform.B pivot column).trans
      (le_max_left _ _)
  have previousInvariant : EliminationInvariant target processed previous :=
    eliminateStageLoop_invariant target processed hprocessed.le state leading
  have targetEntryBound : (previous.transform.B target column).natAbs ≤
      operandBound := by
    by_cases hcolumn : processed ≤ column.val
    · have minor := eliminateStageLoop_target_entry_natAbs_le target
        processed hprocessed.le state leading diagonal_ne column hcolumn
      exact minor.trans <| (selectedMinor_le_stageMinorHeightBound
        hprocessed.le).trans (le_max_right _ _)
    · rw [previousInvariant.targetZero column (by omega), Int.natAbs_zero]
      exact Nat.zero_le _
  have leftNe : left ≠ 0 := by
    have unchanged : left = state.transform.B pivot pivot :=
      eliminateStageLoop_row_unchanged target processed hprocessed.le state
        pivot pivot (by simp [pivot]) pivot_ne_target
    rw [unchanged]
    exact diagonal_ne pivot (by simp [pivot]; omega)
  have operands := eliminateStageLoop_next_pair_operandHeight_le target
    processed hprocessed state leading diagonal_ne
  have matrixCoefficientBound : ∀ row col : Fin 2,
      (boundedBezoutReductionMatrix left right row col).natAbs ≤
        coefficientBound := by
    intro row col
    have exactBound := boundedBezoutReductionMatrix_entry_natAbs_le left right
      (Or.inl leftNe) row col
    exact exactBound.trans <| by
      unfold boundedIntXGCDCoefficientHeight coefficientBound
      unfold stagePairCoefficientHeightBound
      exact Nat.pow_le_pow_left (Nat.add_le_add_right operands 1) 2
  rw [State.gcdEliminate_pivot_apply]
  calc
    (boundedBezoutReductionMatrix left right 0 0 *
          previous.transform.B pivot column +
        boundedBezoutReductionMatrix left right 0 1 *
          previous.transform.B target column).natAbs ≤
        (boundedBezoutReductionMatrix left right 0 0 *
          previous.transform.B pivot column).natAbs +
        (boundedBezoutReductionMatrix left right 0 1 *
          previous.transform.B target column).natAbs :=
      Int.natAbs_add_le _ _
    _ = (boundedBezoutReductionMatrix left right 0 0).natAbs *
          (previous.transform.B pivot column).natAbs +
        (boundedBezoutReductionMatrix left right 0 1).natAbs *
          (previous.transform.B target column).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
    _ ≤ coefficientBound * operandBound +
          coefficientBound * operandBound :=
      Nat.add_le_add
        (Nat.mul_le_mul (matrixCoefficientBound 0 0) pivotEntryBound)
        (Nat.mul_le_mul (matrixCoefficientBound 0 1) targetEntryBound)
    _ = stagePairRowHeightBound target.val
          (matrixHeight state.transform.B) := by
      unfold stagePairRowHeightBound coefficientBound operandBound
      ring

theorem intQuotient_natAbs_le_succ (numerator divisor : Int) :
    (numerator / divisor).natAbs ≤ numerator.natAbs + 1 := by
  rw [Int.natAbs_ediv]
  have divisionLe : numerator.natAbs / divisor.natAbs ≤
      numerator.natAbs := Nat.div_le_self _ _
  split <;> omega

theorem reduceAboveLoop_height_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → (hk : k ≤ destination.val) → (state : State A) →
      (matrixBound destinationBound : Nat) →
      matrixHeight state.transform.B ≤ matrixBound →
      (∀ column, (state.transform.B destination column).natAbs ≤
        destinationBound) →
      matrixHeight (reduceAboveLoop destination k hk state).transform.B ≤
        (matrixBound + 1) * (destinationBound + 1)
  | 0, _, state, matrixBound, destinationBound, heightBound, _ => by
      exact heightBound.trans <| by
        nlinarith [Nat.zero_le destinationBound]
  | k + 1, hk, state, matrixBound, destinationBound, heightBound,
      destinationRowBound => by
      let previous := reduceAboveLoop destination k (by omega) state
      let source : Fin n := ⟨k, by omega⟩
      have hsource : source < destination := by
        change k < destination.val
        omega
      have previousHeight := reduceAboveLoop_height_le destination k (by omega)
        state matrixBound destinationBound heightBound destinationRowBound
      have sourceUnchanged : ∀ column,
          previous.transform.B source column =
            state.transform.B source column := by
        intro column
        exact reduceAboveLoop_row_unchanged destination k (by omega) state
          source column (by simp [source])
      have destinationUnchanged : ∀ column,
          previous.transform.B destination column =
            state.transform.B destination column := by
        intro column
        exact reduceAboveLoop_row_unchanged destination k (by omega) state
          destination column (by omega)
      change matrixHeight
        (previous.reduceAbove source destination hsource).transform.B ≤ _
      apply matrixHeight_le
      intro row column
      by_cases equality : row = source
      · subst row
        rw [State.reduceAbove_source_apply]
        have sourceEntry : (previous.transform.B source column).natAbs ≤
            matrixBound := by
          rw [sourceUnchanged]
          exact (entry_natAbs_le_matrixHeight state.transform.B source column).trans
            heightBound
        have numerator :
            (previous.transform.B source destination).natAbs ≤ matrixBound := by
          rw [sourceUnchanged]
          exact (entry_natAbs_le_matrixHeight state.transform.B
            source destination).trans heightBound
        have quotient :
            (ComputableEuclideanOps.quot
              (previous.transform.B source destination)
              (previous.transform.B destination destination)).natAbs ≤
                matrixBound + 1 := by
          rw [ComputableEuclideanOps.quot_eq]
          exact (intQuotient_natAbs_le_succ _ _).trans
            (Nat.add_le_add_right numerator 1)
        have destinationEntry :
            (previous.transform.B destination column).natAbs ≤
              destinationBound := by
          rw [destinationUnchanged]
          exact destinationRowBound column
        calc
          (previous.transform.B source column -
              ComputableEuclideanOps.quot
                  (previous.transform.B source destination)
                  (previous.transform.B destination destination) *
                previous.transform.B destination column).natAbs ≤
              (previous.transform.B source column).natAbs +
                (ComputableEuclideanOps.quot
                    (previous.transform.B source destination)
                    (previous.transform.B destination destination) *
                  previous.transform.B destination column).natAbs :=
            Int.natAbs_sub_le _ _
          _ = (previous.transform.B source column).natAbs +
                (ComputableEuclideanOps.quot
                    (previous.transform.B source destination)
                    (previous.transform.B destination destination)).natAbs *
                  (previous.transform.B destination column).natAbs := by
            rw [Int.natAbs_mul]
          _ ≤ matrixBound + (matrixBound + 1) * destinationBound :=
            Nat.add_le_add sourceEntry
              (Nat.mul_le_mul quotient destinationEntry)
          _ ≤ (matrixBound + 1) * (destinationBound + 1) := by
            nlinarith
      · rw [State.reduceAbove_other_apply source destination row hsource
          equality]
        exact (entry_natAbs_le_matrixHeight previous.transform.B row column).trans
          previousHeight

theorem eliminateStageLoop_next_pair_target_entry_natAbs_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (processed : Nat) (hprocessed : processed < target.val)
    (state : State A)
    (leading : PrefixHermite target.val state.transform.B)
    (diagonal_ne : ∀ row, row.val < target.val →
      state.transform.B row row ≠ 0)
    (column : Fin n) :
    let previous := eliminateStageLoop target processed hprocessed.le state
    let pivot : Fin n := ⟨processed, hprocessed.trans target.isLt⟩
    let eliminated := previous.gcdEliminate pivot target (by
      change processed < target.val
      exact hprocessed)
    (eliminated.transform.B target column).natAbs ≤
      stageMinorHeightBound target.val (matrixHeight state.transform.B) := by
  let previous := eliminateStageLoop target processed hprocessed.le state
  let pivot : Fin n := ⟨processed, hprocessed.trans target.isLt⟩
  have hpivot : pivot < target := by
    change processed < target.val
    exact hprocessed
  let eliminated := previous.gcdEliminate pivot target hpivot
  let finished := eliminateStageLoop target (processed + 1) (by omega) state
  change (eliminated.transform.B target column).natAbs ≤
    stageMinorHeightBound target.val (matrixHeight state.transform.B)
  have unchanged :
      (reduceAboveLoop pivot pivot.val le_rfl eliminated).transform.B
          target column = eliminated.transform.B target column :=
    reduceAboveLoop_row_unchanged pivot pivot.val le_rfl eliminated
      target column (by simp [pivot]; omega)
  have finishedEq : finished.transform.B target column =
      eliminated.transform.B target column := by
    change
      (reduceAboveLoop pivot pivot.val le_rfl eliminated).transform.B
          target column = eliminated.transform.B target column
    exact unchanged
  rw [← finishedEq]
  by_cases hcolumn : processed + 1 ≤ column.val
  · exact (eliminateStageLoop_target_entry_natAbs_le target
      (processed + 1) (by omega) state leading diagonal_ne column hcolumn).trans
        (selectedMinor_le_stageMinorHeightBound (by omega))
  · have invariant : EliminationInvariant target (processed + 1) finished :=
      eliminateStageLoop_invariant target (processed + 1) (by omega)
        state leading
    rw [invariant.targetZero column (by omega), Int.natAbs_zero]
    exact Nat.zero_le _

/-- A single stage Bézout pair preserves any envelope covering its two rows. -/
theorem eliminateStageLoop_next_pair_height_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (processed : Nat) (hprocessed : processed < target.val)
    (state : State A)
    (leading : PrefixHermite target.val state.transform.B)
    (diagonal_ne : ∀ row, row.val < target.val →
      state.transform.B row row ≠ 0)
    (previousBound : Nat)
    (previousHeight :
      matrixHeight
          (eliminateStageLoop target processed hprocessed.le state).transform.B ≤
        previousBound) :
    let previous := eliminateStageLoop target processed hprocessed.le state
    let pivot : Fin n := ⟨processed, hprocessed.trans target.isLt⟩
    let eliminated := previous.gcdEliminate pivot target (by
      change processed < target.val
      exact hprocessed)
    matrixHeight eliminated.transform.B ≤
      max previousBound
        (max
          (stagePairRowHeightBound target.val
            (matrixHeight state.transform.B))
          (stageMinorHeightBound target.val
            (matrixHeight state.transform.B))) := by
  let previous := eliminateStageLoop target processed hprocessed.le state
  let pivot : Fin n := ⟨processed, hprocessed.trans target.isLt⟩
  have hpivot : pivot < target := by
    change processed < target.val
    exact hprocessed
  let eliminated := previous.gcdEliminate pivot target hpivot
  apply matrixHeight_le
  intro row column
  by_cases rowPivot : row = pivot
  · subst row
    exact (eliminateStageLoop_next_pair_pivot_entry_natAbs_le target
      processed hprocessed state leading diagonal_ne column).trans
        ((le_max_left _ _).trans (le_max_right _ _))
  · by_cases rowTarget : row = target
    · subst row
      exact (eliminateStageLoop_next_pair_target_entry_natAbs_le target
        processed hprocessed state leading diagonal_ne column).trans
          ((le_max_right _ _).trans (le_max_right _ _))
    · rw [State.gcdEliminate_other_apply pivot target row hpivot
        rowPivot rowTarget]
      exact (entry_natAbs_le_matrixHeight previous.transform.B row column).trans
        (previousHeight.trans (le_max_left _ _))

theorem eliminateStageLoop_height_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (processed : Nat) → (hprocessed : processed ≤ target.val) →
      (state : State A) →
      PrefixHermite target.val state.transform.B →
      (∀ row, row.val < target.val → state.transform.B row row ≠ 0) →
      matrixHeight
          (eliminateStageLoop target processed hprocessed state).transform.B ≤
        stageIntermediateHeightBound processed target.val
          (matrixHeight state.transform.B)
  | 0, _, state, _, _ => by
      unfold stageIntermediateHeightBound
      simp only [pow_zero, mul_one]
      exact (le_max_left (matrixHeight state.transform.B) _).trans
        (Nat.le_succ _)
  | processed + 1, hprocessed, state, leading, diagonal_ne => by
      let inputHeight := matrixHeight state.transform.B
      let minorBound := stageMinorHeightBound target.val inputHeight
      let pairRowBound := stagePairRowHeightBound target.val inputHeight
      let base := max inputHeight (max minorBound pairRowBound)
      let previous := eliminateStageLoop target processed (by omega) state
      let previousBound := (base + 1) * (pairRowBound + 2) ^ processed
      let pivot : Fin n := ⟨processed, by omega⟩
      have hpivot : pivot < target := by
        change processed < target.val
        omega
      let eliminated := previous.gcdEliminate pivot target hpivot
      have previousHeight : matrixHeight previous.transform.B ≤
          previousBound := by
        simpa [previousBound, base, pairRowBound, minorBound, inputHeight,
          stageIntermediateHeightBound] using
          eliminateStageLoop_height_le target processed (by omega) state
            leading diagonal_ne
      have pairRowLeBase : pairRowBound ≤ base :=
        (le_max_right minorBound pairRowBound).trans (le_max_right _ _)
      have minorLeBase : minorBound ≤ base :=
        (le_max_left minorBound pairRowBound).trans (le_max_right _ _)
      have baseLtPrevious : base < previousBound := by
        have powerPos : 0 < (pairRowBound + 2) ^ processed :=
          pow_pos (by omega) _
        dsimp only [previousBound]
        nlinarith
      have eliminatedHeight : matrixHeight eliminated.transform.B ≤
          previousBound := by
        apply matrixHeight_le
        intro row column
        by_cases rowPivot : row = pivot
        · subst row
          exact (eliminateStageLoop_next_pair_pivot_entry_natAbs_le target
            processed (by omega) state leading diagonal_ne column).trans
              (pairRowLeBase.trans baseLtPrevious.le)
        · by_cases rowTarget : row = target
          · subst row
            exact (eliminateStageLoop_next_pair_target_entry_natAbs_le target
              processed (by omega) state leading diagonal_ne column).trans
                (minorLeBase.trans baseLtPrevious.le)
          · rw [State.gcdEliminate_other_apply pivot target row hpivot
              rowPivot rowTarget]
            exact (entry_natAbs_le_matrixHeight previous.transform.B
              row column).trans previousHeight
      have eliminatedPivotRow : ∀ column,
          (eliminated.transform.B pivot column).natAbs ≤ pairRowBound := by
        intro column
        exact eliminateStageLoop_next_pair_pivot_entry_natAbs_le target
          processed (by omega) state leading diagonal_ne column
      have reducedHeight := reduceAboveLoop_height_le pivot pivot.val le_rfl
        eliminated previousBound pairRowBound eliminatedHeight eliminatedPivotRow
      change matrixHeight
        (reduceAboveLoop pivot pivot.val le_rfl eliminated).transform.B ≤ _
      have recurrence : (previousBound + 1) * (pairRowBound + 1) ≤
          previousBound * (pairRowBound + 2) := by
        have pairLtPrevious : pairRowBound < previousBound :=
          pairRowLeBase.trans_lt baseLtPrevious
        nlinarith
      calc
        matrixHeight
            (reduceAboveLoop pivot pivot.val le_rfl eliminated).transform.B ≤
          (previousBound + 1) * (pairRowBound + 1) := reducedHeight
        _ ≤ previousBound * (pairRowBound + 2) := recurrence
        _ = stageIntermediateHeightBound (processed + 1) target.val
            (matrixHeight state.transform.B) := by
          simp only [previousBound, base, pairRowBound, minorBound, inputHeight,
            stageIntermediateHeightBound, pow_succ]
          ring

theorem eliminateStageLoop_target_row_natAbs_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (state : State A)
    (leading : PrefixHermite target.val state.transform.B)
    (diagonal_ne : ∀ row, row.val < target.val →
      state.transform.B row row ≠ 0)
    (column : Fin n) :
    ((eliminateStageLoop target target.val le_rfl state).transform.B
        target column).natAbs ≤
      stageMinorHeightBound target.val (matrixHeight state.transform.B) := by
  let eliminated := eliminateStageLoop target target.val le_rfl state
  by_cases hcolumn : target.val ≤ column.val
  · exact (eliminateStageLoop_target_entry_natAbs_le target target.val le_rfl
      state leading diagonal_ne column hcolumn).trans
        (selectedMinor_le_stageMinorHeightBound le_rfl)
  · have invariant : EliminationInvariant target target.val eliminated :=
      eliminateStageLoop_invariant target target.val le_rfl state leading
    rw [invariant.targetZero column (by omega), Int.natAbs_zero]
    exact Nat.zero_le _

theorem State.normalize_height_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (row : Fin n) (state : State A) :
    matrixHeight (state.normalize row).transform.B ≤
      matrixHeight state.transform.B := by
  apply matrixHeight_le
  intro current column
  by_cases equality : current = row
  · subst current
    rw [State.normalize_row_apply, Int.natAbs_mul,
      Int.units_natAbs]
    simpa using entry_natAbs_le_matrixHeight state.transform.B row column
  · rw [State.normalize_other_apply row current equality]
    exact entry_natAbs_le_matrixHeight state.transform.B current column

theorem State.normalize_row_natAbs_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (row : Fin n) (state : State A) (bound : Nat)
    (rowBound : ∀ column,
      (state.transform.B row column).natAbs ≤ bound) :
    ∀ column, ((state.normalize row).transform.B row column).natAbs ≤
      bound := by
  intro column
  rw [State.normalize_row_apply, Int.natAbs_mul, Int.units_natAbs]
  simpa using rowBound column

theorem extendStage_height_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (state : State A)
    (leading : PrefixHermite target.val state.transform.B)
    (diagonal_ne : ∀ row, row.val < target.val →
      state.transform.B row row ≠ 0) :
    matrixHeight (extendStage target state).transform.B ≤
      completedStageHeightBound target.val (matrixHeight state.transform.B) := by
  let eliminated := eliminateStageLoop target target.val le_rfl state
  let normalized := eliminated.normalize target
  let eliminatedBound := stageIntermediateHeightBound target.val target.val
    (matrixHeight state.transform.B)
  let targetBound := stageMinorHeightBound target.val
    (matrixHeight state.transform.B)
  have eliminatedHeight : matrixHeight eliminated.transform.B ≤
      eliminatedBound := by
    exact eliminateStageLoop_height_le target target.val le_rfl state
      leading diagonal_ne
  have normalizedHeight : matrixHeight normalized.transform.B ≤
      eliminatedBound :=
    (State.normalize_height_le target eliminated).trans eliminatedHeight
  have eliminatedTarget : ∀ column,
      (eliminated.transform.B target column).natAbs ≤ targetBound :=
    eliminateStageLoop_target_row_natAbs_le target state leading diagonal_ne
  have normalizedTarget : ∀ column,
      (normalized.transform.B target column).natAbs ≤ targetBound :=
    State.normalize_row_natAbs_le target eliminated targetBound eliminatedTarget
  have reduced := reduceAboveLoop_height_le target target.val le_rfl normalized
    eliminatedBound targetBound normalizedHeight normalizedTarget
  change matrixHeight
    (reduceAboveLoop target target.val le_rfl normalized).transform.B ≤ _
  exact reduced

end Principal

end NormalForms.Research.KannanBachem.Hermite
