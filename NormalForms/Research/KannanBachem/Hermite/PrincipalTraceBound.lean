/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalIntermediateBound
public import NormalForms.Research.KannanBachem.Hermite.PrincipalStageSize
public import NormalForms.Research.KannanBachem.Hermite.IntermediateSize
import all NormalForms.Research.KannanBachem.Hermite.PrincipalIntermediateBound
import all NormalForms.Research.KannanBachem.Hermite.PrincipalOperandBound
import all NormalForms.Research.KannanBachem.Hermite.PrincipalStageSize

/-! Trace-level coefficient envelopes for the principal-minor HNF kernel. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite

namespace Principal

theorem Transform.replay_eq_B {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} (transform : Transform A) :
    transform.steps.replay A = transform.B := by
  calc
    transform.steps.replay A = transform.steps.accumulator * A :=
      RowTrace.replay_eq_accumulator_mul A transform.steps
    _ = transform.U * A := by rw [transform.accumulator_eq]
    _ = transform.B := transform.equation

theorem Transform.trans_intermediateMatrixHeight_le {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (first : Transform A) (second : Transform first.B)
    (first_le : first.steps.intermediateMatrixHeight A ≤ bound)
    (second_le : second.steps.intermediateMatrixHeight first.B ≤ bound) :
    (first.trans second).steps.intermediateMatrixHeight A ≤ bound := by
  change (first.steps ++ second.steps).intermediateMatrixHeight A ≤ bound
  apply RowTrace.intermediateMatrixHeight_append_le A first.steps second.steps
    first_le
  rwa [first.replay_eq_B]

theorem RowTrace.singleton_intermediateMatrixHeight_le {n bound : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int)
    (step : ReversibleRowStep Int n)
    (input_le : matrixHeight A ≤ bound)
    (output_le : matrixHeight (step.forward * A) ≤ bound) :
    RowTrace.intermediateMatrixHeight A ([step] : RowTrace Int n) ≤ bound := by
  simp only [RowTrace.intermediateMatrixHeight, RowTrace.intermediates,
    matrixListHeight, max_zero, max_le_iff]
  exact ⟨input_le, output_le⟩

theorem Transform.ofPrimitive_intermediateMatrixHeight_le {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (U : _root_.Matrix (Fin n) (Fin n) Int)
    (certificate : MatrixInverseCertificate U)
    (B : _root_.Matrix (Fin n) (Fin n) Int)
    (equation : U * A = B)
    (kind : RowOperationKind) (hkind : kind ≠ .certifiedBlock)
    (input_le : matrixHeight A ≤ bound)
    (output_le : matrixHeight B ≤ bound) :
    ((Transform.ofPrimitive U certificate B equation kind hkind).steps
        |>.intermediateMatrixHeight A) ≤ bound := by
  apply RowTrace.singleton_intermediateMatrixHeight_le
  · exact input_le
  · simpa [ReversibleRowStep.ofCertificate, equation] using output_le

theorem State.gcdEliminate_intermediateMatrixHeight_le {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target) (state : State A)
    (trace_le : state.transform.steps.intermediateMatrixHeight A ≤ bound)
    (output_le :
      matrixHeight (state.gcdEliminate pivot target hlt).transform.B ≤ bound) :
    ((state.gcdEliminate pivot target hlt).transform.steps
        |>.intermediateMatrixHeight A) ≤ bound := by
  unfold State.gcdEliminate pairBezoutAt
  apply Transform.trans_intermediateMatrixHeight_le
  · exact trace_le
  · apply Transform.ofPrimitive_intermediateMatrixHeight_le
    · exact state.transform.B_height_le_intermediate.trans trace_le
    · exact output_le

theorem State.reduceAbove_intermediateMatrixHeight_le {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination) (state : State A)
    (trace_le : state.transform.steps.intermediateMatrixHeight A ≤ bound)
    (output_le :
      matrixHeight (state.reduceAbove source destination hlt).transform.B ≤ bound) :
    ((state.reduceAbove source destination hlt).transform.steps
        |>.intermediateMatrixHeight A) ≤ bound := by
  unfold State.reduceAbove
  apply Transform.trans_intermediateMatrixHeight_le
  · exact trace_le
  · apply Transform.ofPrimitive_intermediateMatrixHeight_le
    · exact state.transform.B_height_le_intermediate.trans trace_le
    · exact output_le

theorem State.normalize_intermediateMatrixHeight_le {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (row : Fin n) (state : State A)
    (trace_le : state.transform.steps.intermediateMatrixHeight A ≤ bound)
    (output_le : matrixHeight (state.normalize row).transform.B ≤ bound) :
    ((state.normalize row).transform.steps
        |>.intermediateMatrixHeight A) ≤ bound := by
  unfold State.normalize
  apply Transform.trans_intermediateMatrixHeight_le
  · exact trace_le
  · apply Transform.ofPrimitive_intermediateMatrixHeight_le
    · exact state.transform.B_height_le_intermediate.trans trace_le
    · exact output_le

theorem reduceAboveLoop_intermediateMatrixHeight_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → (hk : k ≤ destination.val) → (state : State A) →
      (matrixBound destinationBound bound : Nat) →
      state.transform.steps.intermediateMatrixHeight A ≤ bound →
      matrixHeight state.transform.B ≤ matrixBound →
      (∀ column, (state.transform.B destination column).natAbs ≤
        destinationBound) →
      (matrixBound + 1) * (destinationBound + 1) ≤ bound →
      ((reduceAboveLoop destination k hk state).transform.steps
          |>.intermediateMatrixHeight A) ≤ bound
  | 0, _, state, _, _, _, trace_le, _, _, _ => trace_le
  | k + 1, hk, state, matrixBound, destinationBound, bound,
      trace_le, height_le, destination_le, envelope_le => by
      let previous := reduceAboveLoop destination k (by omega) state
      let source : Fin n := ⟨k, by omega⟩
      have hsource : source < destination := by
        change k < destination.val
        omega
      have previousTrace := reduceAboveLoop_intermediateMatrixHeight_le
        destination k (by omega) state matrixBound destinationBound bound
        trace_le height_le destination_le envelope_le
      have outputHeight :
          matrixHeight
              (reduceAboveLoop destination (k + 1) hk state).transform.B ≤
            bound :=
        (reduceAboveLoop_height_le destination (k + 1) hk state
          matrixBound destinationBound height_le destination_le).trans
            envelope_le
      change ((previous.reduceAbove source destination hsource).transform.steps
          |>.intermediateMatrixHeight A) ≤ bound
      apply State.reduceAbove_intermediateMatrixHeight_le
      · exact previousTrace
      · exact outputHeight

theorem stageIntermediateHeightBound_mono_processed
    {smaller larger target inputHeight : Nat} (hle : smaller ≤ larger) :
    stageIntermediateHeightBound smaller target inputHeight ≤
      stageIntermediateHeightBound larger target inputHeight := by
  unfold stageIntermediateHeightBound
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by omega) hle

theorem eliminateStageLoop_intermediateMatrixHeight_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (processed : Nat) → (hprocessed : processed ≤ target.val) →
      (state : State A) →
      (leading : PrefixHermite target.val state.transform.B) →
      (diagonal_ne : ∀ row, row.val < target.val →
        state.transform.B row row ≠ 0) →
      (bound : Nat) →
      state.transform.steps.intermediateMatrixHeight A ≤ bound →
      stageIntermediateHeightBound processed target.val
          (matrixHeight state.transform.B) ≤ bound →
      ((eliminateStageLoop target processed hprocessed state).transform.steps
          |>.intermediateMatrixHeight A) ≤ bound
  | 0, _, _, _, _, _, trace_le, _ => trace_le
  | processed + 1, hprocessed, state, leading, diagonal_ne, bound,
      trace_le, envelope_le => by
      let inputHeight := matrixHeight state.transform.B
      let minorBound := stageMinorHeightBound target.val inputHeight
      let pairRowBound := stagePairRowHeightBound target.val inputHeight
      let base := max inputHeight (max minorBound pairRowBound)
      let previousBound :=
        stageIntermediateHeightBound processed target.val inputHeight
      let currentBound :=
        stageIntermediateHeightBound (processed + 1) target.val inputHeight
      let previous := eliminateStageLoop target processed (by omega) state
      let pivot : Fin n := ⟨processed, by omega⟩
      have hpivot : pivot < target := by
        change processed < target.val
        omega
      let eliminated := previous.gcdEliminate pivot target hpivot
      have previousLeCurrent : previousBound ≤ currentBound :=
        stageIntermediateHeightBound_mono_processed (by omega)
      have previousEnvelope : previousBound ≤ bound :=
        previousLeCurrent.trans envelope_le
      have previousTrace := eliminateStageLoop_intermediateMatrixHeight_le
        target processed (by omega) state leading diagonal_ne bound trace_le
          previousEnvelope
      have previousHeight : matrixHeight previous.transform.B ≤ previousBound :=
        eliminateStageLoop_height_le target processed (by omega) state
          leading diagonal_ne
      have pairRowLeBase : pairRowBound ≤ base :=
        (le_max_right minorBound pairRowBound).trans (le_max_right _ _)
      have minorLeBase : minorBound ≤ base :=
        (le_max_left minorBound pairRowBound).trans (le_max_right _ _)
      have baseLtPrevious : base < previousBound := by
        have powerPos : 0 < (pairRowBound + 2) ^ processed :=
          pow_pos (by omega) _
        have baseSuccLe : base + 1 ≤ previousBound := by
          change base + 1 ≤ (base + 1) * (pairRowBound + 2) ^ processed
          exact Nat.le_mul_of_pos_right _ powerPos
        omega
      have eliminatedHeight : matrixHeight eliminated.transform.B ≤
          previousBound := by
        have pairHeight := eliminateStageLoop_next_pair_height_le target
          processed (by omega) state leading diagonal_ne previousBound
            previousHeight
        exact pairHeight.trans <| max_le le_rfl <| max_le
          (pairRowLeBase.trans baseLtPrevious.le)
          (minorLeBase.trans baseLtPrevious.le)
      have eliminatedTrace :
          eliminated.transform.steps.intermediateMatrixHeight A ≤ bound := by
        apply State.gcdEliminate_intermediateMatrixHeight_le
        · exact previousTrace
        · exact eliminatedHeight.trans previousEnvelope
      have eliminatedPivotRow : ∀ column,
          (eliminated.transform.B pivot column).natAbs ≤ pairRowBound := by
        intro column
        exact eliminateStageLoop_next_pair_pivot_entry_natAbs_le target
          processed (by omega) state leading diagonal_ne column
      have recurrence : (previousBound + 1) * (pairRowBound + 1) ≤
          currentBound := by
        have pairLtPrevious : pairRowBound < previousBound :=
          pairRowLeBase.trans_lt baseLtPrevious
        have stepRecurrence : (previousBound + 1) * (pairRowBound + 1) ≤
            previousBound * (pairRowBound + 2) := by
          nlinarith
        exact stepRecurrence.trans_eq <| by
          simp only [previousBound, currentBound, inputHeight,
            stageIntermediateHeightBound, pow_succ]
          ring
      change
        ((reduceAboveLoop pivot pivot.val le_rfl eliminated).transform.steps
            |>.intermediateMatrixHeight A) ≤ bound
      exact reduceAboveLoop_intermediateMatrixHeight_le pivot pivot.val le_rfl
        eliminated previousBound pairRowBound bound eliminatedTrace
          eliminatedHeight eliminatedPivotRow (recurrence.trans envelope_le)

theorem stageIntermediateHeightBound_le_completedStageHeightBound
    (target inputHeight : Nat) :
    stageIntermediateHeightBound target target inputHeight ≤
      completedStageHeightBound target inputHeight := by
  unfold completedStageHeightBound
  have positive : 0 < stageMinorHeightBound target inputHeight + 1 := by omega
  exact (Nat.le_succ _).trans
    (Nat.le_mul_of_pos_right _ positive)

theorem extendStage_intermediateMatrixHeight_le {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (state : State A)
    (leading : PrefixHermite target.val state.transform.B)
    (diagonal_ne : ∀ row, row.val < target.val →
      state.transform.B row row ≠ 0)
    (trace_le : state.transform.steps.intermediateMatrixHeight A ≤ bound)
    (envelope_le :
      completedStageHeightBound target.val
          (matrixHeight state.transform.B) ≤ bound) :
    (extendStage target state).transform.steps.intermediateMatrixHeight A ≤
      bound := by
  let inputHeight := matrixHeight state.transform.B
  let eliminated := eliminateStageLoop target target.val le_rfl state
  let normalized := eliminated.normalize target
  let eliminatedBound :=
    stageIntermediateHeightBound target.val target.val inputHeight
  let targetBound := stageMinorHeightBound target.val inputHeight
  have eliminatedEnvelope : eliminatedBound ≤ bound :=
    (stageIntermediateHeightBound_le_completedStageHeightBound
      target.val inputHeight).trans envelope_le
  have eliminatedHeight : matrixHeight eliminated.transform.B ≤
      eliminatedBound :=
    eliminateStageLoop_height_le target target.val le_rfl state leading
      diagonal_ne
  have eliminatedTrace :
      eliminated.transform.steps.intermediateMatrixHeight A ≤ bound :=
    eliminateStageLoop_intermediateMatrixHeight_le target target.val le_rfl
      state leading diagonal_ne bound trace_le eliminatedEnvelope
  have normalizedHeight : matrixHeight normalized.transform.B ≤
      eliminatedBound :=
    (State.normalize_height_le target eliminated).trans eliminatedHeight
  have normalizedTrace :
      normalized.transform.steps.intermediateMatrixHeight A ≤ bound := by
    apply State.normalize_intermediateMatrixHeight_le
    · exact eliminatedTrace
    · exact normalizedHeight.trans eliminatedEnvelope
  have eliminatedTarget : ∀ column,
      (eliminated.transform.B target column).natAbs ≤ targetBound :=
    eliminateStageLoop_target_row_natAbs_le target state leading diagonal_ne
  have normalizedTarget : ∀ column,
      (normalized.transform.B target column).natAbs ≤ targetBound :=
    State.normalize_row_natAbs_le target eliminated targetBound eliminatedTarget
  change
    ((reduceAboveLoop target target.val le_rfl normalized).transform.steps
        |>.intermediateMatrixHeight A) ≤ bound
  exact reduceAboveLoop_intermediateMatrixHeight_le target target.val le_rfl
    normalized eliminatedBound targetBound bound normalizedTrace
      normalizedHeight normalizedTarget envelope_le

theorem stageMinorHeightBound_mono_input {target smaller larger : Nat}
    (hle : smaller ≤ larger) :
    stageMinorHeightBound target smaller ≤
      stageMinorHeightBound target larger := by
  unfold stageMinorHeightBound
  gcongr

theorem stagePairOperandHeightBound_mono_input {target smaller larger : Nat}
    (hle : smaller ≤ larger) :
    stagePairOperandHeightBound target smaller ≤
      stagePairOperandHeightBound target larger := by
  unfold stagePairOperandHeightBound
  exact max_le_max hle (stageMinorHeightBound_mono_input hle)

theorem stagePairCoefficientHeightBound_mono_input
    {target smaller larger : Nat} (hle : smaller ≤ larger) :
    stagePairCoefficientHeightBound target smaller ≤
      stagePairCoefficientHeightBound target larger := by
  unfold stagePairCoefficientHeightBound
  gcongr
  exact stagePairOperandHeightBound_mono_input hle

theorem stagePairRowHeightBound_mono_input {target smaller larger : Nat}
    (hle : smaller ≤ larger) :
    stagePairRowHeightBound target smaller ≤
      stagePairRowHeightBound target larger := by
  unfold stagePairRowHeightBound
  exact Nat.mul_le_mul
    (Nat.mul_le_mul_left 2
      (stagePairCoefficientHeightBound_mono_input hle))
    (stagePairOperandHeightBound_mono_input hle)

theorem stageIntermediateHeightBound_mono_input
    (processed : Nat) {target smaller larger : Nat} (hle : smaller ≤ larger) :
    stageIntermediateHeightBound processed target smaller ≤
      stageIntermediateHeightBound processed target larger := by
  unfold stageIntermediateHeightBound
  have minorLe := stageMinorHeightBound_mono_input
    (target := target) hle
  have pairLe := stagePairRowHeightBound_mono_input
    (target := target) hle
  exact Nat.mul_le_mul
    (Nat.add_le_add_right (max_le_max hle (max_le_max minorLe pairLe)) 1)
    (Nat.pow_le_pow_left (Nat.add_le_add_right pairLe 2) processed)

theorem completedStageHeightBound_mono_input
    {target smaller larger : Nat} (hle : smaller ≤ larger) :
    completedStageHeightBound target smaller ≤
      completedStageHeightBound target larger := by
  unfold completedStageHeightBound
  exact Nat.mul_le_mul
    (Nat.add_le_add_right
      (stageIntermediateHeightBound_mono_input target hle) 1)
    (Nat.add_le_add_right (stageMinorHeightBound_mono_input hle) 1)

/-- Height envelope reconstructed from a stage-boundary bit budget. -/
@[expose] public def stageStartHeightBound (k inputBits : Nat) : Nat :=
  2 ^ stageStartBitLengthBound k inputBits

/--
Uniform envelope for every transformed matrix in the first `k` stages.
The recursion takes the maximum of the preceding trace and the next stage's
paper-level determinant envelope.
-/
@[expose] public def principalIntermediateHeightBound : Nat → Nat → Nat
  | 0, inputBits => 2 ^ inputBits
  | k + 1, inputBits =>
      max (principalIntermediateHeightBound k inputBits)
        (completedStageHeightBound k (stageStartHeightBound k inputBits))

/-- Binary-length form of `principalIntermediateHeightBound`. -/
@[expose] public def principalIntermediateBitLengthBound
    (n inputBits : Nat) : Nat :=
  Nat.size (principalIntermediateHeightBound n inputBits)

theorem matrixHeight_lt_two_pow_matrixBitLength {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    matrixHeight A < 2 ^ matrixBitLength A := by
  exact Nat.lt_size_self (matrixHeight A)

theorem stageLoop_refl_height_le_stageStartHeightBound {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n)
    (ready : PrincipalReady A) :
    matrixHeight (stageLoop k hk (State.refl A)).transform.B ≤
      stageStartHeightBound k (matrixBitLength A) := by
  have bitLength := stageLoop_refl_bitLength_le A hk ready
  have strict := matrixHeight_lt_two_pow_matrixBitLength
    (stageLoop k hk (State.refl A)).transform.B
  unfold stageStartHeightBound
  exact strict.le.trans <| Nat.pow_le_pow_right (by omega) bitLength

theorem stageLoop_refl_diagonal_ne {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n)
    (ready : PrincipalReady A) :
    ∀ row, row.val < k →
      (stageLoop k hk (State.refl A)).transform.B row row ≠ 0 := by
  let stage := stageLoop k hk (State.refl A)
  have leadingPrefix : PrefixHermite k
      (leadingSubmatrix hk stage.transform.B) :=
    (stageLoop_correct k hk (State.refl A)).leadingSubmatrix hk
  have determinant_ne :
      (leadingSubmatrix hk stage.transform.B).det ≠ 0 :=
    stageLoop_refl_leading_det_ne A hk ready
  have diagonal := leadingPrefix.diagonal_ne_of_det_ne determinant_ne
  intro row hrow
  let prefixRow : Fin k := ⟨row.val, hrow⟩
  have castRow : Fin.castLE hk prefixRow = row := Fin.ext rfl
  have entry := diagonal prefixRow
  simpa [leadingSubmatrix, prefixRow, castRow] using entry

theorem stageLoop_refl_intermediateMatrixHeight_le {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n)
    (ready : PrincipalReady A) :
    ((stageLoop k hk (State.refl A)).transform.steps
        |>.intermediateMatrixHeight A) ≤
      principalIntermediateHeightBound k (matrixBitLength A) := by
  induction k with
  | zero =>
      simpa [stageLoop, State.refl, Transform.refl,
        RowTrace.intermediateMatrixHeight, RowTrace.intermediates,
        matrixListHeight, principalIntermediateHeightBound] using
          (matrixHeight_lt_two_pow_matrixBitLength A).le
  | succ k ih =>
      let previous := stageLoop k (by omega) (State.refl A)
      let target : Fin n := ⟨k, by omega⟩
      let previousTraceBound :=
        principalIntermediateHeightBound k (matrixBitLength A)
      let stageEnvelope := completedStageHeightBound k
        (stageStartHeightBound k (matrixBitLength A))
      let currentBound := max previousTraceBound stageEnvelope
      have previousTrace :
          previous.transform.steps.intermediateMatrixHeight A ≤
            previousTraceBound :=
        ih (by omega)
      have leading : PrefixHermite target.val previous.transform.B := by
        exact stageLoop_correct k (by omega) (State.refl A)
      have diagonal_ne : ∀ row, row.val < target.val →
          previous.transform.B row row ≠ 0 := by
        exact stageLoop_refl_diagonal_ne A (by omega) ready
      have inputHeight : matrixHeight previous.transform.B ≤
          stageStartHeightBound k (matrixBitLength A) :=
        stageLoop_refl_height_le_stageStartHeightBound A (by omega) ready
      have actualEnvelope :
          completedStageHeightBound target.val
              (matrixHeight previous.transform.B) ≤ stageEnvelope := by
        exact completedStageHeightBound_mono_input inputHeight
      change ((extendStage target previous).transform.steps
          |>.intermediateMatrixHeight A) ≤ currentBound
      apply extendStage_intermediateMatrixHeight_le target previous leading
        diagonal_ne
      · exact previousTrace.trans (le_max_left _ _)
      · exact actualEnvelope.trans (le_max_right _ _)

end Principal

/-- Every transformed matrix in a ready principal-minor run has explicit height. -/
public theorem principalIntermediateMatrixHeight_le_of_ready {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int)
    (ready : Principal.PrincipalReady A) :
    principalIntermediateMatrixHeight A ≤
      Principal.principalIntermediateHeightBound n (matrixBitLength A) := by
  change (Principal.compute A).transform.steps.intermediateMatrixHeight A ≤ _
  exact Principal.stageLoop_refl_intermediateMatrixHeight_le A le_rfl ready

/-- Binary-length consequence of the trace-level height theorem. -/
public theorem principalIntermediateMatrixBitLength_le_of_ready {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int)
    (ready : Principal.PrincipalReady A) :
    principalIntermediateMatrixBitLength A ≤
      Principal.principalIntermediateBitLengthBound n (matrixBitLength A) :=
  Nat.size_le_size (principalIntermediateMatrixHeight_le_of_ready A ready)

end NormalForms.Research.KannanBachem.Hermite
