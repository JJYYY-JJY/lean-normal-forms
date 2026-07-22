/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.IntermediateSize
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal

/-! Arithmetic operands are entries of matrices already represented in the trace. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix

namespace Principal

theorem Transform.B_height_le_intermediate {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} (transform : Transform A) :
    matrixHeight transform.B ≤
      transform.steps.intermediateMatrixHeight A := by
  have replayBound := RowTrace.replay_height_le_intermediateMatrixHeight
    A transform.steps
  have replay_eq : transform.steps.replay A = transform.B := by
    calc
      transform.steps.replay A = transform.steps.accumulator * A :=
        RowTrace.replay_eq_accumulator_mul A transform.steps
      _ = transform.U * A := by rw [transform.accumulator_eq]
      _ = transform.B := transform.equation
  rwa [replay_eq] at replayBound

theorem Transform.intermediate_height_le_trans {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (first : Transform A) (second : Transform first.B) :
    first.steps.intermediateMatrixHeight A ≤
      (first.trans second).steps.intermediateMatrixHeight A := by
  exact RowTrace.intermediateMatrixHeight_le_append A first.steps second.steps

/-- Every recorded arithmetic operand is covered by a represented matrix state. -/
def State.ArithmeticBound {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} (state : State A) : Prop :=
  arithmeticEventListHeight state.arithmeticEvents ≤
    state.transform.steps.intermediateMatrixHeight A

theorem State.ArithmeticBound.refl {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (State.refl A).ArithmeticBound := by
  simp [State.ArithmeticBound, State.refl, arithmeticEventListHeight]

theorem State.ArithmeticBound.of_append {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    {state next : State A} (bound : state.ArithmeticBound)
    (event : PrincipalArithmeticEvent)
    (events_eq : next.arithmeticEvents = state.arithmeticEvents ++ [event])
    (height_mono :
      state.transform.steps.intermediateMatrixHeight A ≤
        next.transform.steps.intermediateMatrixHeight A)
    (event_le : event.operandHeight ≤ matrixHeight state.transform.B) :
    next.ArithmeticBound := by
  unfold State.ArithmeticBound at bound ⊢
  rw [events_eq, arithmeticEventListHeight_append]
  simp only [arithmeticEventListHeight, max_zero]
  exact (max_le bound
    (event_le.trans state.transform.B_height_le_intermediate)).trans height_mono

theorem State.ArithmeticBound.gcdEliminate {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    {state : State A} (bound : state.ArithmeticBound) :
    (state.gcdEliminate pivot target hlt).ArithmeticBound := by
  apply bound.of_append
    (.xgcd pivot.val target.val
      (state.transform.B pivot pivot) (state.transform.B target pivot))
  · rfl
  · simp only [State.gcdEliminate]
    unfold pairBezoutAt
    exact Transform.intermediate_height_le_trans _ _
  · simp only [PrincipalArithmeticEvent.operandHeight]
    exact max_le
      (entry_natAbs_le_matrixHeight state.transform.B pivot pivot)
      (entry_natAbs_le_matrixHeight state.transform.B target pivot)

theorem State.ArithmeticBound.reduceAbove {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination)
    {state : State A} (bound : state.ArithmeticBound) :
    (state.reduceAbove source destination hlt).ArithmeticBound := by
  apply bound.of_append
    (.divMod source.val destination.val
      (state.transform.B source destination)
      (state.transform.B destination destination))
  · rfl
  · simp only [State.reduceAbove]
    exact Transform.intermediate_height_le_trans _ _
  · simp only [PrincipalArithmeticEvent.operandHeight]
    exact max_le
      (entry_natAbs_le_matrixHeight state.transform.B source destination)
      (entry_natAbs_le_matrixHeight state.transform.B destination destination)

theorem State.ArithmeticBound.normalize {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (row : Fin n) {state : State A} (bound : state.ArithmeticBound) :
    (state.normalize row).ArithmeticBound := by
  apply bound.of_append (.normalize row.val (state.transform.B row row))
  · rfl
  · simp only [State.normalize]
    exact Transform.intermediate_height_le_trans _ _
  · exact entry_natAbs_le_matrixHeight state.transform.B row row

theorem reduceAboveLoop_arithmeticBound {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → (hk : k ≤ destination.val) → (state : State A) →
      state.ArithmeticBound →
        (reduceAboveLoop destination k hk state).ArithmeticBound
  | 0, _, _, bound => bound
  | k + 1, hk, state, bound => by
      let previous := reduceAboveLoop destination k (by omega) state
      let source : Fin n := ⟨k, by omega⟩
      have previousBound := reduceAboveLoop_arithmeticBound destination k
        (by omega) state bound
      exact previousBound.reduceAbove source destination (by
        change k < destination.val
        omega)

theorem eliminateStageLoop_arithmeticBound {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (k : Nat) → (hk : k ≤ target.val) → (state : State A) →
      state.ArithmeticBound →
        (eliminateStageLoop target k hk state).ArithmeticBound
  | 0, _, _, bound => bound
  | k + 1, hk, state, bound => by
      let previous := eliminateStageLoop target k (by omega) state
      let pivot : Fin n := ⟨k, by omega⟩
      have previousBound := eliminateStageLoop_arithmeticBound target k
        (by omega) state bound
      have eliminatedBound := previousBound.gcdEliminate pivot target (by
        change k < target.val
        omega)
      exact reduceAboveLoop_arithmeticBound pivot pivot.val le_rfl _
        eliminatedBound

theorem extendStage_arithmeticBound {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (state : State A) (bound : state.ArithmeticBound) :
    (extendStage target state).ArithmeticBound := by
  let eliminated := eliminateStageLoop target target.val le_rfl state
  have eliminatedBound := eliminateStageLoop_arithmeticBound target target.val
    le_rfl state bound
  let normalized := eliminated.normalize target
  have normalizedBound := eliminatedBound.normalize target
  exact reduceAboveLoop_arithmeticBound target target.val le_rfl normalized
    normalizedBound

theorem stageLoop_arithmeticBound {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : State A) →
      state.ArithmeticBound → (stageLoop k hk state).ArithmeticBound
  | 0, _, _, bound => bound
  | k + 1, hk, state, bound => by
      let previous := stageLoop k (by omega) state
      have previousBound := stageLoop_arithmeticBound k (by omega) state bound
      exact extendStage_arithmeticBound ⟨k, by omega⟩ previous previousBound

theorem compute_arithmeticBound {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (compute A).ArithmeticBound :=
  stageLoop_arithmeticBound n le_rfl (State.refl A)
    (State.ArithmeticBound.refl A)

end Principal

/-- Every principal xgcd/division/normalization operand occurs in a traced matrix. -/
public theorem principalArithmeticOperandHeight_le_intermediateMatrixHeight
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int) :
    principalArithmeticOperandHeight A ≤
      principalIntermediateMatrixHeight A := by
  change arithmeticEventListHeight (Principal.compute A).arithmeticEvents ≤
    (Principal.compute A).transform.steps.intermediateMatrixHeight A
  exact Principal.compute_arithmeticBound A

/-- The same coverage statement at binary-length level. -/
public theorem principalArithmeticOperandBitLength_le_intermediateMatrixBitLength
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int) :
    principalArithmeticOperandBitLength A ≤
      principalIntermediateMatrixBitLength A :=
  Nat.size_le_size
    (principalArithmeticOperandHeight_le_intermediateMatrixHeight A)

end NormalForms.Research.KannanBachem.Hermite
