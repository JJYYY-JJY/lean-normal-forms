/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalChecker
public import NormalForms.Research.KannanBachem.Hermite.OperationBound
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal

/-! Ring-operation bound for the principal-minor HNF schedule. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix

namespace Principal

theorem State.gcdEliminate_steps_length {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target) (state : State A) :
    (state.gcdEliminate pivot target hlt).transform.steps.length =
      state.transform.steps.length + 1 := by
  simp [State.gcdEliminate, pairBezoutAt, Transform.trans,
    Transform.ofPrimitive]

theorem State.reduceAbove_steps_length {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination) (state : State A) :
    (state.reduceAbove source destination hlt).transform.steps.length =
      state.transform.steps.length + 1 := by
  simp [State.reduceAbove, Transform.trans, Transform.add,
    Transform.ofPrimitive]

theorem State.normalize_steps_length {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (row : Fin n) (state : State A) :
    (state.normalize row).transform.steps.length =
      state.transform.steps.length + 1 := by
  simp [State.normalize, Transform.trans, Transform.unitScale,
    Transform.ofPrimitive]

theorem reduceAboveLoop_steps_length {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → (hk : k ≤ destination.val) → (state : State A) →
      (reduceAboveLoop destination k hk state).transform.steps.length =
        state.transform.steps.length + k
  | 0, _, _ => by simp [reduceAboveLoop]
  | k + 1, hk, state => by
      let previous := reduceAboveLoop destination k (by omega) state
      let source : Fin n := ⟨k, by omega⟩
      have hsource : source < destination := by
        change k < destination.val
        omega
      change
        (previous.reduceAbove source destination hsource).transform.steps.length =
          state.transform.steps.length + (k + 1)
      rw [State.reduceAbove_steps_length,
        reduceAboveLoop_steps_length destination k (by omega) state]
      omega

theorem eliminateStageLoop_steps_length_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (k : Nat) → (hk : k ≤ target.val) → (state : State A) →
      (eliminateStageLoop target k hk state).transform.steps.length ≤
        state.transform.steps.length + k * (target.val + 1)
  | 0, _, _ => by simp [eliminateStageLoop]
  | k + 1, hk, state => by
      let previous := eliminateStageLoop target k (by omega) state
      let pivot : Fin n := ⟨k, by omega⟩
      have hpivot : pivot < target := by
        change k < target.val
        omega
      let eliminated := previous.gcdEliminate pivot target hpivot
      have previousBound := eliminateStageLoop_steps_length_le target k
        (by omega) state
      have eliminatedLength := State.gcdEliminate_steps_length
        pivot target hpivot previous
      have reducedLength := reduceAboveLoop_steps_length pivot pivot.val le_rfl eliminated
      change
        (reduceAboveLoop pivot pivot.val le_rfl eliminated).transform.steps.length ≤
          state.transform.steps.length + (k + 1) * (target.val + 1)
      rw [reducedLength, eliminatedLength]
      dsimp [pivot]
      nlinarith

theorem extendStage_steps_length_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (state : State A) :
    (extendStage target state).transform.steps.length ≤
      state.transform.steps.length + (target.val + 1) ^ 2 := by
  let eliminated := eliminateStageLoop target target.val le_rfl state
  let normalized := eliminated.normalize target
  have eliminatedBound := eliminateStageLoop_steps_length_le target target.val
    le_rfl state
  have normalizedLength := State.normalize_steps_length target eliminated
  have reducedLength := reduceAboveLoop_steps_length target target.val le_rfl normalized
  change
    (reduceAboveLoop target target.val le_rfl normalized).transform.steps.length ≤
      state.transform.steps.length + (target.val + 1) ^ 2
  rw [reducedLength, normalizedLength]
  nlinarith

theorem stageLoop_steps_length_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : State A) →
      (stageLoop k hk state).transform.steps.length ≤
        state.transform.steps.length + k * n ^ 2
  | 0, _, _ => by simp [stageLoop]
  | k + 1, hk, state => by
      let previous := stageLoop k (by omega) state
      let target : Fin n := ⟨k, by omega⟩
      have previousBound := stageLoop_steps_length_le k (by omega) state
      have stageBound := extendStage_steps_length_le target previous
      change
        (extendStage target previous).transform.steps.length ≤
          state.transform.steps.length + (k + 1) * n ^ 2
      dsimp [target] at stageBound
      nlinarith

theorem compute_steps_length_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (compute A).transform.steps.length ≤ n ^ 3 := by
  have bound := stageLoop_steps_length_le n le_rfl (State.refl A)
  have simplified :
      (compute A).transform.steps.length ≤ n * n ^ 2 := by
    simpa [compute, State.refl, Transform.refl] using bound
  calc
    (compute A).transform.steps.length ≤ n * n ^ 2 := simplified
    _ = n ^ 3 := by ring

end Principal

/-- The principal trace contains at most `n^3` primitive row steps. -/
public theorem principalRun_steps_length_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (principalRun A).steps.length ≤ n ^ 3 := by
  change (Principal.compute A).transform.steps.length ≤ n ^ 3
  exact Principal.compute_steps_length_le A

/-- Ring-operation accounting for the principal-minor trace. -/
@[expose] public def principalRingOperations {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : RingOperationCount :=
  RingOperationCount.ofTrace n (principalRun A).steps

/-- Closed dimension-only algebraic-operation budget. -/
@[expose] public def principalRingOperationBound (n : Nat) : Nat :=
  n * (3 * n ^ 3) + n * (6 * n ^ 3) + 2 * n ^ 3

public theorem principalRingOperationBound_eq (n : Nat) :
    principalRingOperationBound n = 9 * n ^ 4 + 2 * n ^ 3 := by
  simp [principalRingOperationBound]
  ring

public theorem principalRingOperations_total_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (principalRingOperations A).total ≤ principalRingOperationBound n := by
  exact RingOperationCount.total_le_of_length (principalRun A).steps
    (principalRun_steps_length_le A)

end NormalForms.Research.KannanBachem.Hermite
