/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalTypes
import all NormalForms.Research.KannanBachem.Hermite.BoundedXGCD
import all NormalForms.Matrix.Hermite.Bezout

/-! Internal reversible state machine for the principal-minor HNF schedule. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix
open NormalForms
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

namespace Principal

/-- Transform state pairing the core certificate with primitive steps. -/
structure Transform {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) where
  U : _root_.Matrix (Fin m) (Fin m) Int
  U_cert : MatrixInverseCertificate U
  B : _root_.Matrix (Fin m) (Fin n) Int
  equation : U * A = B
  steps : RowTrace Int m
  accumulator_eq : steps.accumulator = U
  inverseAccumulator_eq : steps.inverseAccumulator = U_cert.inverse
  primitive : steps.IsPrimitive

def Transform.refl {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) : Transform A :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    B := A
    equation := NormalForms.Matrix.Constructive.one_mul A
    steps := []
    accumulator_eq := by simp [RowTrace.accumulator]
    inverseAccumulator_eq := by
      simp [RowTrace.inverseAccumulator, MatrixInverseCertificate.one]
    primitive := by
      simp [RowTrace.IsPrimitive, RowTrace.operationCount] }

def Transform.trans {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (first : Transform A) (second : Transform first.B) : Transform A :=
  { U := second.U * first.U
    U_cert := second.U_cert.mul first.U_cert
    B := second.B
    equation := by
      calc
        (second.U * first.U) * A = second.U * (first.U * A) := by
          rw [NormalForms.Matrix.Constructive.mul_assoc]
        _ = second.U * first.B := by rw [first.equation]
        _ = second.B := second.equation
    steps := first.steps ++ second.steps
    accumulator_eq := by
      rw [RowTrace.accumulator_append, second.accumulator_eq,
        first.accumulator_eq]
    inverseAccumulator_eq := by
      rw [RowTrace.inverseAccumulator_append, first.inverseAccumulator_eq,
        second.inverseAccumulator_eq]
      rfl
    primitive := (RowTrace.isPrimitive_append first.steps second.steps).2
      ⟨first.primitive, second.primitive⟩ }

def Transform.ofPrimitive {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (U : _root_.Matrix (Fin m) (Fin m) Int)
    (U_cert : MatrixInverseCertificate U)
    (B : _root_.Matrix (Fin m) (Fin n) Int)
    (equation : U * A = B)
    (kind : RowOperationKind) (hkind : kind ≠ .certifiedBlock) : Transform A :=
  { U
    U_cert
    B
    equation
    steps := [ReversibleRowStep.ofCertificate kind U_cert]
    accumulator_eq := by
      simp [RowTrace.accumulator, ReversibleRowStep.ofCertificate]
    inverseAccumulator_eq := by
      simp [RowTrace.inverseAccumulator, ReversibleRowStep.ofCertificate]
    primitive := by
      cases kind <;>
        simp_all [RowTrace.IsPrimitive, RowTrace.operationCount,
          OperationCount.singleton, OperationCount.add,
          ReversibleRowStep.ofCertificate] }

def Transform.swap {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (i j : Fin m) : Transform A :=
  Transform.ofPrimitive
    (rowOperationMatrix (.swap i j))
    (rowSwapInverseCertificate i j)
    (applyRowOperation A (.swap i j))
    (rowOperationMatrix_mul A (.swap i j))
    .swap (by decide)

def Transform.add {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (source destination : Fin m) (coefficient : Int)
    (hne : source ≠ destination) : Transform A :=
  Transform.ofPrimitive
    (rowOperationMatrix (.add source destination coefficient))
    (rowAddInverseCertificate source destination coefficient hne)
    (applyRowOperation A (.add source destination coefficient))
    (rowOperationMatrix_mul A (.add source destination coefficient))
    .add (by decide)

def Transform.unitScale {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (unit : Intˣ) : Transform A :=
  Transform.ofPrimitive
    (rowOperationMatrix (.smul row (unit : Int)))
    (rowUnitScaleInverseCertificate row unit)
    (applyRowOperation A (.smul row (unit : Int)))
    (rowOperationMatrix_mul A (.smul row (unit : Int)))
    .unitScale (by decide)

/-- Internal state adds paper-level events to the reversible transform. -/
structure State {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) where
  transform : Transform A
  events : List PrincipalEvent
  arithmeticEvents : List PrincipalArithmeticEvent
  validEvents : events.Forall (PrincipalEvent.Valid n)
  validArithmeticEvents :
    arithmeticEvents.Forall (PrincipalArithmeticEvent.Valid n)

def State.refl {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : State A :=
  { transform := Transform.refl A
    events := []
    arithmeticEvents := []
    validEvents := by simp
    validArithmeticEvents := by simp }

/-- The top-two-row Bezout primitive, reading its pair from any column. -/
def topBezoutAtColumn {m n : Nat}
    (A : _root_.Matrix (Fin (m + 2)) (Fin n) Int)
    (column : Fin n) : Transform A := by
  let forward := topBezoutMatrix (m := m) (A 0 column) (A 1 column)
  let certificate :=
    topBezoutMatrixInverseCertificate (m := m) (A 0 column) (A 1 column)
  exact
    { U := forward
      U_cert := certificate
      B := forward * A
      equation := rfl
      steps := [ReversibleRowStep.ofCertificate .bezoutPair certificate]
      accumulator_eq := by
        simp [RowTrace.accumulator, ReversibleRowStep.ofCertificate,
          forward, certificate]
      inverseAccumulator_eq := by
        simp [RowTrace.inverseAccumulator, ReversibleRowStep.ofCertificate,
          forward, certificate]
      primitive := by
        simp [RowTrace.IsPrimitive, RowTrace.operationCount,
          OperationCount.singleton, OperationCount.add,
          ReversibleRowStep.ofCertificate] }

/-- Combine arbitrary rows `pivot < target`, restoring their positions. -/
def pairBezoutAt {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : Transform A) : Transform A :=
  let forward := boundedPairBezoutMatrix pivot target
    (state.B pivot pivot) (state.B target pivot)
  let certificate := boundedPairBezoutMatrixInverseCertificate pivot target hlt.ne
    (state.B pivot pivot) (state.B target pivot)
  state.trans <| Transform.ofPrimitive
    forward certificate (forward * state.B) rfl .bezoutPair (by decide)

theorem pairBezoutAt_pivot_apply {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : Transform A) (column : Fin n) :
    (pairBezoutAt pivot target hlt state).B pivot column =
      boundedBezoutReductionMatrix (state.B pivot pivot) (state.B target pivot) 0 0 *
          state.B pivot column +
        boundedBezoutReductionMatrix (state.B pivot pivot) (state.B target pivot) 0 1 *
          state.B target column := by
  exact twoRowLiftMatrix_mul_apply_pivot pivot target hlt.ne
    (boundedBezoutReductionMatrix (state.B pivot pivot) (state.B target pivot))
    state.B column

theorem pairBezoutAt_target_apply {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : Transform A) (column : Fin n) :
    (pairBezoutAt pivot target hlt state).B target column =
      boundedBezoutReductionMatrix (state.B pivot pivot) (state.B target pivot) 1 0 *
          state.B pivot column +
        boundedBezoutReductionMatrix (state.B pivot pivot) (state.B target pivot) 1 1 *
          state.B target column := by
  exact twoRowLiftMatrix_mul_apply_target pivot target
    (boundedBezoutReductionMatrix (state.B pivot pivot) (state.B target pivot))
    state.B column

theorem pairBezoutAt_other_apply {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target row : Fin n) (hlt : pivot < target)
    (hp : row ≠ pivot) (ht : row ≠ target)
    (state : Transform A) (column : Fin n) :
    (pairBezoutAt pivot target hlt state).B row column = state.B row column := by
  exact twoRowLiftMatrix_mul_apply_other pivot target row hp ht
    (boundedBezoutReductionMatrix (state.B pivot pivot) (state.B target pivot))
    state.B column

theorem pairBezoutAt_pivot_pivot {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : Transform A) :
    (pairBezoutAt pivot target hlt state).B pivot pivot =
      (boundedIntXGCD
        (state.B pivot pivot) (state.B target pivot)).gcd := by
  rw [pairBezoutAt_pivot_apply]
  have entry := congrFun
    (boundedBezoutReductionMatrix_mulVec
      (state.B pivot pivot) (state.B target pivot)) 0
  simpa [_root_.Matrix.mulVec, dotProduct,
    NormalForms.Matrix.Constructive.sum_univ_two] using entry

theorem pairBezoutAt_target_pivot {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : Transform A) :
    (pairBezoutAt pivot target hlt state).B target pivot = 0 := by
  rw [pairBezoutAt_target_apply]
  have entry := congrFun
    (boundedBezoutReductionMatrix_mulVec
      (state.B pivot pivot) (state.B target pivot)) 1
  simpa [_root_.Matrix.mulVec, dotProduct,
    NormalForms.Matrix.Constructive.sum_univ_two] using entry

theorem pairBezoutAt_pivot_normalized {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : Transform A) :
    (pairBezoutAt pivot target hlt state).B pivot pivot =
      normalize ((pairBezoutAt pivot target hlt state).B pivot pivot) := by
  rw [pairBezoutAt_pivot_pivot]
  exact boundedIntXGCD_gcd_normalized _ _

def State.gcdEliminate {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : State A) : State A :=
  { transform := pairBezoutAt pivot target hlt state.transform
    events := state.events ++ [.gcdEliminate pivot.val target.val]
    arithmeticEvents := state.arithmeticEvents ++
      [.xgcd pivot.val target.val
        (state.transform.B pivot pivot) (state.transform.B target pivot)]
    validEvents := by
      simp [state.validEvents, PrincipalEvent.Valid, hlt, target.isLt]
    validArithmeticEvents := by
      simp [state.validArithmeticEvents, PrincipalArithmeticEvent.Valid,
        hlt, target.isLt] }

def State.reduceAbove {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination)
    (state : State A) : State A :=
  let coefficient :=
    -(ComputableEuclideanOps.quot
      (state.transform.B source destination)
      (state.transform.B destination destination))
  { transform := state.transform.trans <|
      Transform.add state.transform.B destination source
        coefficient (by omega)
    events := state.events ++ [.reduceAbove source.val destination.val]
    arithmeticEvents := state.arithmeticEvents ++
      [.divMod source.val destination.val
        (state.transform.B source destination)
        (state.transform.B destination destination)]
    validEvents := by
      simp [state.validEvents, PrincipalEvent.Valid, hlt, destination.isLt]
    validArithmeticEvents := by
      simp [state.validArithmeticEvents, PrincipalArithmeticEvent.Valid,
        hlt, destination.isLt] }

def State.normalize {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (row : Fin n) (state : State A) : State A :=
  { transform := state.transform.trans <|
      Transform.unitScale state.transform.B row <|
        ComputableEuclideanOps.normUnitUnit
          (state.transform.B row row)
    events := state.events ++ [.normalize row.val]
    arithmeticEvents := state.arithmeticEvents ++
      [.normalize row.val (state.transform.B row row)]
    validEvents := by
      simp [state.validEvents, PrincipalEvent.Valid, row.isLt]
    validArithmeticEvents := by
      simp [state.validArithmeticEvents, PrincipalArithmeticEvent.Valid, row.isLt] }

theorem State.gcdEliminate_pivot_apply {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : State A) (column : Fin n) :
    (state.gcdEliminate pivot target hlt).transform.B pivot column =
      boundedBezoutReductionMatrix
          (state.transform.B pivot pivot) (state.transform.B target pivot) 0 0 *
          state.transform.B pivot column +
        boundedBezoutReductionMatrix
          (state.transform.B pivot pivot) (state.transform.B target pivot) 0 1 *
          state.transform.B target column :=
  pairBezoutAt_pivot_apply pivot target hlt state.transform column

theorem State.gcdEliminate_target_apply {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : State A) (column : Fin n) :
    (state.gcdEliminate pivot target hlt).transform.B target column =
      boundedBezoutReductionMatrix
          (state.transform.B pivot pivot) (state.transform.B target pivot) 1 0 *
          state.transform.B pivot column +
        boundedBezoutReductionMatrix
          (state.transform.B pivot pivot) (state.transform.B target pivot) 1 1 *
          state.transform.B target column :=
  pairBezoutAt_target_apply pivot target hlt state.transform column

theorem State.gcdEliminate_other_apply {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target row : Fin n) (hlt : pivot < target)
    (hp : row ≠ pivot) (ht : row ≠ target)
    (state : State A) (column : Fin n) :
    (state.gcdEliminate pivot target hlt).transform.B row column =
      state.transform.B row column :=
  pairBezoutAt_other_apply pivot target row hlt hp ht state.transform column

theorem State.gcdEliminate_target_pivot {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : State A) :
    (state.gcdEliminate pivot target hlt).transform.B target pivot = 0 :=
  pairBezoutAt_target_pivot pivot target hlt state.transform

theorem State.gcdEliminate_pivot_normalized {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : State A) :
    (state.gcdEliminate pivot target hlt).transform.B pivot pivot =
      _root_.normalize
        ((state.gcdEliminate pivot target hlt).transform.B pivot pivot) :=
  pairBezoutAt_pivot_normalized pivot target hlt state.transform

theorem State.reduceAbove_source_apply {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination)
    (state : State A) (column : Fin n) :
    (state.reduceAbove source destination hlt).transform.B source column =
      state.transform.B source column -
        ComputableEuclideanOps.quot
            (state.transform.B source destination)
            (state.transform.B destination destination) *
          state.transform.B destination column := by
  simp [State.reduceAbove, Transform.trans, Transform.add,
    Transform.ofPrimitive, applyRowOperation, sub_eq_add_neg]

theorem State.reduceAbove_other_apply {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination row : Fin n) (hlt : source < destination)
    (hr : row ≠ source) (state : State A) (column : Fin n) :
    (state.reduceAbove source destination hlt).transform.B row column =
      state.transform.B row column := by
  simp [State.reduceAbove, Transform.trans, Transform.add,
    Transform.ofPrimitive, applyRowOperation, hr]

theorem State.reduceAbove_reduced {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination)
    (state : State A) :
    (state.reduceAbove source destination hlt).transform.B source destination =
      (state.reduceAbove source destination hlt).transform.B source destination %
        (state.reduceAbove source destination hlt).transform.B
          destination destination := by
  rw [State.reduceAbove_source_apply,
    State.reduceAbove_other_apply source destination destination hlt hlt.ne']
  simp only [ComputableEuclideanOps.quot_eq]
  have division := EuclideanDomain.mod_add_div'
    (state.transform.B source destination)
    (state.transform.B destination destination)
  have remainder :
      state.transform.B source destination -
          state.transform.B source destination /
              state.transform.B destination destination *
            state.transform.B destination destination =
        state.transform.B source destination %
          state.transform.B destination destination := by
    calc
      state.transform.B source destination -
            state.transform.B source destination /
                state.transform.B destination destination *
              state.transform.B destination destination =
          (state.transform.B source destination %
              state.transform.B destination destination +
            state.transform.B source destination /
                state.transform.B destination destination *
              state.transform.B destination destination) -
            state.transform.B source destination /
                state.transform.B destination destination *
              state.transform.B destination destination := by
        rw [division]
      _ = state.transform.B source destination %
          state.transform.B destination destination := by ring
  rw [remainder, CanonicalMod.mod_mod]

theorem State.normalize_row_apply {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (row : Fin n) (state : State A) (column : Fin n) :
    (state.normalize row).transform.B row column =
      (ComputableEuclideanOps.normUnitUnit
          (state.transform.B row row) : Int) *
        state.transform.B row column := by
  simp [State.normalize, Transform.trans, Transform.unitScale,
    Transform.ofPrimitive, applyRowOperation]

theorem State.normalize_other_apply {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target row : Fin n) (hr : row ≠ target)
    (state : State A) (column : Fin n) :
    (state.normalize target).transform.B row column =
      state.transform.B row column := by
  simp [State.normalize, Transform.trans, Transform.unitScale,
    Transform.ofPrimitive, applyRowOperation, hr]

theorem State.normalize_diagonal {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (row : Fin n) (state : State A) :
    (state.normalize row).transform.B row row =
      _root_.normalize ((state.normalize row).transform.B row row) := by
  rw [State.normalize_row_apply]
  have value :
      (ComputableEuclideanOps.normUnitUnit
          (state.transform.B row row) : Int) *
          state.transform.B row row =
        _root_.normalize (state.transform.B row row) := by
    rw [mul_comm]
    calc
      state.transform.B row row *
            (ComputableEuclideanOps.normUnitUnit
              (state.transform.B row row) : Int) =
          ComputableEuclideanOps.normalize (state.transform.B row row) :=
        (ComputableEuclideanOps.normalize_eq_mul_normUnitUnit (R := Int)
          (state.transform.B row row)).symm
      _ = _root_.normalize (state.transform.B row row) :=
        ComputableEuclideanOps.normalize_eq_mathlib _
  rw [value, ComputableEuclideanOps.normalize_idem_constructive]

def reduceAboveLoop {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → k ≤ destination.val → State A → State A
  | 0, _, state => state
  | k + 1, hk, state =>
      let previous := reduceAboveLoop destination k (by omega) state
      let source : Fin n := ⟨k, by omega⟩
      previous.reduceAbove source destination (by
        change k < destination.val
        omega)

def eliminateStageLoop {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (k : Nat) → k ≤ target.val → State A → State A
  | 0, _, state => state
  | k + 1, hk, state =>
      let previous := eliminateStageLoop target k (by omega) state
      let pivot : Fin n := ⟨k, by omega⟩
      let eliminated := previous.gcdEliminate pivot target (by
        change k < target.val
        omega)
      reduceAboveLoop pivot pivot.val le_rfl eliminated

def extendStage {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (state : State A) : State A :=
  let eliminated := eliminateStageLoop target target.val le_rfl state
  let normalized := eliminated.normalize target
  reduceAboveLoop target target.val le_rfl normalized

def stageLoop {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} :
    (k : Nat) → k ≤ n → State A → State A
  | 0, _, state => state
  | k + 1, hk, state =>
      let previous := stageLoop k (by omega) state
      let target : Fin n := ⟨k, by omega⟩
      extendStage target previous

def compute {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : State A :=
  stageLoop n le_rfl (State.refl A)

/--
Expose only the primitive control schedule and scalar operands.  Matrix values
remain the responsibility of the value-producing execution layer.
-/
public def _root_.NormalForms.Research.KannanBachem.Hermite.principalSchedule
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int) :
    PrincipalSchedule n :=
  let final := compute A
  { steps := final.transform.steps
    arithmeticEvents := final.arithmeticEvents
    validArithmeticEvents := final.validArithmeticEvents }

/-- Execute the transposed principal-minor schedule on a square matrix. -/
public def _root_.NormalForms.Research.KannanBachem.Hermite.principalRun
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int) : PrincipalRun A := by
  let final := compute A
  exact
    { matrix := final.transform.B
      steps := final.transform.steps
      events := final.events
      arithmeticEvents := final.arithmeticEvents
      equation := by
        rw [final.transform.accumulator_eq]
        exact final.transform.equation
      primitive := final.transform.primitive
      validEvents := final.validEvents
      validArithmeticEvents := final.validArithmeticEvents }

/-- Replay of the primitive trace reaches the recorded candidate matrix. -/
public theorem _root_.NormalForms.Research.KannanBachem.Hermite.principalRun_replay
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (principalRun A).steps.replay A = (principalRun A).matrix := by
  rw [RowTrace.replay_eq_accumulator_mul]
  exact (principalRun A).equation

/-- The directly accumulated inverse takes the candidate back to the input. -/
public theorem _root_.NormalForms.Research.KannanBachem.Hermite.principalRun_inverse_equation
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (principalRun A).steps.inverseAccumulator * (principalRun A).matrix = A := by
  rw [← (principalRun A).equation, ← Matrix.mul_assoc,
    RowTrace.inverse_mul_accumulator]
  simp

/-- Both inverse identities are inherited constructively from the trace. -/
public theorem _root_.NormalForms.Research.KannanBachem.Hermite.principalRun_inverse_identities
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (principalRun A).steps.inverseAccumulator *
          (principalRun A).steps.accumulator = 1 ∧
      (principalRun A).steps.accumulator *
          (principalRun A).steps.inverseAccumulator = 1 :=
  ⟨RowTrace.inverse_mul_accumulator _, RowTrace.accumulator_mul_inverse _⟩

end Principal

namespace RowTrace

/-- Input matrix followed by the matrix after every represented row step. -/
@[expose] public def intermediates {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    RowTrace Int m → List (_root_.Matrix (Fin m) (Fin n) Int)
  | [] => [A]
  | step :: tail => A :: intermediates (step.forward * A) tail

@[simp] public theorem intermediates_length {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (steps : RowTrace Int m) :
    (steps.intermediates A).length = steps.length + 1 := by
  induction steps generalizing A with
  | nil => rfl
  | cons step tail ih =>
      simp [intermediates, ih]

@[simp] public theorem intermediates_head? {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (steps : RowTrace Int m) :
    (steps.intermediates A).head? = some A := by
  cases steps <;> rfl

end RowTrace

end NormalForms.Research.KannanBachem.Hermite
