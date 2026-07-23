/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Matrix.Hermite.Bezout
public import NormalForms.Research.KannanBachem.Execution.Dense
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal
import all NormalForms.Research.KannanBachem.Smith.BoundedColumn

/-! # Shared Value-Producing Principal Transition -/

public section

namespace NormalForms.Research.KannanBachem

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite
open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Hermite.Principal
open NormalForms.Research.KannanBachem.Smith

/-- The three matrices updated by every principal scalar transition. -/
public structure PrincipalTransitionState (n : Nat) where
  B : Matrix (Fin n) (Fin n) Int
  U : Matrix (Fin n) (Fin n) Int
  Uinv : Matrix (Fin n) (Fin n) Int

namespace Internal

/-- Sealed scalar owner for one exact value-producing transition. -/
public inductive PrincipalTransitionData (n : Nat) where
  | bezout
      (before : PrincipalTransitionState n)
      (pivot target : Fin n) (hlt : pivot < target)
      (run : WithCost BoundedBezoutBlock)
      (run_eq : run = boundedBezoutBlockWithCost
        (SignMagnitude.ofInt (before.B pivot pivot))
        (SignMagnitude.ofInt (before.B target pivot)))
  | reduceAbove
      (before : PrincipalTransitionState n)
      (source destination : Fin n) (hlt : source < destination)
      (run : WithCost DivModResult)
      (run_eq : run = divModWithCost
        (SignMagnitude.ofInt (before.B source destination))
        (SignMagnitude.ofInt (before.B destination destination)))
  | normalize
      (before : PrincipalTransitionState n)
      (row : Fin n)
      (run : WithCost Intˣ)
      (run_eq : run =
        normalizationUnitWithCost (SignMagnitude.ofInt (before.B row row)))

end Internal

/--
One sealed scalar run together with the three dense products it determines.
The only public constructors below store an exact named primitive run.
-/
public structure PrincipalTransitionExecution (n : Nat) where
  mk ::
  data : Internal.PrincipalTransitionData n

namespace PrincipalTransitionExecution

@[expose] public def before {n : Nat} :
    PrincipalTransitionExecution n → PrincipalTransitionState n
  | ⟨.bezout before ..⟩ => before
  | ⟨.reduceAbove before ..⟩ => before
  | ⟨.normalize before ..⟩ => before

@[expose] public def event {n : Nat} :
    PrincipalTransitionExecution n → PrincipalArithmeticEvent
  | ⟨.bezout before pivot target ..⟩ =>
      .xgcd pivot target
        (before.B pivot pivot) (before.B target pivot)
  | ⟨.reduceAbove before source destination ..⟩ =>
      .divMod source destination
        (before.B source destination) (before.B destination destination)
  | ⟨.normalize before row ..⟩ =>
      .normalize row (before.B row row)

@[expose] public def step {n : Nat} :
    PrincipalTransitionExecution n → ReversibleRowStep Int n
  | ⟨.bezout _ pivot target hlt run _⟩ => by
      let forward := twoRowLiftMatrix pivot target run.value.forward
      let certificate : MatrixInverseCertificate forward :=
        { inverse := twoRowLiftMatrix pivot target run.value.inverse
          left_inv := by
            change twoRowLiftMatrix pivot target run.value.inverse *
                twoRowLiftMatrix pivot target run.value.forward = 1
            rw [twoRowLiftMatrix_mul pivot target hlt.ne,
              run.value.left_inv, twoRowLiftMatrix_one pivot target hlt.ne]
          right_inv := by
            change twoRowLiftMatrix pivot target run.value.forward *
                twoRowLiftMatrix pivot target run.value.inverse = 1
            rw [twoRowLiftMatrix_mul pivot target hlt.ne,
              run.value.right_inv, twoRowLiftMatrix_one pivot target hlt.ne] }
      exact ReversibleRowStep.ofCertificate .bezoutPair certificate
  | ⟨.reduceAbove _ source destination hlt run _⟩ =>
      ReversibleRowStep.add destination source
        (-run.value.quotient.value) hlt.ne'
  | ⟨.normalize _ row run _⟩ =>
      ReversibleRowStep.unitScale row run.value

@[expose] public def scalarCharge {n : Nat} :
    (transition : PrincipalTransitionExecution n) →
      KannanBachemArithmeticCharge
  | ⟨.bezout before pivot target hlt run run_eq⟩ =>
      let location := ArithmeticChargeLocation.ofIndices .bezoutBlock n
        [pivot, target] (by
          intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact pivot.isLt
          · exact target.isLt)
      KannanBachemArithmeticCharge.boundedBezoutBlockOfRun location
        (SignMagnitude.ofInt (before.B pivot pivot))
        (SignMagnitude.ofInt (before.B target pivot)) run run_eq
  | ⟨.reduceAbove before source destination hlt run run_eq⟩ =>
      let location := ArithmeticChargeLocation.ofIndices .hnfReduceAbove n
        [source, destination] (by
          intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact source.isLt
          · exact destination.isLt)
      KannanBachemArithmeticCharge.divModOfRun location .hnfReduceAbove
        (SignMagnitude.ofInt (before.B source destination))
        (SignMagnitude.ofInt (before.B destination destination))
        run run_eq trivial
  | ⟨.normalize before row run run_eq⟩ =>
      let location := ArithmeticChargeLocation.ofIndices .scalar n [row] (by
        intro index member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        subst index
        exact row.isLt)
      KannanBachemArithmeticCharge.normalizationOfRun location
        (SignMagnitude.ofInt (before.B row row)) run run_eq

public theorem scalarCharge_wellFormed {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    transition.scalarCharge.WellFormed := by
  cases transition with
  | mk data =>
      cases data with
      | bezout before pivot target hlt run run_eq =>
          simpa only [scalarCharge] using
            KannanBachemArithmeticCharge.boundedBezoutBlockOfRun_wellFormed
              _ _ _ run run_eq
      | reduceAbove before source destination hlt run run_eq =>
          simpa only [scalarCharge] using
            KannanBachemArithmeticCharge.divModOfRun_wellFormed
              (ArithmeticChargeLocation.ofIndices .hnfReduceAbove n
                [source, destination] (by
                  intro index member
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                  rcases member with rfl | rfl
                  · exact source.isLt
                  · exact destination.isLt))
              .hnfReduceAbove _ _ run run_eq trivial
      | normalize before row run run_eq =>
          simpa only [scalarCharge] using
            KannanBachemArithmeticCharge.normalizationOfRun_wellFormed
              _ _ run run_eq

@[expose] public def matrixRun {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    MatrixProductExecution (n := n) :=
  matrixProductExecution transition.step.forward transition.before.B

@[expose] public def forwardRun {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    MatrixProductExecution (n := n) :=
  matrixProductExecution transition.step.forward transition.before.U

@[expose] public def inverseRun {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    MatrixProductExecution (n := n) :=
  matrixProductExecution transition.before.Uinv transition.step.backward

@[expose] public def after {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    PrincipalTransitionState n :=
  { B := transition.matrixRun.value
    U := transition.forwardRun.value
    Uinv := transition.inverseRun.value }

@[simp] public theorem after_B {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    transition.after.B =
      transition.step.forward * transition.before.B :=
  by
    simpa only [after, matrixRun] using
      matrixProductExecution_value transition.step.forward transition.before.B

@[simp] public theorem after_U {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    transition.after.U =
      transition.step.forward * transition.before.U :=
  by
    simpa only [after, forwardRun] using
      matrixProductExecution_value transition.step.forward transition.before.U

@[simp] public theorem after_Uinv {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    transition.after.Uinv =
      transition.before.Uinv * transition.step.backward :=
  by
    simpa only [after, inverseRun] using
      matrixProductExecution_value transition.before.Uinv transition.step.backward

/-- Exact charge bundle owned by this transition. -/
@[expose] public def charges {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    List KannanBachemArithmeticCharge :=
  [transition.scalarCharge] ++
    (transition.matrixRun.charges ++
      (transition.forwardRun.charges ++ transition.inverseRun.charges))

public theorem charges_wellFormed {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    ArithmeticChargeListWellFormed transition.charges := by
  apply (List.forall_iff_forall_mem.mpr fun charge member => ?_)
  simp only [charges, List.mem_append, List.mem_singleton] at member
  rcases member with rfl | member
  · exact transition.scalarCharge_wellFormed
  · rcases member with member | member
    · exact List.forall_iff_forall_mem.mp
        transition.matrixRun.trace_wellFormed _ member
    · rcases member with member | member
      · exact List.forall_iff_forall_mem.mp
          transition.forwardRun.trace_wellFormed _ member
      · exact List.forall_iff_forall_mem.mp
          transition.inverseRun.trace_wellFormed _ member

/--
Forward, inverse, and the block leaf of a Bézout transition all reference its
single stored block run.
-/
@[expose] public def BezoutRunShared {n : Nat}
    (transition : PrincipalTransitionExecution n) : Prop :=
  match transition.data with
  | .bezout before pivot target hlt run run_eq =>
      transition.step.forward =
          twoRowLiftMatrix pivot target run.value.forward ∧
        transition.step.backward =
          twoRowLiftMatrix pivot target run.value.inverse ∧
        transition.scalarCharge =
          KannanBachemArithmeticCharge.boundedBezoutBlockOfRun
            (ArithmeticChargeLocation.ofIndices .bezoutBlock n
              [pivot, target] (by
                intro index member
                simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                rcases member with rfl | rfl
                · exact pivot.isLt
                · exact target.isLt))
            (SignMagnitude.ofInt (before.B pivot pivot))
            (SignMagnitude.ofInt (before.B target pivot)) run run_eq
  | _ => True

public theorem bezoutRunShared {n : Nat}
    (transition : PrincipalTransitionExecution n) :
    transition.BezoutRunShared := by
  cases transition with
  | mk data =>
      cases data <;>
        simp [BezoutRunShared, step, scalarCharge,
          ReversibleRowStep.ofCertificate]

end PrincipalTransitionExecution

@[expose] public def bezoutTransition {n : Nat}
    (before : PrincipalTransitionState n)
    (pivot target : Fin n) (hlt : pivot < target) :
    PrincipalTransitionExecution n :=
  let run := boundedBezoutBlockWithCost
    (SignMagnitude.ofInt (before.B pivot pivot))
    (SignMagnitude.ofInt (before.B target pivot))
  ⟨.bezout before pivot target hlt run rfl⟩

@[expose] public def reduceAboveTransition {n : Nat}
    (before : PrincipalTransitionState n)
    (source destination : Fin n) (hlt : source < destination) :
    PrincipalTransitionExecution n :=
  let run := divModWithCost
    (SignMagnitude.ofInt (before.B source destination))
    (SignMagnitude.ofInt (before.B destination destination))
  ⟨.reduceAbove before source destination hlt run rfl⟩

@[expose] public def normalizationTransition {n : Nat}
    (before : PrincipalTransitionState n) (row : Fin n) :
    PrincipalTransitionExecution n :=
  let run := normalizationUnitWithCost
    (SignMagnitude.ofInt (before.B row row))
  ⟨.normalize before row run rfl⟩

private theorem boundedBezoutBlockWithCost_forward_eq
    (left right : Int) :
    (boundedBezoutBlockWithCost
      (SignMagnitude.ofInt left)
      (SignMagnitude.ofInt right)).value.forward =
        boundedBezoutReductionMatrix left right := by
  rw [boundedBezoutBlockWithCost]
  split
  next zero =>
    have gcdZero :
        (boundedXGCDWithCost
          (SignMagnitude.ofInt left)
          (SignMagnitude.ofInt right)).value.gcd.value = 0 := by
      simpa using zero
    simp [boundedBezoutReductionMatrix, boundedIntXGCD, gcdZero]
  next nonzero =>
    have gcdNonzero :
        (boundedXGCDWithCost
          (SignMagnitude.ofInt left)
          (SignMagnitude.ofInt right)).value.gcd.value ≠ 0 := by
      simpa using nonzero
    simp [boundedBezoutReductionMatrix, boundedIntXGCD, gcdNonzero,
      exactDivWithCost, quotientWithCost]

private theorem boundedBezoutBlockWithCost_inverse_eq
    (left right : Int) :
    (boundedBezoutBlockWithCost
      (SignMagnitude.ofInt left)
      (SignMagnitude.ofInt right)).value.inverse =
        boundedBezoutReductionInverseMatrix left right := by
  rw [boundedBezoutBlockWithCost]
  split
  next zero =>
    have gcdZero :
        (boundedXGCDWithCost
          (SignMagnitude.ofInt left)
          (SignMagnitude.ofInt right)).value.gcd.value = 0 := by
      simpa using zero
    simp [boundedBezoutReductionInverseMatrix, boundedIntXGCD, gcdZero]
  next nonzero =>
    have gcdNonzero :
        (boundedXGCDWithCost
          (SignMagnitude.ofInt left)
          (SignMagnitude.ofInt right)).value.gcd.value ≠ 0 := by
      simpa using nonzero
    simp [boundedBezoutReductionInverseMatrix, boundedIntXGCD, gcdNonzero,
      exactDivWithCost, quotientWithCost]

private theorem bezoutTransition_step_eq {n : Nat}
    (before : PrincipalTransitionState n)
    (pivot target : Fin n) (hlt : pivot < target) :
    (bezoutTransition before pivot target hlt).step =
      ReversibleRowStep.ofCertificate .bezoutPair
        (boundedPairBezoutMatrixInverseCertificate pivot target hlt.ne
          (before.B pivot pivot) (before.B target pivot)) := by
  simp [bezoutTransition, PrincipalTransitionExecution.step,
    boundedPairBezoutMatrix, boundedPairBezoutMatrixInverseCertificate,
    boundedBezoutBlockWithCost_forward_eq,
    boundedBezoutBlockWithCost_inverse_eq,
    ReversibleRowStep.ofCertificate]

private theorem reduceAboveTransition_step_eq {n : Nat}
    (before : PrincipalTransitionState n)
    (source destination : Fin n) (hlt : source < destination) :
    (reduceAboveTransition before source destination hlt).step =
      ReversibleRowStep.ofCertificate .add
        (rowAddInverseCertificate destination source
          (-(ComputableEuclideanOps.quot
            (before.B source destination)
            (before.B destination destination))) hlt.ne') := by
  simp [reduceAboveTransition, PrincipalTransitionExecution.step,
    ComputableEuclideanOps.quot_eq, ReversibleRowStep.add,
    ReversibleRowStep.ofCertificate, rowAddInverseCertificate]

private theorem normalizationTransition_step_eq {n : Nat}
    (before : PrincipalTransitionState n) (row : Fin n) :
    (normalizationTransition before row).step =
      ReversibleRowStep.ofCertificate .unitScale
        (rowUnitScaleInverseCertificate row
          (ComputableEuclideanOps.normUnitUnit (before.B row row))) := by
  simp [normalizationTransition, PrincipalTransitionExecution.step,
    normalizationUnitWithCost, ReversibleRowStep.unitScale,
    ReversibleRowStep.ofCertificate, rowUnitScaleInverseCertificate]

/--
Coverage can only start at the exact initial matrices and extend by one sealed
transition whose input is the preceding state.
-/
public inductive PrincipalExecutionCoverage {n : Nat}
    (initial : PrincipalTransitionState n) :
    PrincipalTransitionState n →
      List (PrincipalTransitionExecution n) →
        List KannanBachemArithmeticCharge → Prop
  | initial : PrincipalExecutionCoverage initial initial [] []
  | transition
      {current : PrincipalTransitionState n}
      {transitions : List (PrincipalTransitionExecution n)}
      {charges : List KannanBachemArithmeticCharge}
      (_coverage :
        PrincipalExecutionCoverage initial current transitions charges)
      (next : PrincipalTransitionExecution n)
      (input_exact : next.before = current) :
      PrincipalExecutionCoverage initial next.after
        (transitions ++ [next]) (charges ++ next.charges)

namespace PrincipalExecutionCoverage

public theorem charges_eq_flatten {n : Nat}
    {initial final : PrincipalTransitionState n}
    {transitions : List (PrincipalTransitionExecution n)}
    {charges : List KannanBachemArithmeticCharge}
    (coverage :
      PrincipalExecutionCoverage initial final transitions charges) :
    charges = transitions.flatMap PrincipalTransitionExecution.charges := by
  induction coverage with
  | initial => rfl
  | transition coverage next input_exact ih =>
      rw [ih, List.flatMap_append]
      simp

public theorem transitions_shared {n : Nat}
    {initial final : PrincipalTransitionState n}
    {transitions : List (PrincipalTransitionExecution n)}
    {charges : List KannanBachemArithmeticCharge}
    (_coverage :
      PrincipalExecutionCoverage initial final transitions charges) :
    ∀ transition ∈ transitions, transition.BezoutRunShared := by
  intro transition member
  exact transition.bezoutRunShared

end PrincipalExecutionCoverage

/-- Accumulated exact transition execution from one fixed input matrix. -/
public structure PrincipalTransitionSequence {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) where
  state : PrincipalTransitionState n
  steps : RowTrace Int n
  events : List PrincipalArithmeticEvent
  transitions : List (PrincipalTransitionExecution n)
  charges : List KannanBachemArithmeticCharge
  steps_eq_transitions :
    steps = transitions.map PrincipalTransitionExecution.step
  events_eq_transitions :
    events = transitions.map PrincipalTransitionExecution.event
  transition_prefix :
    ∀ transition ∈ transitions,
      ∃ before after : RowTrace Int n,
        steps = before ++ transition.step :: after ∧
          transition.before.B = before.replay A ∧
          transition.before.U = before.accumulator ∧
          transition.before.Uinv = before.inverseAccumulator
  B_eq_replay : state.B = steps.replay A
  U_eq_accumulator : state.U = steps.accumulator
  Uinv_eq_inverseAccumulator : state.Uinv = steps.inverseAccumulator
  equation : state.U * A = state.B
  inverse_identities :
    state.Uinv * state.U = 1 ∧ state.U * state.Uinv = 1
  trace_wellFormed : ArithmeticChargeListWellFormed charges
  coverage :
    PrincipalExecutionCoverage { B := A, U := 1, Uinv := 1 }
      state transitions charges

@[expose] public def PrincipalTransitionSequence.initial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    PrincipalTransitionSequence A :=
  { state := { B := A, U := 1, Uinv := 1 }
    steps := []
    events := []
    transitions := []
    charges := []
    steps_eq_transitions := rfl
    events_eq_transitions := rfl
    transition_prefix := by simp
    B_eq_replay := rfl
    U_eq_accumulator := rfl
    Uinv_eq_inverseAccumulator := rfl
    equation := NormalForms.Matrix.Constructive.one_mul A
    inverse_identities := by constructor <;> simp
    trace_wellFormed := by simp [ArithmeticChargeListWellFormed]
    coverage := .initial }

@[expose] public def PrincipalTransitionSequence.apply {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (sequence : PrincipalTransitionSequence A)
    (transition : PrincipalTransitionExecution n)
    (input_exact : transition.before = sequence.state) :
    PrincipalTransitionSequence A := by
  exact
    { state := transition.after
      steps := sequence.steps ++ [transition.step]
      events := sequence.events ++ [transition.event]
      transitions := sequence.transitions ++ [transition]
      charges := sequence.charges ++ transition.charges
      steps_eq_transitions := by
        rw [List.map_append, sequence.steps_eq_transitions]
        rfl
      events_eq_transitions := by
        rw [List.map_append, sequence.events_eq_transitions]
        rfl
      transition_prefix := by
        intro candidate member
        rw [List.mem_append, List.mem_singleton] at member
        rcases member with member | rfl
        · obtain ⟨before, after, steps, matrix, forward, inverse⟩ :=
            sequence.transition_prefix candidate member
          refine ⟨before, after ++ [transition.step], ?_, matrix,
            forward, inverse⟩
          rw [steps]
          simp [List.append_assoc]
        · refine ⟨sequence.steps, [], ?_, ?_, ?_, ?_⟩
          · simp
          · rw [input_exact, sequence.B_eq_replay]
          · rw [input_exact, sequence.U_eq_accumulator]
          · rw [input_exact, sequence.Uinv_eq_inverseAccumulator]
      B_eq_replay := by
        rw [transition.after_B, RowTrace.replay_append]
        simp only [RowTrace.replay, List.foldl_cons, List.foldl_nil]
        rw [input_exact, sequence.B_eq_replay]
        rfl
      U_eq_accumulator := by
        rw [transition.after_U, RowTrace.accumulator_append]
        simp only [RowTrace.accumulator]
        rw [NormalForms.Matrix.Constructive.one_mul]
        rw [input_exact, sequence.U_eq_accumulator]
      Uinv_eq_inverseAccumulator := by
        rw [transition.after_Uinv, RowTrace.inverseAccumulator_append]
        simp only [RowTrace.inverseAccumulator, Matrix.mul_one]
        rw [input_exact, sequence.Uinv_eq_inverseAccumulator]
      equation := by
        rw [transition.after_U, transition.after_B,
          input_exact, Matrix.mul_assoc, sequence.equation]
      inverse_identities := by
        constructor
        · rw [transition.after_Uinv, transition.after_U]
          rw [input_exact]
          calc
            (sequence.state.Uinv * transition.step.backward) *
                  (transition.step.forward * sequence.state.U) =
                sequence.state.Uinv *
                  (transition.step.backward * transition.step.forward) *
                    sequence.state.U := by simp only [Matrix.mul_assoc]
            _ = sequence.state.Uinv * sequence.state.U := by
              rw [transition.step.backward_forward, Matrix.mul_one]
            _ = 1 := sequence.inverse_identities.1
        · rw [transition.after_U, transition.after_Uinv]
          rw [input_exact]
          calc
            (transition.step.forward * sequence.state.U) *
                  (sequence.state.Uinv * transition.step.backward) =
                transition.step.forward *
                  (sequence.state.U * sequence.state.Uinv) *
                    transition.step.backward := by simp only [Matrix.mul_assoc]
            _ = transition.step.forward * transition.step.backward := by
              rw [sequence.inverse_identities.2, Matrix.mul_one]
            _ = 1 := transition.step.forward_backward
      trace_wellFormed :=
        sequence.trace_wellFormed.append transition.charges_wellFormed
      coverage :=
        .transition sequence.coverage transition input_exact }

namespace PrincipalTransitionSequence

def reduceAboveLoop {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → k ≤ destination.val →
      PrincipalTransitionSequence A → PrincipalTransitionSequence A
  | 0, _, sequence => sequence
  | k + 1, hk, sequence =>
      let previous := reduceAboveLoop destination k (by omega) sequence
      let source : Fin n := ⟨k, by omega⟩
      previous.apply
        (reduceAboveTransition previous.state source destination (by
          change k < destination.val
          omega))
        rfl

def eliminateStageLoop {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (k : Nat) → k ≤ target.val →
      PrincipalTransitionSequence A → PrincipalTransitionSequence A
  | 0, _, sequence => sequence
  | k + 1, hk, sequence =>
      let previous := eliminateStageLoop target k (by omega) sequence
      let pivot : Fin n := ⟨k, by omega⟩
      let eliminated := previous.apply
        (bezoutTransition previous.state pivot target (by
          change k < target.val
          omega))
        rfl
      reduceAboveLoop pivot pivot.val le_rfl eliminated

def extendStage {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (target : Fin n)
    (sequence : PrincipalTransitionSequence A) :
    PrincipalTransitionSequence A :=
  let eliminated :=
    eliminateStageLoop target target.val le_rfl sequence
  let normalized := eliminated.apply
    (normalizationTransition eliminated.state target) rfl
  reduceAboveLoop target target.val le_rfl normalized

def stageLoop {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} :
    (k : Nat) → k ≤ n →
      PrincipalTransitionSequence A → PrincipalTransitionSequence A
  | 0, _, sequence => sequence
  | k + 1, hk, sequence =>
      let previous := stageLoop k (by omega) sequence
      let target : Fin n := ⟨k, by omega⟩
      extendStage target previous

end PrincipalTransitionSequence

/-- Stateful production execution of the full principal stage loop. -/
@[expose] public def principalTransitionSequence {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    PrincipalTransitionSequence A :=
  PrincipalTransitionSequence.stageLoop n le_rfl
    (PrincipalTransitionSequence.initial A)

namespace PrincipalTransitionSequence

def boundedColumnLoop {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → k ≤ n →
      PrincipalTransitionSequence A → PrincipalTransitionSequence A
  | 0, _, sequence => sequence
  | k + 1, hk, sequence =>
      let previous := boundedColumnLoop k (by omega) sequence
      let target : Fin (n + 1) := ⟨k + 1, by omega⟩
      previous.apply
        (bezoutTransition previous.state 0 target (by
          change 0 < k + 1
          omega))
        rfl

end PrincipalTransitionSequence

/-- Stateful production execution of the bounded first-column loop. -/
@[expose] public def boundedColumnTransitionSequence {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    PrincipalTransitionSequence A :=
  let reduced :=
    PrincipalTransitionSequence.boundedColumnLoop n le_rfl
      (PrincipalTransitionSequence.initial A)
  reduced.apply (normalizationTransition reduced.state 0) rfl

private structure PrincipalSequenceRefines {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (sequence : PrincipalTransitionSequence A)
    (state : Principal.State A) : Prop where
  state_B : sequence.state.B = state.transform.B
  steps : sequence.steps = state.transform.steps
  events : sequence.events = state.arithmeticEvents

private theorem principalSequenceRefines_initial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    PrincipalSequenceRefines
      (PrincipalTransitionSequence.initial A) (Principal.State.refl A) := by
  constructor <;> rfl

private theorem PrincipalSequenceRefines.gcdEliminate {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    {sequence : PrincipalTransitionSequence A}
    {state : Principal.State A}
    (refines : PrincipalSequenceRefines sequence state)
    (pivot target : Fin n) (hlt : pivot < target) :
    PrincipalSequenceRefines
      (sequence.apply (bezoutTransition sequence.state pivot target hlt) rfl)
      (state.gcdEliminate pivot target hlt) := by
  constructor
  · rw [PrincipalTransitionSequence.apply,
      PrincipalTransitionExecution.after_B, bezoutTransition_step_eq,
      refines.state_B]
    simp only [PrincipalTransitionExecution.before, bezoutTransition,
      ReversibleRowStep.ofCertificate, Principal.State.gcdEliminate,
      pairBezoutAt, Principal.Transform.trans,
      Principal.Transform.ofPrimitive]
    rw [refines.state_B]
  · change
      sequence.steps ++
          [(bezoutTransition sequence.state pivot target hlt).step] =
        state.transform.steps ++
          [ReversibleRowStep.ofCertificate .bezoutPair
            (boundedPairBezoutMatrixInverseCertificate
              pivot target hlt.ne
              (state.transform.B pivot pivot)
              (state.transform.B target pivot))]
    rw [refines.steps, bezoutTransition_step_eq, refines.state_B]
  · change
      sequence.events ++
          [.xgcd pivot.val target.val
            (sequence.state.B pivot pivot)
            (sequence.state.B target pivot)] =
        state.arithmeticEvents ++
          [.xgcd pivot.val target.val
            (state.transform.B pivot pivot)
            (state.transform.B target pivot)]
    rw [refines.events, refines.state_B]

private theorem PrincipalSequenceRefines.reduceAbove {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    {sequence : PrincipalTransitionSequence A}
    {state : Principal.State A}
    (refines : PrincipalSequenceRefines sequence state)
    (source destination : Fin n) (hlt : source < destination) :
    PrincipalSequenceRefines
      (sequence.apply
        (reduceAboveTransition sequence.state source destination hlt) rfl)
      (state.reduceAbove source destination hlt) := by
  constructor
  · rw [PrincipalTransitionSequence.apply,
      PrincipalTransitionExecution.after_B,
      reduceAboveTransition_step_eq, refines.state_B]
    simp only [PrincipalTransitionExecution.before, reduceAboveTransition,
      ReversibleRowStep.ofCertificate, Principal.State.reduceAbove,
      Principal.Transform.trans, Principal.Transform.add,
      Principal.Transform.ofPrimitive]
    rw [refines.state_B]
    exact rowOperationMatrix_mul _ _
  · change
      sequence.steps ++
          [(reduceAboveTransition
            sequence.state source destination hlt).step] =
        state.transform.steps ++
          [ReversibleRowStep.ofCertificate .add
            (rowAddInverseCertificate destination source
              (-(ComputableEuclideanOps.quot
                (state.transform.B source destination)
                (state.transform.B destination destination))) hlt.ne')]
    rw [refines.steps, reduceAboveTransition_step_eq, refines.state_B]
  · change
      sequence.events ++
          [.divMod source.val destination.val
            (sequence.state.B source destination)
            (sequence.state.B destination destination)] =
        state.arithmeticEvents ++
          [.divMod source.val destination.val
            (state.transform.B source destination)
            (state.transform.B destination destination)]
    rw [refines.events, refines.state_B]

private theorem PrincipalSequenceRefines.normalize {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    {sequence : PrincipalTransitionSequence A}
    {state : Principal.State A}
    (refines : PrincipalSequenceRefines sequence state)
    (row : Fin n) :
    PrincipalSequenceRefines
      (sequence.apply (normalizationTransition sequence.state row) rfl)
      (state.normalize row) := by
  constructor
  · rw [PrincipalTransitionSequence.apply,
      PrincipalTransitionExecution.after_B,
      normalizationTransition_step_eq, refines.state_B]
    simp only [PrincipalTransitionExecution.before, normalizationTransition,
      ReversibleRowStep.ofCertificate, Principal.State.normalize,
      Principal.Transform.trans, Principal.Transform.unitScale,
      Principal.Transform.ofPrimitive]
    rw [refines.state_B]
    exact rowOperationMatrix_mul _ _
  · change
      sequence.steps ++
          [(normalizationTransition sequence.state row).step] =
        state.transform.steps ++
          [ReversibleRowStep.ofCertificate .unitScale
            (rowUnitScaleInverseCertificate row
              (ComputableEuclideanOps.normUnitUnit
                (state.transform.B row row)))]
    rw [refines.steps, normalizationTransition_step_eq, refines.state_B]
  · change
      sequence.events ++
          [.normalize row.val (sequence.state.B row row)] =
        state.arithmeticEvents ++
          [.normalize row.val (state.transform.B row row)]
    rw [refines.events, refines.state_B]

private theorem principalReduceAboveLoop_refines {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → (hk : k ≤ destination.val) →
      (sequence : PrincipalTransitionSequence A) →
      (state : Principal.State A) →
      PrincipalSequenceRefines sequence state →
      PrincipalSequenceRefines
        (PrincipalTransitionSequence.reduceAboveLoop
          destination k hk sequence)
        (Principal.reduceAboveLoop destination k hk state)
  | 0, _, sequence, state, refines => refines
  | k + 1, hk, sequence, state, refines => by
      let previousSequence :=
        PrincipalTransitionSequence.reduceAboveLoop
          destination k (by omega) sequence
      let previousState :=
        Principal.reduceAboveLoop destination k (by omega) state
      have previousRefines :
          PrincipalSequenceRefines previousSequence previousState :=
        principalReduceAboveLoop_refines destination k
          (by omega) sequence state refines
      let source : Fin n := ⟨k, by omega⟩
      simpa [PrincipalTransitionSequence.reduceAboveLoop,
        Principal.reduceAboveLoop, previousSequence, previousState, source] using
        previousRefines.reduceAbove source destination (by
          change k < destination.val
          omega)

private theorem principalEliminateStageLoop_refines {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (k : Nat) → (hk : k ≤ target.val) →
      (sequence : PrincipalTransitionSequence A) →
      (state : Principal.State A) →
      PrincipalSequenceRefines sequence state →
      PrincipalSequenceRefines
        (PrincipalTransitionSequence.eliminateStageLoop target k hk sequence)
        (Principal.eliminateStageLoop target k hk state)
  | 0, _, sequence, state, refines => refines
  | k + 1, hk, sequence, state, refines => by
      let previousSequence :=
        PrincipalTransitionSequence.eliminateStageLoop
          target k (by omega) sequence
      let previousState :=
        Principal.eliminateStageLoop target k (by omega) state
      have previousRefines :
          PrincipalSequenceRefines previousSequence previousState :=
        principalEliminateStageLoop_refines target k
          (by omega) sequence state refines
      let pivot : Fin n := ⟨k, by omega⟩
      have eliminatedRefines :=
        previousRefines.gcdEliminate pivot target (by
          change k < target.val
          omega)
      simpa [PrincipalTransitionSequence.eliminateStageLoop,
        Principal.eliminateStageLoop, previousSequence, previousState,
        pivot] using
        principalReduceAboveLoop_refines pivot pivot.val le_rfl
          _ _ eliminatedRefines

private theorem principalExtendStage_refines {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (target : Fin n)
    (sequence : PrincipalTransitionSequence A)
    (state : Principal.State A)
    (refines : PrincipalSequenceRefines sequence state) :
    PrincipalSequenceRefines
      (PrincipalTransitionSequence.extendStage target sequence)
      (Principal.extendStage target state) := by
  let eliminatedSequence :=
    PrincipalTransitionSequence.eliminateStageLoop
      target target.val le_rfl sequence
  let eliminatedState :=
    Principal.eliminateStageLoop target target.val le_rfl state
  have eliminatedRefines :
      PrincipalSequenceRefines eliminatedSequence eliminatedState :=
    principalEliminateStageLoop_refines target target.val le_rfl
      sequence state refines
  have normalizedRefines := eliminatedRefines.normalize target
  simpa [PrincipalTransitionSequence.extendStage, Principal.extendStage,
    eliminatedSequence, eliminatedState] using
    principalReduceAboveLoop_refines target target.val le_rfl
      _ _ normalizedRefines

private theorem principalStageLoop_refines {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} :
    (k : Nat) → (hk : k ≤ n) →
      (sequence : PrincipalTransitionSequence A) →
      (state : Principal.State A) →
      PrincipalSequenceRefines sequence state →
      PrincipalSequenceRefines
        (PrincipalTransitionSequence.stageLoop k hk sequence)
        (Principal.stageLoop k hk state)
  | 0, _, sequence, state, refines => refines
  | k + 1, hk, sequence, state, refines => by
      let previousSequence :=
        PrincipalTransitionSequence.stageLoop k (by omega) sequence
      let previousState := Principal.stageLoop k (by omega) state
      have previousRefines :
          PrincipalSequenceRefines previousSequence previousState :=
        principalStageLoop_refines k (by omega) sequence state refines
      let target : Fin n := ⟨k, by omega⟩
      simpa [PrincipalTransitionSequence.stageLoop, Principal.stageLoop,
        previousSequence, previousState, target] using
        principalExtendStage_refines target
          previousSequence previousState previousRefines

private theorem principalTransitionSequence_refines {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    PrincipalSequenceRefines
      (principalTransitionSequence A) (Principal.compute A) := by
  simpa [principalTransitionSequence, Principal.compute] using
    principalStageLoop_refines n le_rfl
      (PrincipalTransitionSequence.initial A)
      (Principal.State.refl A)
      (principalSequenceRefines_initial A)

public theorem principalTransitionSequence_value {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    (principalTransitionSequence A).state.B = (principalRun A).matrix ∧
      (principalTransitionSequence A).steps = (principalRun A).steps ∧
      (principalTransitionSequence A).events =
        (principalRun A).arithmeticEvents := by
  let refines := principalTransitionSequence_refines A
  exact ⟨refines.state_B, refines.steps, refines.events⟩

private structure BoundedColumnSequenceRefines {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (sequence : PrincipalTransitionSequence A)
    (transform : Principal.Transform A)
    (events : List PrincipalArithmeticEvent) : Prop where
  state_B : sequence.state.B = transform.B
  steps : sequence.steps = transform.steps
  events_eq : sequence.events = events

private theorem boundedColumnSequenceRefines_initial {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    BoundedColumnSequenceRefines
      (PrincipalTransitionSequence.initial A)
      (Principal.Transform.refl A) [] := by
  constructor <;> rfl

private theorem BoundedColumnSequenceRefines.bezout {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    {sequence : PrincipalTransitionSequence A}
    {transform : Principal.Transform A}
    {events : List PrincipalArithmeticEvent}
    (refines : BoundedColumnSequenceRefines sequence transform events)
    (target : Fin (n + 1)) (hne : (0 : Fin (n + 1)) ≠ target) :
    BoundedColumnSequenceRefines
      (sequence.apply
        (bezoutTransition sequence.state 0 target
          (Fin.pos_iff_ne_zero.mpr hne.symm))
        rfl)
      (BoundedColumn.pairAtFirstColumn target hne transform)
      (events ++
        [.xgcd 0 target.val
          (transform.B 0 0) (transform.B target 0)]) := by
  have hlt : (0 : Fin (n + 1)) < target :=
    Fin.pos_iff_ne_zero.mpr hne.symm
  constructor
  · rw [PrincipalTransitionSequence.apply,
      PrincipalTransitionExecution.after_B,
      bezoutTransition_step_eq, refines.state_B]
    simp only [PrincipalTransitionExecution.before, bezoutTransition,
      ReversibleRowStep.ofCertificate,
      BoundedColumn.pairAtFirstColumn,
      Principal.Transform.trans, Principal.Transform.ofPrimitive]
    rw [refines.state_B]
  · change
      sequence.steps ++
          [(bezoutTransition sequence.state 0 target hlt).step] =
        transform.steps ++
          [ReversibleRowStep.ofCertificate .bezoutPair
            (boundedPairBezoutMatrixInverseCertificate
              0 target hne (transform.B 0 0) (transform.B target 0))]
    rw [refines.steps, bezoutTransition_step_eq, refines.state_B]
  · change
      sequence.events ++
          [.xgcd 0 target.val
            (sequence.state.B 0 0)
            (sequence.state.B target 0)] =
        events ++
          [.xgcd 0 target.val
            (transform.B 0 0) (transform.B target 0)]
    rw [refines.events_eq, refines.state_B]

private theorem boundedColumnLoop_refines {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → (hk : k ≤ n) →
      (sequence : PrincipalTransitionSequence A) →
      (transform : Principal.Transform A) →
      BoundedColumnSequenceRefines sequence transform [] →
      BoundedColumnSequenceRefines
        (PrincipalTransitionSequence.boundedColumnLoop k hk sequence)
        (BoundedColumn.loop k hk transform)
        (BoundedColumn.arithmeticLoop k hk transform)
  | 0, _, sequence, transform, refines => refines
  | k + 1, hk, sequence, transform, refines => by
      let previousSequence :=
        PrincipalTransitionSequence.boundedColumnLoop
          k (by omega) sequence
      let previousTransform :=
        BoundedColumn.loop k (by omega) transform
      have previousRefines :
          BoundedColumnSequenceRefines previousSequence previousTransform
            (BoundedColumn.arithmeticLoop k (by omega) transform) :=
        boundedColumnLoop_refines k (by omega) sequence transform refines
      let target : Fin (n + 1) := ⟨k + 1, by omega⟩
      simpa [PrincipalTransitionSequence.boundedColumnLoop,
        BoundedColumn.loop, BoundedColumn.arithmeticLoop,
        previousSequence, previousTransform, target] using
        previousRefines.bezout target (by simp [target])

private theorem boundedColumnTransitionSequence_refines {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    BoundedColumnSequenceRefines
      (boundedColumnTransitionSequence A)
      (BoundedColumn.compute A)
      (BoundedColumn.arithmeticEvents A) := by
  let reducedSequence :=
    PrincipalTransitionSequence.boundedColumnLoop n le_rfl
      (PrincipalTransitionSequence.initial A)
  let reduced :=
    BoundedColumn.loop n le_rfl (Principal.Transform.refl A)
  have reducedRefines :
      BoundedColumnSequenceRefines reducedSequence reduced
        (BoundedColumn.arithmeticLoop n le_rfl
          (Principal.Transform.refl A)) :=
    boundedColumnLoop_refines n le_rfl
      (PrincipalTransitionSequence.initial A)
      (Principal.Transform.refl A)
      (boundedColumnSequenceRefines_initial A)
  let boundedState : Principal.State A :=
    { transform := reduced
      events := []
      arithmeticEvents :=
        BoundedColumn.arithmeticLoop n le_rfl
          (Principal.Transform.refl A)
      validEvents := by simp
      validArithmeticEvents :=
        BoundedColumn.arithmeticLoop_valid n le_rfl
          (Principal.Transform.refl A) }
  have normalizedRefines :
      PrincipalSequenceRefines
        (reducedSequence.apply
          (normalizationTransition reducedSequence.state 0) rfl)
        (boundedState.normalize 0) := by
    apply PrincipalSequenceRefines.normalize
    exact
      { state_B := reducedRefines.state_B
        steps := reducedRefines.steps
        events := reducedRefines.events_eq }
  exact
    { state_B := by
        simpa [boundedColumnTransitionSequence, reducedSequence,
          BoundedColumn.compute, Principal.State.normalize, boundedState,
          Principal.Transform.trans, Principal.Transform.unitScale,
          Principal.Transform.ofPrimitive] using normalizedRefines.state_B
      steps := by
        simpa [boundedColumnTransitionSequence, reducedSequence,
          BoundedColumn.compute, Principal.State.normalize, boundedState,
          Principal.Transform.trans, Principal.Transform.unitScale,
          Principal.Transform.ofPrimitive] using normalizedRefines.steps
      events_eq := by
        simpa [boundedColumnTransitionSequence, reducedSequence,
          BoundedColumn.arithmeticEvents, Principal.State.normalize,
          boundedState] using
          normalizedRefines.events }

public theorem boundedColumnTransitionSequence_value {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (boundedColumnTransitionSequence A).steps = boundedColumnTrace A ∧
      (boundedColumnTransitionSequence A).events =
        boundedColumnArithmeticEvents A := by
  let refines := boundedColumnTransitionSequence_refines A
  exact ⟨refines.steps, refines.events_eq⟩

end NormalForms.Research.KannanBachem
