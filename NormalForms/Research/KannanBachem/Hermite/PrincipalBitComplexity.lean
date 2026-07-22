/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalPolynomialBound
public import NormalForms.Research.KannanBachem.Hermite.PrincipalOperationBound
public import NormalForms.Research.KannanBachem.Hermite.BoundedXGCD
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal

/-!
# Bit Complexity of the Ready Principal HNF Kernel

Every arithmetic event is paired with its primitive row operation.  This
module charges the exact bounded-XGCD and long-division reference costs, then
charges all scalar row additions and multiplications with the proved uniform
coefficient width.  The resulting total is bounded by a closed expression in
the dimension and input bit length.

This is a theorem about the explicit schoolbook sign-magnitude cost model.  It
does not identify Lean's native `Int` wall time with formal bit complexity.
-/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

namespace PrincipalArithmeticEvent

/-- The row primitive executed by one arithmetic event. -/
@[expose] public def rowKind : PrincipalArithmeticEvent → RowOperationKind
  | .xgcd .. => .bezoutPair
  | .divMod .. => .add
  | .normalize .. => .unitScale

end PrincipalArithmeticEvent

namespace Principal

/-- Exact reference long-division charge for two standard integer values. -/
@[expose] public def integerDivModBitOperationCost (numerator divisor : Int) : Nat :=
  (NormalForms.Research.BitCost.divModWithCost
    (NormalForms.Research.BitCost.SignMagnitude.ofInt numerator)
    (NormalForms.Research.BitCost.SignMagnitude.ofInt divisor)).cost

/-- Uniform schoolbook long-division budget at one operand width. -/
@[expose] public def integerDivModBitOperationBound (operandBits : Nat) : Nat :=
  NormalForms.Research.BitCost.divisionCostForBitLengths
    operandBits operandBits

public theorem integerDivModBitOperationCost_le
    (numerator divisor : Int) (operandBits : Nat)
    (numeratorWidth : Nat.size numerator.natAbs ≤ operandBits)
    (divisorWidth : Nat.size divisor.natAbs ≤ operandBits) :
    integerDivModBitOperationCost numerator divisor ≤
      integerDivModBitOperationBound operandBits := by
  let encodedNumerator :=
    NormalForms.Research.BitCost.SignMagnitude.ofInt numerator
  let encodedDivisor :=
    NormalForms.Research.BitCost.SignMagnitude.ofInt divisor
  have numeratorWidth' : encodedNumerator.bitLength ≤ operandBits := by
    simpa only [encodedNumerator,
      NormalForms.Research.BitCost.SignMagnitude.bitLength_eq_natSize_natAbs,
      NormalForms.Research.BitCost.SignMagnitude.value_ofInt] using
      numeratorWidth
  have divisorWidth' : encodedDivisor.bitLength ≤ operandBits := by
    simpa only [encodedDivisor,
      NormalForms.Research.BitCost.SignMagnitude.bitLength_eq_natSize_natAbs,
      NormalForms.Research.BitCost.SignMagnitude.value_ofInt] using
      divisorWidth
  exact
    (NormalForms.Research.BitCost.divModWithCost_cost_le
      encodedNumerator encodedDivisor).trans
      (NormalForms.Research.BitCost.Internal.divModBitOperationBound_le_lengths
        encodedNumerator encodedDivisor operandBits operandBits
        numeratorWidth' divisorWidth')

/-- Width sufficient for all four coefficients of a two-row Bezout matrix. -/
@[expose] public def principalRowCoefficientBitLengthBound
    (operandBits : Nat) : Nat :=
  operandBits + 1 +
    NormalForms.Research.BitCost.boundedXGCDCoefficientBitLengthBound operandBits

/-- Bit charge for one XGCD transition and its two-row matrix update. -/
@[expose] public def principalXGCDTransitionBitOperationBound
    (dimension operandBits : Nat) : Nat :=
  let coefficientBits := principalRowCoefficientBitLengthBound operandBits
  boundedIntXGCDUniformBitOperationBound operandBits + 1 +
    4 * dimension *
      NormalForms.Research.BitCost.multiplicationCostForBitLengths
        coefficientBits operandBits +
    2 * dimension *
      NormalForms.Research.BitCost.additionCostForBitLengths
        (coefficientBits + operandBits) (coefficientBits + operandBits)

/-- Bit charge for one quotient transition and its single-row update. -/
@[expose] public def principalDivModTransitionBitOperationBound
    (dimension operandBits : Nat) : Nat :=
  integerDivModBitOperationBound operandBits + 1 +
    dimension *
      NormalForms.Research.BitCost.multiplicationCostForBitLengths
        (operandBits + 1) operandBits +
    dimension *
      NormalForms.Research.BitCost.additionCostForBitLengths
        operandBits (2 * operandBits + 1)

/-- Bit charge for one sign normalization and its row scaling. -/
@[expose] public def principalNormalizeTransitionBitOperationBound
    (dimension operandBits : Nat) : Nat :=
  1 + dimension *
    NormalForms.Research.BitCost.multiplicationCostForBitLengths 1 operandBits

/-- One uniform transition budget covering all three event classes. -/
@[expose] public def principalTransitionBitOperationBound
    (dimension operandBits : Nat) : Nat :=
  principalXGCDTransitionBitOperationBound dimension operandBits +
    principalDivModTransitionBitOperationBound dimension operandBits +
    principalNormalizeTransitionBitOperationBound dimension operandBits

end Principal

namespace PrincipalArithmeticEvent

/--
Reference-model charge for an actual event.  Matrix row entries are charged at
the supplied uniform width; the Euclidean primitive uses its exact modeled
cost.
-/
@[expose] public def chargedBitOperationCost
    (dimension operandBits : Nat) : PrincipalArithmeticEvent → Nat
  | .xgcd _ _ left right =>
      let coefficientBits :=
        Principal.principalRowCoefficientBitLengthBound operandBits
      Principal.boundedIntXGCDBitOperationCost left right + 1 +
        4 * dimension *
          NormalForms.Research.BitCost.multiplicationCostForBitLengths
            coefficientBits operandBits +
        2 * dimension *
          NormalForms.Research.BitCost.additionCostForBitLengths
            (coefficientBits + operandBits) (coefficientBits + operandBits)
  | .divMod _ _ numerator divisor =>
      Principal.integerDivModBitOperationCost numerator divisor + 1 +
        dimension *
          NormalForms.Research.BitCost.multiplicationCostForBitLengths
            (operandBits + 1) operandBits +
        dimension *
          NormalForms.Research.BitCost.additionCostForBitLengths
            operandBits (2 * operandBits + 1)
  | .normalize _ _ =>
      Principal.principalNormalizeTransitionBitOperationBound
        dimension operandBits

/-- One event's exact Euclidean charge and row charge fit the uniform budget. -/
public theorem chargedBitOperationCost_le
    (event : PrincipalArithmeticEvent) (dimension operandBits : Nat)
    (operandWidth : event.operandBitLength ≤ operandBits) :
    event.chargedBitOperationCost dimension operandBits ≤
      Principal.principalTransitionBitOperationBound dimension operandBits := by
  cases event with
  | xgcd pivot target left right =>
      have leftWidth : Nat.size left.natAbs ≤ operandBits :=
        (Nat.size_le_size (le_max_left left.natAbs right.natAbs)).trans
          operandWidth
      have rightWidth : Nat.size right.natAbs ≤ operandBits :=
        (Nat.size_le_size (le_max_right left.natAbs right.natAbs)).trans
          operandWidth
      have primitive := Principal.boundedIntXGCDBitOperationCost_le_uniform
        left right operandBits leftWidth rightWidth
      simp only [chargedBitOperationCost,
        Principal.principalTransitionBitOperationBound,
        Principal.principalXGCDTransitionBitOperationBound]
      omega
  | divMod source destination numerator divisor =>
      have numeratorWidth : Nat.size numerator.natAbs ≤ operandBits :=
        (Nat.size_le_size (le_max_left numerator.natAbs divisor.natAbs)).trans
          operandWidth
      have divisorWidth : Nat.size divisor.natAbs ≤ operandBits :=
        (Nat.size_le_size (le_max_right numerator.natAbs divisor.natAbs)).trans
          operandWidth
      have primitive := Principal.integerDivModBitOperationCost_le
        numerator divisor operandBits numeratorWidth divisorWidth
      simp only [chargedBitOperationCost,
        Principal.principalTransitionBitOperationBound,
        Principal.principalDivModTransitionBitOperationBound]
      omega
  | normalize row value =>
      simp only [chargedBitOperationCost,
        Principal.principalTransitionBitOperationBound]
      omega

end PrincipalArithmeticEvent

/-- Sum of all charged reference-model event costs. -/
@[expose] public def arithmeticEventListBitOperationCost
    (dimension operandBits : Nat) : List PrincipalArithmeticEvent → Nat
  | [] => 0
  | event :: tail =>
      event.chargedBitOperationCost dimension operandBits +
        arithmeticEventListBitOperationCost dimension operandBits tail

public theorem PrincipalArithmeticEvent.operandHeight_le_list_of_mem
    (event : PrincipalArithmeticEvent) (events : List PrincipalArithmeticEvent)
    (member : event ∈ events) :
    event.operandHeight ≤ arithmeticEventListHeight events := by
  induction events with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact le_max_left _ _
      · exact (ih member).trans (le_max_right _ _)

public theorem PrincipalArithmeticEvent.operandBitLength_le_list_of_mem
    (event : PrincipalArithmeticEvent) (events : List PrincipalArithmeticEvent)
    (member : event ∈ events) :
    event.operandBitLength ≤ Nat.size (arithmeticEventListHeight events) :=
  Nat.size_le_size (event.operandHeight_le_list_of_mem events member)

/-- A list with uniformly bounded operands costs at most length times one step. -/
public theorem arithmeticEventListBitOperationCost_le
    (events : List PrincipalArithmeticEvent) (dimension operandBits : Nat)
    (allWidths : ∀ event ∈ events, event.operandBitLength ≤ operandBits) :
    arithmeticEventListBitOperationCost dimension operandBits events ≤
      events.length *
        Principal.principalTransitionBitOperationBound dimension operandBits := by
  induction events with
  | nil => simp [arithmeticEventListBitOperationCost]
  | cons head tail ih =>
      have headBound := head.chargedBitOperationCost_le dimension operandBits
        (allWidths head (by simp))
      have tailBound := ih fun event member =>
        allWidths event (by simp [member])
      rw [arithmeticEventListBitOperationCost, List.length_cons]
      calc
        head.chargedBitOperationCost dimension operandBits +
              arithmeticEventListBitOperationCost dimension operandBits tail ≤
            Principal.principalTransitionBitOperationBound dimension operandBits +
              tail.length *
                Principal.principalTransitionBitOperationBound dimension operandBits :=
          Nat.add_le_add headBound tailBound
        _ = (tail.length + 1) *
              Principal.principalTransitionBitOperationBound dimension operandBits := by
          ring

namespace Principal

/-- Arithmetic events and primitive row steps remain aligned by operation class. -/
def State.ArithmeticTraceAligned {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} (state : State A) : Prop :=
  state.arithmeticEvents.map PrincipalArithmeticEvent.rowKind =
    state.transform.steps.map ReversibleRowStep.kind

theorem State.ArithmeticTraceAligned.refl {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (State.refl A).ArithmeticTraceAligned := by
  rfl

theorem State.ArithmeticTraceAligned.gcdEliminate {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    {state : State A} (aligned : state.ArithmeticTraceAligned) :
    (state.gcdEliminate pivot target hlt).ArithmeticTraceAligned := by
  unfold State.ArithmeticTraceAligned at aligned ⊢
  simp only [State.gcdEliminate, pairBezoutAt, Transform.trans,
    Transform.ofPrimitive, PrincipalArithmeticEvent.rowKind,
    ReversibleRowStep.ofCertificate, List.map_append, List.map_cons,
    List.map_nil]
  rw [aligned]

theorem State.ArithmeticTraceAligned.reduceAbove {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination)
    {state : State A} (aligned : state.ArithmeticTraceAligned) :
    (state.reduceAbove source destination hlt).ArithmeticTraceAligned := by
  unfold State.ArithmeticTraceAligned at aligned ⊢
  simp only [State.reduceAbove, Transform.trans, Transform.add,
    Transform.ofPrimitive, PrincipalArithmeticEvent.rowKind,
    ReversibleRowStep.ofCertificate, List.map_append, List.map_cons,
    List.map_nil]
  rw [aligned]

theorem State.ArithmeticTraceAligned.normalize {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (row : Fin n) {state : State A} (aligned : state.ArithmeticTraceAligned) :
    (state.normalize row).ArithmeticTraceAligned := by
  unfold State.ArithmeticTraceAligned at aligned ⊢
  simp only [State.normalize, Transform.trans, Transform.unitScale,
    Transform.ofPrimitive, PrincipalArithmeticEvent.rowKind,
    ReversibleRowStep.ofCertificate, List.map_append, List.map_cons,
    List.map_nil]
  rw [aligned]

theorem reduceAboveLoop_arithmeticTraceAligned {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → (hk : k ≤ destination.val) → (state : State A) →
      state.ArithmeticTraceAligned →
        (reduceAboveLoop destination k hk state).ArithmeticTraceAligned
  | 0, _, _, aligned => aligned
  | k + 1, hk, state, aligned => by
      let previous := reduceAboveLoop destination k (by omega) state
      have previousAligned := reduceAboveLoop_arithmeticTraceAligned
        destination k (by omega) state aligned
      exact previousAligned.reduceAbove ⟨k, by omega⟩ destination (by
        change k < destination.val
        omega)

theorem eliminateStageLoop_arithmeticTraceAligned {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (k : Nat) → (hk : k ≤ target.val) → (state : State A) →
      state.ArithmeticTraceAligned →
        (eliminateStageLoop target k hk state).ArithmeticTraceAligned
  | 0, _, _, aligned => aligned
  | k + 1, hk, state, aligned => by
      let previous := eliminateStageLoop target k (by omega) state
      let pivot : Fin n := ⟨k, by omega⟩
      have previousAligned := eliminateStageLoop_arithmeticTraceAligned
        target k (by omega) state aligned
      have eliminatedAligned := previousAligned.gcdEliminate pivot target (by
        change k < target.val
        omega)
      exact reduceAboveLoop_arithmeticTraceAligned pivot pivot.val le_rfl _
        eliminatedAligned

theorem extendStage_arithmeticTraceAligned {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (state : State A)
    (aligned : state.ArithmeticTraceAligned) :
    (extendStage target state).ArithmeticTraceAligned := by
  let eliminated := eliminateStageLoop target target.val le_rfl state
  have eliminatedAligned := eliminateStageLoop_arithmeticTraceAligned
    target target.val le_rfl state aligned
  let normalized := eliminated.normalize target
  have normalizedAligned := eliminatedAligned.normalize target
  exact reduceAboveLoop_arithmeticTraceAligned target target.val le_rfl
    normalized normalizedAligned

theorem stageLoop_arithmeticTraceAligned {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : State A) →
      state.ArithmeticTraceAligned →
        (stageLoop k hk state).ArithmeticTraceAligned
  | 0, _, _, aligned => aligned
  | k + 1, hk, state, aligned => by
      let previous := stageLoop k (by omega) state
      have previousAligned := stageLoop_arithmeticTraceAligned
        k (by omega) state aligned
      exact extendStage_arithmeticTraceAligned ⟨k, by omega⟩ previous
        previousAligned

theorem compute_arithmeticTraceAligned {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (compute A).ArithmeticTraceAligned :=
  stageLoop_arithmeticTraceAligned n le_rfl (State.refl A)
    (State.ArithmeticTraceAligned.refl A)

end Principal

/-- The executable event stream is in bijective order with the primitive trace. -/
public theorem principalRun_arithmeticTraceAligned {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (principalRun A).arithmeticEvents.map PrincipalArithmeticEvent.rowKind =
      (principalRun A).steps.map ReversibleRowStep.kind := by
  change
    (Principal.compute A).arithmeticEvents.map
        PrincipalArithmeticEvent.rowKind =
      (Principal.compute A).transform.steps.map ReversibleRowStep.kind
  exact Principal.compute_arithmeticTraceAligned A

public theorem principalRun_arithmeticEvents_length {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (principalRun A).arithmeticEvents.length =
      (principalRun A).steps.length := by
  have aligned := congrArg List.length (principalRun_arithmeticTraceAligned A)
  simpa using aligned

public theorem principalRun_arithmeticEvents_length_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    (principalRun A).arithmeticEvents.length ≤ n ^ 3 := by
  rw [principalRun_arithmeticEvents_length]
  exact principalRun_steps_length_le A

/-- Executable reference-model bit charge for the ready principal HNF run. -/
@[expose] public def principalHNFBitOperationCost {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Nat :=
  let operandBits :=
    Principal.principalPolynomialBitLengthBound n (matrixBitLength A)
  arithmeticEventListBitOperationCost n operandBits
    (principalRun A).arithmeticEvents

/-- Closed HNF bit-operation budget in dimension and input coefficient width. -/
@[expose] public def principalHNFBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  let operandBits :=
    Principal.principalPolynomialBitLengthBound dimension inputBits
  dimension ^ 3 *
    Principal.principalTransitionBitOperationBound dimension operandBits

/-- Stage four: the ready principal HNF kernel has polynomial bit complexity. -/
public theorem principalHNFBitOperationCost_le_of_ready {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int)
    (ready : Principal.PrincipalReady A) :
    principalHNFBitOperationCost A ≤
      principalHNFBitOperationBound n (matrixBitLength A) := by
  let operandBits :=
    Principal.principalPolynomialBitLengthBound n (matrixBitLength A)
  have globalWidth : principalArithmeticOperandBitLength A ≤ operandBits := by
    simpa only [operandBits] using
      principalArithmeticOperandBitLength_le_polynomial_of_ready A ready
  have allWidths : ∀ event ∈ (principalRun A).arithmeticEvents,
      event.operandBitLength ≤ operandBits := by
    intro event member
    exact
      (event.operandBitLength_le_list_of_mem
        (principalRun A).arithmeticEvents member).trans globalWidth
  have eventCost := arithmeticEventListBitOperationCost_le
    (principalRun A).arithmeticEvents n operandBits allWidths
  have lengthBound := principalRun_arithmeticEvents_length_le A
  have multiplied := Nat.mul_le_mul_right
    (Principal.principalTransitionBitOperationBound n operandBits) lengthBound
  change
    arithmeticEventListBitOperationCost n operandBits
        (principalRun A).arithmeticEvents ≤
      n ^ 3 * Principal.principalTransitionBitOperationBound n operandBits
  exact eventCost.trans multiplied

end NormalForms.Research.KannanBachem.Hermite
