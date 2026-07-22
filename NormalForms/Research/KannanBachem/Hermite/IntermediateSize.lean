/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.Principal
public import NormalForms.Research.KannanBachem.Hermite.CoefficientSize

/-!
# Intermediate matrix sizes

Executable instrumentation for the transformed matrices retained by a row
trace.  This deliberately does not yet claim a polynomial bound: operands
inside extended gcd and the accumulated multiplier require their own proved
envelopes before the coefficient-growth acceptance tier is closed.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix

/-- Largest matrix height in a homogeneous list. -/
@[expose] public def matrixListHeight {m n : Nat} :
    List (_root_.Matrix (Fin m) (Fin n) Int) → Nat
  | [] => 0
  | A :: tail => max (matrixHeight A) (matrixListHeight tail)

/-- Membership in a matrix list gives a height bound by its maximum. -/
public theorem matrixHeight_le_matrixListHeight_of_mem {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    {matrices : List (_root_.Matrix (Fin m) (Fin n) Int)}
    (hmem : A ∈ matrices) :
    matrixHeight A ≤ matrixListHeight matrices := by
  induction matrices with
  | nil => simp at hmem
  | cons head tail ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact le_max_left _ _
      · exact (ih htail).trans (le_max_right _ _)

namespace RowTrace

/-- Replay always occurs as the final member of the intermediate sequence. -/
public theorem replay_mem_intermediates {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (steps : RowTrace Int m) :
    steps.replay A ∈ steps.intermediates A := by
  induction steps generalizing A with
  | nil => simp [replay, intermediates]
  | cons step tail ih =>
      change replay (step.forward * A) tail ∈
        A :: intermediates (step.forward * A) tail
      exact List.mem_cons_of_mem A (ih (step.forward * A))

/-- Maximum transformed-matrix height encountered by replay. -/
@[expose] public def intermediateMatrixHeight {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (steps : RowTrace Int m) : Nat :=
  matrixListHeight (steps.intermediates A)

/-- Binary length of the largest transformed-matrix coefficient in replay. -/
@[expose] public def intermediateMatrixBitLength {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (steps : RowTrace Int m) : Nat :=
  Nat.size (steps.intermediateMatrixHeight A)

/-- The trace's input is included in the intermediate height. -/
public theorem input_height_le_intermediateMatrixHeight {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (steps : RowTrace Int m) :
    matrixHeight A ≤ steps.intermediateMatrixHeight A := by
  apply matrixHeight_le_matrixListHeight_of_mem
  cases steps <;> simp [intermediates]

/-- The replay result is included in the intermediate height. -/
public theorem replay_height_le_intermediateMatrixHeight {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (steps : RowTrace Int m) :
    matrixHeight (steps.replay A) ≤ steps.intermediateMatrixHeight A :=
  matrixHeight_le_matrixListHeight_of_mem
    (replay_mem_intermediates A steps)

/-- Appending more row steps can only enlarge the observed matrix height. -/
public theorem intermediateMatrixHeight_le_append {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (first second : RowTrace Int m) :
    first.intermediateMatrixHeight A ≤
      (first ++ second).intermediateMatrixHeight A := by
  induction first generalizing A with
  | nil =>
      simpa [intermediateMatrixHeight, intermediates, matrixListHeight] using
        input_height_le_intermediateMatrixHeight A second
  | cons step tail ih =>
      simpa [intermediateMatrixHeight, intermediates, matrixListHeight] using
        max_le_max le_rfl (ih (step.forward * A))

/--
An appended replay stays below a common envelope when both constituent
replays do.  The second trace starts at the first trace's replay result.
-/
public theorem intermediateMatrixHeight_append_le {m n bound : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (first second : RowTrace Int m)
    (first_le : first.intermediateMatrixHeight A ≤ bound)
    (second_le : second.intermediateMatrixHeight (first.replay A) ≤ bound) :
    (first ++ second).intermediateMatrixHeight A ≤ bound := by
  induction first generalizing A with
  | nil => simpa [replay] using second_le
  | cons step tail ih =>
      have split : matrixHeight A ≤ bound ∧
          RowTrace.intermediateMatrixHeight (step.forward * A) tail ≤ bound := by
        simpa [intermediateMatrixHeight, intermediates, matrixListHeight] using
          first_le
      have input_le : matrixHeight A ≤ bound := split.1
      have tail_le : RowTrace.intermediateMatrixHeight
          (step.forward * A) tail ≤ bound := split.2
      have appendedTail := ih (step.forward * A) tail_le second_le
      simpa [intermediateMatrixHeight, intermediates, matrixListHeight] using
        max_le input_le appendedTail

/-- Maximum height of every accumulated forward multiplier prefix. -/
@[expose] public def intermediateMultiplierHeight {m : Nat}
    (steps : RowTrace Int m) : Nat :=
  steps.intermediateMatrixHeight
    (1 : _root_.Matrix (Fin m) (Fin m) Int)

/-- Maximum bit length of every accumulated forward multiplier prefix. -/
@[expose] public def intermediateMultiplierBitLength {m : Nat}
    (steps : RowTrace Int m) : Nat :=
  Nat.size steps.intermediateMultiplierHeight

/-- The final accumulated multiplier occurs in the prefix sequence. -/
public theorem accumulator_height_le_intermediateMultiplierHeight {m : Nat}
    (steps : RowTrace Int m) :
    matrixHeight steps.accumulator ≤ steps.intermediateMultiplierHeight := by
  have replayBound := replay_height_le_intermediateMatrixHeight
    (1 : _root_.Matrix (Fin m) (Fin m) Int) steps
  rw [replay_eq_accumulator_mul, _root_.Matrix.mul_one] at replayBound
  exact replayBound

/-- Prefix inverses, updated on the right in forward execution order. -/
@[expose] public def inverseIntermediatesFrom {m : Nat}
    (current : _root_.Matrix (Fin m) (Fin m) Int) :
    RowTrace Int m → List (_root_.Matrix (Fin m) (Fin m) Int)
  | [] => [current]
  | step :: tail =>
      current :: inverseIntermediatesFrom (current * step.backward) tail

theorem inverseProduct_mem_inverseIntermediatesFrom {m : Nat}
    (current : _root_.Matrix (Fin m) (Fin m) Int)
    (steps : RowTrace Int m) :
    current * steps.inverseAccumulator ∈
      steps.inverseIntermediatesFrom current := by
  induction steps generalizing current with
  | nil => simp [inverseIntermediatesFrom, inverseAccumulator]
  | cons step tail ih =>
      change current * (step.backward * inverseAccumulator tail) ∈
        current :: inverseIntermediatesFrom (current * step.backward) tail
      rw [← _root_.Matrix.mul_assoc]
      exact List.mem_cons_of_mem current (ih (current * step.backward))

/-- Maximum height of every directly accumulated inverse prefix. -/
@[expose] public def intermediateInverseMultiplierHeight {m : Nat}
    (steps : RowTrace Int m) : Nat :=
  matrixListHeight <| steps.inverseIntermediatesFrom
    (1 : _root_.Matrix (Fin m) (Fin m) Int)

/-- Maximum bit length of every directly accumulated inverse prefix. -/
@[expose] public def intermediateInverseMultiplierBitLength {m : Nat}
    (steps : RowTrace Int m) : Nat :=
  Nat.size steps.intermediateInverseMultiplierHeight

/-- The final explicit inverse occurs in the inverse-prefix sequence. -/
public theorem inverseAccumulator_height_le_intermediateInverseMultiplierHeight
    {m : Nat} (steps : RowTrace Int m) :
    matrixHeight steps.inverseAccumulator ≤
      steps.intermediateInverseMultiplierHeight := by
  apply matrixHeight_le_matrixListHeight_of_mem
  have member := inverseProduct_mem_inverseIntermediatesFrom
    (1 : _root_.Matrix (Fin m) (Fin m) Int) steps
  simpa using member

end RowTrace

namespace PrincipalArithmeticEvent

/-- Largest absolute operand consumed by one arithmetic event. -/
@[expose] public def operandHeight : PrincipalArithmeticEvent → Nat
  | .xgcd _ _ left right => max left.natAbs right.natAbs
  | .divMod _ _ numerator divisor => max numerator.natAbs divisor.natAbs
  | .normalize _ value => value.natAbs

/-- Binary length of the largest operand consumed by one arithmetic event. -/
@[expose] public def operandBitLength (event : PrincipalArithmeticEvent) : Nat :=
  Nat.size event.operandHeight

end PrincipalArithmeticEvent

/-- Largest arithmetic operand represented in an event list. -/
@[expose] public def arithmeticEventListHeight :
    List PrincipalArithmeticEvent → Nat
  | [] => 0
  | event :: tail => max event.operandHeight (arithmeticEventListHeight tail)

@[simp] public theorem arithmeticEventListHeight_append
    (first second : List PrincipalArithmeticEvent) :
    arithmeticEventListHeight (first ++ second) =
      max (arithmeticEventListHeight first)
        (arithmeticEventListHeight second) := by
  induction first with
  | nil => simp [arithmeticEventListHeight]
  | cons event tail ih =>
      simp [arithmeticEventListHeight, ih, max_assoc]

/-- Largest arithmetic operand consumed by the principal schedule. -/
@[expose] public def principalArithmeticOperandHeight {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Nat :=
  arithmeticEventListHeight (principalRun A).arithmeticEvents

/-- Largest arithmetic-operand bit length in the principal schedule. -/
@[expose] public def principalArithmeticOperandBitLength {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Nat :=
  Nat.size (principalArithmeticOperandHeight A)

/-- Transformed-matrix height observed along the principal schedule. -/
@[expose] public def principalIntermediateMatrixHeight {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Nat :=
  (principalRun A).steps.intermediateMatrixHeight A

/-- Transformed-matrix coefficient length observed along the principal schedule. -/
@[expose] public def principalIntermediateMatrixBitLength {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Nat :=
  Nat.size (principalIntermediateMatrixHeight A)

/-- The observed principal height covers the input. -/
public theorem principal_input_height_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    matrixHeight A ≤ principalIntermediateMatrixHeight A :=
  RowTrace.input_height_le_intermediateMatrixHeight A (principalRun A).steps

/-- The observed principal height covers the returned normal-form candidate. -/
public theorem principal_result_height_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    matrixHeight (principalRun A).matrix ≤
      principalIntermediateMatrixHeight A := by
  rw [← principalRun_replay A]
  exact RowTrace.replay_height_le_intermediateMatrixHeight A
    (principalRun A).steps

/-- Maximum height of all accumulated multiplier prefixes in the principal run. -/
@[expose] public def principalIntermediateMultiplierHeight {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Nat :=
  (principalRun A).steps.intermediateMultiplierHeight

/-- Maximum bit length of all accumulated multiplier prefixes. -/
@[expose] public def principalIntermediateMultiplierBitLength {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Nat :=
  Nat.size (principalIntermediateMultiplierHeight A)

/-- Maximum height of all directly accumulated inverse prefixes. -/
@[expose] public def principalIntermediateInverseHeight {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Nat :=
  (principalRun A).steps.intermediateInverseMultiplierHeight

/-- Maximum bit length of all directly accumulated inverse prefixes. -/
@[expose] public def principalIntermediateInverseBitLength {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Nat :=
  Nat.size (principalIntermediateInverseHeight A)

end NormalForms.Research.KannanBachem.Hermite
