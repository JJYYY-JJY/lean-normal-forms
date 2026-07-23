/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Transition
public import NormalForms.Research.KannanBachem.Hermite.PrincipalCorrectness
public import NormalForms.Research.KannanBachem.Hermite.PrincipalBitComplexity
public import NormalForms.Research.KannanBachem.Hermite.PrincipalMultiplierBound
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal

/-!
# Value-producing Principal HNF Execution

The principal execution obtains its matrix, multiplier, and explicit inverse
by replaying the primitive row steps through costed dense products.  The
existing `principalRun` appears only in refinement theorems.
-/

public section

namespace NormalForms.Research.KannanBachem

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

/-- Uniform scalar-leaf budget for one principal transition. -/
@[expose] public def principalScalarTransitionBitOperationBound
    (operandBits : Nat) : Nat :=
  Principal.boundedIntXGCDUniformBitOperationBound operandBits + 1 +
    3 * Principal.integerDivModBitOperationBound operandBits + 1

private theorem boundedXGCD_gcd_bitLength_le_max
    (left right : SignMagnitude) :
    (boundedXGCDWithCost left right).value.gcd.bitLength ≤
      max left.bitLength right.bitLength := by
  rw [SignMagnitude.bitLength_eq_natSize_natAbs,
    (boundedXGCDWithCost_spec left right).gcd_value,
    SignMagnitude.bitLength_eq_natSize_natAbs,
    SignMagnitude.bitLength_eq_natSize_natAbs]
  simp only [Int.natAbs_natCast]
  rw [← natSize_max]
  apply Nat.size_le_size
  by_cases leftZero : left.value = 0
  · rw [leftZero]
    simp
  · exact (Int.gcd_le_natAbs_left right.value leftZero).trans
      (le_max_left _ _)

private theorem principalTransition_scalarCost_le {n operandBits : Nat}
    (transition : PrincipalTransitionExecution n)
    (operandBound :
      transition.event.operandBitLength ≤ operandBits) :
    transition.scalarCharge.bitCost ≤
      principalScalarTransitionBitOperationBound operandBits := by
  cases transition with
  | mk data =>
      cases data with
      | bezout before pivot target hlt run run_eq =>
          subst run
          let left := SignMagnitude.ofInt (before.B pivot pivot)
          let right := SignMagnitude.ofInt (before.B target pivot)
          let xgcdRun := boundedXGCDWithCost left right
          have leftWidth : left.bitLength ≤ operandBits := by
            simpa [PrincipalTransitionExecution.event,
              PrincipalArithmeticEvent.operandBitLength,
              PrincipalArithmeticEvent.operandHeight, left,
              SignMagnitude.bitLength_eq_natSize_natAbs,
              SignMagnitude.value_ofInt] using
              (Nat.size_le_size
                (le_max_left
                  (before.B pivot pivot).natAbs
                  (before.B target pivot).natAbs)).trans operandBound
          have rightWidth : right.bitLength ≤ operandBits := by
            simpa [PrincipalTransitionExecution.event,
              PrincipalArithmeticEvent.operandBitLength,
              PrincipalArithmeticEvent.operandHeight, right,
              SignMagnitude.bitLength_eq_natSize_natAbs,
              SignMagnitude.value_ofInt] using
              (Nat.size_le_size
                (le_max_right
                  (before.B pivot pivot).natAbs
                  (before.B target pivot).natAbs)).trans operandBound
          have gcdWidth : xgcdRun.value.gcd.bitLength ≤ operandBits :=
            (boundedXGCD_gcd_bitLength_le_max left right).trans
              (max_le leftWidth rightWidth)
          have xgcdCost :
              xgcdRun.cost ≤
                Principal.boundedIntXGCDUniformBitOperationBound
                  operandBits := by
            simpa [xgcdRun, left, right,
              Principal.boundedIntXGCDBitOperationCost] using
              Principal.boundedIntXGCDBitOperationCost_le_uniform
                (before.B pivot pivot) (before.B target pivot)
                operandBits
                (by simpa [left,
                    SignMagnitude.bitLength_eq_natSize_natAbs] using
                    leftWidth)
                (by simpa [right,
                    SignMagnitude.bitLength_eq_natSize_natAbs] using
                    rightWidth)
          have leftDivision :
              (divModWithCost left xgcdRun.value.gcd).cost ≤
                Principal.integerDivModBitOperationBound operandBits :=
            (divModWithCost_cost_le _ _).trans <|
              Internal.divModBitOperationBound_le_lengths _ _
                operandBits operandBits leftWidth gcdWidth
          have rightDivision :
              (divModWithCost right xgcdRun.value.gcd).cost ≤
                Principal.integerDivModBitOperationBound operandBits :=
            (divModWithCost_cost_le _ _).trans <|
              Internal.divModBitOperationBound_le_lengths _ _
                operandBits operandBits rightWidth gcdWidth
          have blockCost :=
            boundedBezoutBlockWithCost_cost_le left right
          change (boundedBezoutBlockWithCost left right).cost ≤ _
          unfold boundedBezoutBlockBitOperationBound at blockCost
          unfold principalScalarTransitionBitOperationBound
          dsimp only at blockCost
          dsimp [xgcdRun] at xgcdCost leftDivision rightDivision
          omega
      | reduceAbove before source destination hlt run run_eq =>
          subst run
          have numeratorWidth :
              Nat.size (before.B source destination).natAbs ≤ operandBits :=
            (Nat.size_le_size
              (le_max_left
                (before.B source destination).natAbs
                (before.B destination destination).natAbs)).trans
              operandBound
          have divisorWidth :
              Nat.size
                  (before.B destination destination).natAbs ≤ operandBits :=
            (Nat.size_le_size
              (le_max_right
                (before.B source destination).natAbs
                (before.B destination destination).natAbs)).trans
              operandBound
          have divisionCost :=
            Principal.integerDivModBitOperationCost_le
              (before.B source destination)
              (before.B destination destination)
              operandBits numeratorWidth divisorWidth
          simpa [PrincipalTransitionExecution.scalarCharge,
            KannanBachemArithmeticCharge.divModOfRun,
            KannanBachemArithmeticCharge.bitCost,
            Principal.integerDivModBitOperationCost] using
            (divisionCost.trans (by
              unfold principalScalarTransitionBitOperationBound
              omega))
      | normalize before row run run_eq =>
          subst run
          simp [PrincipalTransitionExecution.scalarCharge,
            KannanBachemArithmeticCharge.normalizationOfRun,
            KannanBachemArithmeticCharge.bitCost,
            normalizationUnitWithCost,
            principalScalarTransitionBitOperationBound]

private theorem inverseIntermediatesHeight_le_appendFrom {n : Nat}
    (current : Matrix (Fin n) (Fin n) Int)
    (first second : RowTrace Int n) :
    matrixListHeight (first.inverseIntermediatesFrom current) ≤
      matrixListHeight ((first ++ second).inverseIntermediatesFrom current) := by
  induction first generalizing current with
  | nil =>
      simp only [RowTrace.inverseIntermediatesFrom, List.nil_append,
        matrixListHeight]
      rw [max_eq_left (Nat.zero_le _)]
      apply matrixHeight_le_matrixListHeight_of_mem
      cases second <;> simp [RowTrace.inverseIntermediatesFrom]
  | cons step tail ih =>
      simp only [RowTrace.inverseIntermediatesFrom, List.cons_append,
        matrixListHeight]
      exact max_le_max le_rfl (ih (current * step.backward))

private theorem inverseIntermediateBitLength_le_append {n : Nat}
    (first second : RowTrace Int n) :
    first.intermediateInverseMultiplierBitLength ≤
      (first ++ second).intermediateInverseMultiplierBitLength := by
  unfold RowTrace.intermediateInverseMultiplierBitLength
    RowTrace.intermediateInverseMultiplierHeight
  exact Nat.size_le_size
    (inverseIntermediatesHeight_le_appendFrom 1 first second)

private theorem prefixAccumulator_bitLength_le {n : Nat}
    (first second : RowTrace Int n) :
    matrixBitLength first.accumulator ≤
      (first ++ second).intermediateMultiplierBitLength := by
  apply (Nat.size_le_size
    first.accumulator_height_le_intermediateMultiplierHeight).trans
  unfold RowTrace.intermediateMultiplierBitLength
  exact Nat.size_le_size <|
    RowTrace.intermediateMatrixHeight_le_append 1 first second

private theorem prefixInverse_bitLength_le {n : Nat}
    (first second : RowTrace Int n) :
    matrixBitLength first.inverseAccumulator ≤
      (first ++ second).intermediateInverseMultiplierBitLength := by
  apply (Nat.size_le_size
    first.inverseAccumulator_height_le_intermediateInverseMultiplierHeight).trans
  exact inverseIntermediateBitLength_le_append first second

private theorem prefixReplay_bitLength_le {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (first second : RowTrace Int n) :
    matrixBitLength (first.replay A) ≤
      (first ++ second).intermediateMatrixBitLength A := by
  apply (Nat.size_le_size
    (RowTrace.replay_height_le_intermediateMatrixHeight A first)).trans
  unfold RowTrace.intermediateMatrixBitLength
  exact Nat.size_le_size <|
    RowTrace.intermediateMatrixHeight_le_append A first second

/-- Common width for a row step and every relative suffix transform. -/
@[expose] public def rowTraceTransformBitLengthBound
    (dimension forwardBits inverseBits : Nat) : Nat :=
  Nat.size dimension + forwardBits + inverseBits

/-- Dense replay budget for all three products executed by every row step. -/
@[expose] public def rowTraceDenseBitOperationBound
    (dimension steps matrixBits forwardBits inverseBits : Nat) : Nat :=
  let transformBits :=
    rowTraceTransformBitLengthBound dimension forwardBits inverseBits
  steps *
    (matrixMultiplicationBitOperationBound dimension transformBits matrixBits +
      2 * matrixMultiplicationBitOperationBound
        dimension transformBits transformBits)

public theorem rowTraceDenseBitOperationBound_mono
    (dimension : Nat)
    {stepsSmall stepsLarge matrixSmall matrixLarge
      forwardSmall forwardLarge inverseSmall inverseLarge : Nat}
    (stepsLe : stepsSmall ≤ stepsLarge)
    (matrixLe : matrixSmall ≤ matrixLarge)
    (forwardLe : forwardSmall ≤ forwardLarge)
    (inverseLe : inverseSmall ≤ inverseLarge) :
    rowTraceDenseBitOperationBound dimension stepsSmall matrixSmall
        forwardSmall inverseSmall ≤
      rowTraceDenseBitOperationBound dimension stepsLarge matrixLarge
        forwardLarge inverseLarge := by
  have transformLe :
      rowTraceTransformBitLengthBound dimension forwardSmall inverseSmall ≤
        rowTraceTransformBitLengthBound dimension forwardLarge inverseLarge := by
    unfold rowTraceTransformBitLengthBound
    omega
  unfold rowTraceDenseBitOperationBound
  apply Nat.mul_le_mul stepsLe
  exact Nat.add_le_add
    (matrixMultiplicationBitOperationBound_mono
      dimension transformLe matrixLe)
    (Nat.mul_le_mul_left 2 <|
      matrixMultiplicationBitOperationBound_mono
        dimension transformLe transformLe)

private theorem traceBitCost_flatMap {α : Type*} (values : List α)
    (f : α → List KannanBachemArithmeticCharge) :
    traceBitCost (values.flatMap f) =
      (values.map fun value ↦ traceBitCost (f value)).sum := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [traceBitCost_append, ih]

public theorem principalTransition_cost_le {n operandBits matrixBits
    forwardBits inverseBits : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (sequence : PrincipalTransitionSequence A)
    (transition : PrincipalTransitionExecution n)
    (member : transition ∈ sequence.transitions)
    (allWidths : ∀ event ∈ sequence.events,
      event.operandBitLength ≤ operandBits)
    (matrixWidth :
      sequence.steps.intermediateMatrixBitLength A ≤ matrixBits)
    (forwardWidth :
      sequence.steps.intermediateMultiplierBitLength ≤ forwardBits)
    (inverseWidth :
      sequence.steps.intermediateInverseMultiplierBitLength ≤ inverseBits) :
    traceBitCost transition.charges ≤
      principalScalarTransitionBitOperationBound operandBits +
        (matrixMultiplicationBitOperationBound n
            (rowTraceTransformBitLengthBound n forwardBits inverseBits)
            matrixBits +
          2 * matrixMultiplicationBitOperationBound n
            (rowTraceTransformBitLengthBound n forwardBits inverseBits)
            (rowTraceTransformBitLengthBound
              n forwardBits inverseBits)) := by
  obtain ⟨before, after, stepsEq, beforeB, beforeU, beforeUinv⟩ :=
    sequence.transition_prefix transition member
  let nextBefore := before ++ [transition.step]
  let transformBits :=
    rowTraceTransformBitLengthBound n forwardBits inverseBits
  have split : nextBefore ++ after = sequence.steps := by
    rw [stepsEq]
    simp [nextBefore, List.append_assoc]
  have eventMember : transition.event ∈ sequence.events := by
    rw [sequence.events_eq_transitions]
    exact List.mem_map.mpr ⟨transition, member, rfl⟩
  have scalarCost :=
    principalTransition_scalarCost_le transition
      (allWidths transition.event eventMember)
  have beforeMatrixBits :
      matrixBitLength transition.before.B ≤ matrixBits := by
    rw [beforeB]
    exact (prefixReplay_bitLength_le A before
      (transition.step :: after)).trans (by
        simpa only [stepsEq] using matrixWidth)
  have beforeForwardBits :
      matrixBitLength transition.before.U ≤ forwardBits := by
    rw [beforeU]
    exact (prefixAccumulator_bitLength_le before
      (transition.step :: after)).trans (by
        simpa only [stepsEq] using forwardWidth)
  have beforeInverseBits :
      matrixBitLength transition.before.Uinv ≤ inverseBits := by
    rw [beforeUinv]
    exact (prefixInverse_bitLength_le before
      (transition.step :: after)).trans (by
        simpa only [stepsEq] using inverseWidth)
  have nextForwardBits :
      matrixBitLength nextBefore.accumulator ≤ forwardBits := by
    exact (prefixAccumulator_bitLength_le nextBefore after).trans (by
      rw [split]
      exact forwardWidth)
  have nextInverseBits :
      matrixBitLength nextBefore.inverseAccumulator ≤ inverseBits := by
    exact (prefixInverse_bitLength_le nextBefore after).trans (by
      rw [split]
      exact inverseWidth)
  have beforeAccumulatorBits :
      matrixBitLength before.accumulator ≤ forwardBits := by
    rw [← beforeU]
    exact beforeForwardBits
  have beforeInverseAccumulatorBits :
      matrixBitLength before.inverseAccumulator ≤ inverseBits := by
    rw [← beforeUinv]
    exact beforeInverseBits
  have stepForwardIdentity :
      transition.step.forward =
        nextBefore.accumulator * before.inverseAccumulator := by
    simp [nextBefore, RowTrace.accumulator_append,
      RowTrace.accumulator, Matrix.mul_assoc,
      RowTrace.accumulator_mul_inverse]
  have stepBackwardIdentity :
      transition.step.backward =
        before.accumulator * nextBefore.inverseAccumulator := by
    rw [show nextBefore.inverseAccumulator =
        before.inverseAccumulator * transition.step.backward by
      simp [nextBefore, RowTrace.inverseAccumulator_append,
        RowTrace.inverseAccumulator]]
    rw [← Matrix.mul_assoc, RowTrace.accumulator_mul_inverse,
      NormalForms.Matrix.Constructive.one_mul]
  have stepForwardBits :
      matrixBitLength transition.step.forward ≤ transformBits := by
    rw [stepForwardIdentity]
    exact (matrix_mul_bitLength_le _ _).trans (by
      unfold transformBits rowTraceTransformBitLengthBound
      omega)
  have stepBackwardBits :
      matrixBitLength transition.step.backward ≤ transformBits := by
    rw [stepBackwardIdentity]
    exact (matrix_mul_bitLength_le _ _).trans (by
      unfold transformBits rowTraceTransformBitLengthBound
      omega)
  have matrixCost :
      matrixMultiplicationBitOperationCost
          transition.step.forward transition.before.B ≤
        matrixMultiplicationBitOperationBound
          n transformBits matrixBits :=
    matrixMultiplicationBitOperationCost_le _ _
      stepForwardBits beforeMatrixBits
  have forwardCost :
      matrixMultiplicationBitOperationCost
          transition.step.forward transition.before.U ≤
        matrixMultiplicationBitOperationBound
          n transformBits transformBits :=
    matrixMultiplicationBitOperationCost_le _ _ stepForwardBits
      (beforeForwardBits.trans (by
        unfold transformBits rowTraceTransformBitLengthBound
        omega))
  have inverseCost :
      matrixMultiplicationBitOperationCost
          transition.before.Uinv transition.step.backward ≤
        matrixMultiplicationBitOperationBound
          n transformBits transformBits :=
    matrixMultiplicationBitOperationCost_le _ _
      (beforeInverseBits.trans (by
        unfold transformBits rowTraceTransformBitLengthBound
        omega))
      stepBackwardBits
  rw [PrincipalTransitionExecution.charges,
    traceBitCost_append, traceBitCost_append, traceBitCost_append,
    PrincipalTransitionExecution.matrixRun,
    PrincipalTransitionExecution.forwardRun,
    PrincipalTransitionExecution.inverseRun,
    matrixProductExecution_cost_eq, matrixProductExecution_cost_eq,
    matrixProductExecution_cost_eq]
  simp only [traceBitCost, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  dsimp [transformBits] at matrixCost forwardCost inverseCost
  omega

public theorem principalTransitionSequence_cost_le {n operandBits matrixBits
    forwardBits inverseBits : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (sequence : PrincipalTransitionSequence A)
    (allWidths : ∀ event ∈ sequence.events,
      event.operandBitLength ≤ operandBits)
    (matrixWidth :
      sequence.steps.intermediateMatrixBitLength A ≤ matrixBits)
    (forwardWidth :
      sequence.steps.intermediateMultiplierBitLength ≤ forwardBits)
    (inverseWidth :
      sequence.steps.intermediateInverseMultiplierBitLength ≤ inverseBits) :
    traceBitCost sequence.charges ≤
      sequence.steps.length *
          principalScalarTransitionBitOperationBound operandBits +
        rowTraceDenseBitOperationBound n sequence.steps.length
          matrixBits forwardBits inverseBits := by
  rw [sequence.coverage.charges_eq_flatten, traceBitCost_flatMap]
  have eachTransition :
      ∀ transition ∈ sequence.transitions,
        traceBitCost transition.charges ≤
          principalScalarTransitionBitOperationBound operandBits +
            (matrixMultiplicationBitOperationBound n
                (rowTraceTransformBitLengthBound
                  n forwardBits inverseBits)
                matrixBits +
              2 * matrixMultiplicationBitOperationBound n
                (rowTraceTransformBitLengthBound
                  n forwardBits inverseBits)
                (rowTraceTransformBitLengthBound
                  n forwardBits inverseBits)) :=
    fun transition member =>
      principalTransition_cost_le sequence transition member
        allWidths matrixWidth forwardWidth inverseWidth
  have sumBoundAux :
      ∀ transitions : List (PrincipalTransitionExecution n),
        (∀ transition ∈ transitions,
          traceBitCost transition.charges ≤
            principalScalarTransitionBitOperationBound operandBits +
              (matrixMultiplicationBitOperationBound n
                  (rowTraceTransformBitLengthBound
                    n forwardBits inverseBits)
                  matrixBits +
                2 * matrixMultiplicationBitOperationBound n
                  (rowTraceTransformBitLengthBound
                    n forwardBits inverseBits)
                  (rowTraceTransformBitLengthBound
                    n forwardBits inverseBits))) →
        (transitions.map
          fun transition ↦ traceBitCost transition.charges).sum ≤
            transitions.length *
              (principalScalarTransitionBitOperationBound operandBits +
                (matrixMultiplicationBitOperationBound n
                    (rowTraceTransformBitLengthBound
                      n forwardBits inverseBits)
                    matrixBits +
                  2 * matrixMultiplicationBitOperationBound n
                    (rowTraceTransformBitLengthBound
                      n forwardBits inverseBits)
                    (rowTraceTransformBitLengthBound
                      n forwardBits inverseBits))) := by
    intro transitions bounds
    induction transitions with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have headBound := bounds head (by simp)
        have tailBound := ih fun transition member =>
          bounds transition (by simp [member])
        rw [Nat.add_mul, one_mul]
        omega
  have sumBound :
      (sequence.transitions.map
        fun transition ↦ traceBitCost transition.charges).sum ≤
          sequence.transitions.length *
            (principalScalarTransitionBitOperationBound operandBits +
              (matrixMultiplicationBitOperationBound n
                  (rowTraceTransformBitLengthBound
                    n forwardBits inverseBits)
                  matrixBits +
                2 * matrixMultiplicationBitOperationBound n
                  (rowTraceTransformBitLengthBound
                    n forwardBits inverseBits)
                  (rowTraceTransformBitLengthBound
                    n forwardBits inverseBits))) :=
    sumBoundAux sequence.transitions eachTransition
  rw [sequence.steps_eq_transitions, List.length_map]
  unfold rowTraceDenseBitOperationBound
  dsimp only
  rw [Nat.mul_add] at sumBound
  exact sumBound

public theorem principalMultiplierPrefixPolynomialBitLengthBound_mono
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    Principal.principalMultiplierPrefixPolynomialBitLengthBound
        dimension smaller ≤
      Principal.principalMultiplierPrefixPolynomialBitLengthBound
        dimension larger := by
  cases dimension with
  | zero => rfl
  | succ order =>
      simp only [Principal.principalMultiplierPrefixPolynomialBitLengthBound]
      have polynomialLe :=
        Principal.principalPolynomialBitLengthBound_mono_right
          (order + 1) hle
      gcongr

public theorem principalInversePrefixPolynomialBitLengthBound_mono
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    Principal.principalInversePrefixPolynomialBitLengthBound
        dimension smaller ≤
      Principal.principalInversePrefixPolynomialBitLengthBound
        dimension larger := by
  cases dimension with
  | zero => rfl
  | succ order =>
      simp only [Principal.principalInversePrefixPolynomialBitLengthBound]
      have polynomialLe :=
        Principal.principalPolynomialBitLengthBound_mono_right
          (order + 1) hle
      gcongr

public theorem principalScalarTransitionBitOperationBound_mono
    {smaller larger : Nat} (hle : smaller ≤ larger) :
    principalScalarTransitionBitOperationBound smaller ≤
      principalScalarTransitionBitOperationBound larger := by
  unfold principalScalarTransitionBitOperationBound
    Principal.boundedIntXGCDUniformBitOperationBound
    Principal.integerDivModBitOperationBound
    boundedXGCDStepCostBound boundedXGCDEuclideanUpdateCostBound
    boundedXGCDReductionCostBound
    boundedXGCDCoefficientBitLengthBound
    boundedXGCDRawCoefficientBitLengthBound divisionCostForBitLengths
    multiplicationCostForBitLengths additionCostForBitLengths
  dsimp only
  gcongr
  all_goals
    unfold boundedXGCDCoefficientBitLengthBound
    omega

/-- Closed bound for the actual scalar and three-matrix principal replay. -/
@[expose] public def principalExecutionBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  let operandBits :=
    Principal.principalPolynomialBitLengthBound dimension inputBits
  dimension ^ 3 * principalScalarTransitionBitOperationBound operandBits +
    rowTraceDenseBitOperationBound dimension (dimension ^ 3)
      operandBits
      (Principal.principalMultiplierPrefixPolynomialBitLengthBound
        dimension inputBits)
      (Principal.principalInversePrefixPolynomialBitLengthBound
        dimension inputBits)

public theorem principalExecutionBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    principalExecutionBitOperationBound dimension smaller ≤
      principalExecutionBitOperationBound dimension larger := by
  unfold principalExecutionBitOperationBound
  let smallOperand :=
    Principal.principalPolynomialBitLengthBound dimension smaller
  let largeOperand :=
    Principal.principalPolynomialBitLengthBound dimension larger
  have operandLe : smallOperand ≤ largeOperand :=
    Principal.principalPolynomialBitLengthBound_mono_right dimension hle
  exact Nat.add_le_add
    (Nat.mul_le_mul_left (dimension ^ 3) <|
      principalScalarTransitionBitOperationBound_mono operandLe)
    (rowTraceDenseBitOperationBound_mono dimension le_rfl operandLe
      (principalMultiplierPrefixPolynomialBitLengthBound_mono dimension hle)
      (principalInversePrefixPolynomialBitLengthBound_mono dimension hle))

/-- Instrumented principal execution value. -/
public structure PrincipalExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) where
  B : Matrix (Fin n) (Fin n) Int
  U : Matrix (Fin n) (Fin n) Int
  Uinv : Matrix (Fin n) (Fin n) Int
  transitions : List (PrincipalTransitionExecution n)
  charges : List KannanBachemArithmeticCharge
  replay :
    B = (principalRun A).steps.replay A
  value_refinement :
    B = (principalRun A).matrix ∧
      U = (principalRun A).steps.accumulator ∧
      Uinv = (principalRun A).steps.inverseAccumulator
  equation : U * A = B
  inverse_identities : Uinv * U = 1 ∧ U * Uinv = 1
  trace_wellFormed : ArithmeticChargeListWellFormed charges
  coverage :
    PrincipalExecutionCoverage { B := A, U := 1, Uinv := 1 }
      { B, U, Uinv } transitions charges

/--
Run the stateful principal transition schedule.  `Principal.compute` appears
only in the refinement proof.
-/
@[expose] public def principalExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) : PrincipalExecution A := by
  let sequence := principalTransitionSequence A
  have refinement := principalTransitionSequence_value A
  exact
    { B := sequence.state.B
      U := sequence.state.U
      Uinv := sequence.state.Uinv
      transitions := sequence.transitions
      charges := sequence.charges
      replay := by
        rw [sequence.B_eq_replay, refinement.2.1]
      value_refinement := by
        exact
          ⟨refinement.1,
            by rw [sequence.U_eq_accumulator, refinement.2.1],
            by rw [sequence.Uinv_eq_inverseAccumulator,
              refinement.2.1]⟩
      equation := sequence.equation
      inverse_identities := sequence.inverse_identities
      trace_wellFormed := sequence.trace_wellFormed
      coverage := sequence.coverage }

public theorem principalExecution_cost_le_of_ready {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int)
    (ready : Principal.PrincipalReady A) :
    traceBitCost (principalExecution A).charges ≤
      principalExecutionBitOperationBound n (matrixBitLength A) := by
  let sequence := principalTransitionSequence A
  let operandBits :=
    Principal.principalPolynomialBitLengthBound n (matrixBitLength A)
  let forwardBits :=
    Principal.principalMultiplierPrefixPolynomialBitLengthBound
      n (matrixBitLength A)
  let inverseBits :=
    Principal.principalInversePrefixPolynomialBitLengthBound
      n (matrixBitLength A)
  have refinement := principalTransitionSequence_value A
  have allWidths : ∀ event ∈ sequence.events,
      event.operandBitLength ≤ operandBits := by
    intro event member
    rw [refinement.2.2] at member
    exact
      (event.operandBitLength_le_list_of_mem
        (principalRun A).arithmeticEvents member).trans
        (principalArithmeticOperandBitLength_le_polynomial_of_ready A ready)
  have matrixWidth :
      sequence.steps.intermediateMatrixBitLength A ≤ operandBits := by
    rw [refinement.2.1]
    simpa only [operandBits, principalIntermediateMatrixBitLength,
      principalIntermediateMatrixHeight,
      RowTrace.intermediateMatrixBitLength] using
      principalIntermediateMatrixBitLength_le_polynomial_of_ready A ready
  have forwardWidth :
      sequence.steps.intermediateMultiplierBitLength ≤ forwardBits := by
    rw [refinement.2.1]
    simpa only [forwardBits, principalIntermediateMultiplierBitLength,
      principalIntermediateMultiplierHeight,
      RowTrace.intermediateMultiplierBitLength] using
      principalIntermediateMultiplierBitLength_le_polynomial_of_ready A ready
  have inverseWidth :
      sequence.steps.intermediateInverseMultiplierBitLength ≤ inverseBits := by
    rw [refinement.2.1]
    simpa only [inverseBits, principalIntermediateInverseBitLength,
      principalIntermediateInverseHeight,
      RowTrace.intermediateInverseMultiplierBitLength] using
      principalIntermediateInverseBitLength_le_polynomial_of_ready A ready
  have actualCost :=
    principalTransitionSequence_cost_le sequence
      allWidths matrixWidth forwardWidth inverseWidth
  have lengthBound : sequence.steps.length ≤ n ^ 3 := by
    rw [refinement.2.1]
    exact principalRun_steps_length_le A
  have closed :
      sequence.steps.length *
            principalScalarTransitionBitOperationBound operandBits +
          rowTraceDenseBitOperationBound n sequence.steps.length
            operandBits forwardBits inverseBits ≤
        n ^ 3 * principalScalarTransitionBitOperationBound operandBits +
          rowTraceDenseBitOperationBound n (n ^ 3)
            operandBits forwardBits inverseBits :=
    Nat.add_le_add
      (Nat.mul_le_mul_right _ lengthBound)
      (rowTraceDenseBitOperationBound_mono n lengthBound
        le_rfl le_rfl le_rfl)
  change traceBitCost sequence.charges ≤
    principalExecutionBitOperationBound n (matrixBitLength A)
  exact actualCost.trans (by
    unfold principalExecutionBitOperationBound
    simpa only [operandBits, forwardBits, inverseBits] using closed)

public theorem principalExecution_replay {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    (principalExecution A).B =
      (principalRun A).steps.replay A :=
  (principalExecution A).replay

public theorem principalExecution_value {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    (principalExecution A).B = (principalRun A).matrix ∧
      (principalExecution A).U =
        (principalRun A).steps.accumulator ∧
      (principalExecution A).Uinv =
        (principalRun A).steps.inverseAccumulator :=
  (principalExecution A).value_refinement

public theorem principalExecution_trace_wellFormed {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    ArithmeticChargeListWellFormed (principalExecution A).charges :=
  (principalExecution A).trace_wellFormed

public theorem principalExecution_transitionAdequate {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    PrincipalExecutionCoverage { B := A, U := 1, Uinv := 1 }
      { B := (principalExecution A).B
        U := (principalExecution A).U
        Uinv := (principalExecution A).Uinv }
      (principalExecution A).transitions
      (principalExecution A).charges :=
  (principalExecution A).coverage

public theorem principalExecution_chargeComplete {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    (principalExecution A).charges =
      (principalExecution A).transitions.flatMap
        PrincipalTransitionExecution.charges :=
  (principalExecution A).coverage.charges_eq_flatten

public theorem principalExecution_singleOwner {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    ∃ transitions : List (PrincipalTransitionExecution n),
      transitions.map PrincipalTransitionExecution.step =
          (principalRun A).steps ∧
        (principalExecution A).charges =
          transitions.flatMap PrincipalTransitionExecution.charges := by
  let sequence := principalTransitionSequence A
  refine ⟨sequence.transitions, ?_, ?_⟩
  · rw [← sequence.steps_eq_transitions,
      (principalTransitionSequence_value A).2.1]
  · exact sequence.coverage.charges_eq_flatten

public theorem principalExecution_bezoutRun_shared {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    ∀ transition ∈ (principalExecution A).transitions,
      transition.BezoutRunShared :=
  (principalExecution A).coverage.transitions_shared

/-- Macro count is always the fold of the execution's single charge list. -/
@[expose] public def principalArithmeticOperationCount {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) : ArithmeticOperationCount :=
  traceOperationCount (principalExecution A).charges

public theorem principalArithmeticOperationCount_eq_trace {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    principalArithmeticOperationCount A =
      traceOperationCount (principalExecution A).charges :=
  rfl

/-- Standalone divisions are likewise read from the same macro fold. -/
@[expose] public def principalStandaloneDivModCalls {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) : Nat :=
  (traceOperationCount (principalExecution A).charges).standaloneDivModCalls

public theorem principalStandaloneDivModCalls_eq_trace {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    principalStandaloneDivModCalls A =
      (traceOperationCount
        (principalExecution A).charges).standaloneDivModCalls :=
  rfl

end NormalForms.Research.KannanBachem
