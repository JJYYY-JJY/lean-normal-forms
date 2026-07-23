/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Dense
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

/-- A small container for an already checked list of arithmetic leaves. -/
public structure ArithmeticLeafExecution where
  charges : List KannanBachemArithmeticCharge
  trace_wellFormed : ArithmeticChargeListWellFormed charges

/-- Charge the scalar primitives owned by one principal transition. -/
@[expose] public def principalEventChargeExecution
    (dimension : Nat) (event : PrincipalArithmeticEvent)
    (valid : event.Valid dimension) : ArithmeticLeafExecution := by
  cases event with
  | xgcd pivot target left right =>
      let location := ArithmeticChargeLocation.ofIndices .bezoutBlock
        dimension [pivot, target] (by
          intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact valid.1.trans valid.2
          · exact valid.2)
      let encodedLeft := SignMagnitude.ofInt left
      let encodedRight := SignMagnitude.ofInt right
      let xgcdRun := boundedXGCDWithCost encodedLeft encodedRight
      let zeroRun := isZeroWithCost xgcdRun.value.gcd
      let xgcdCharge :=
        KannanBachemArithmeticCharge.boundedXGCDOfRun
          location encodedLeft encodedRight xgcdRun rfl
      let zeroCharge :=
        KannanBachemArithmeticCharge.zeroTestOfRun
          location xgcdRun.value.gcd zeroRun rfl
      if zero : zeroRun.value then
        exact
          { charges := [xgcdCharge, zeroCharge]
            trace_wellFormed := by
              simp only [ArithmeticChargeListWellFormed,
                List.forall_cons]
              exact
                ⟨KannanBachemArithmeticCharge.boundedXGCDOfRun_wellFormed
                    location encodedLeft encodedRight xgcdRun rfl,
                  KannanBachemArithmeticCharge.zeroTestOfRun_wellFormed
                    location xgcdRun.value.gcd zeroRun rfl,
                  by simp⟩ }
      else
        let leftDivision := divModWithCost encodedLeft xgcdRun.value.gcd
        let rightDivision := divModWithCost encodedRight xgcdRun.value.gcd
        let leftDivisionCharge :=
          KannanBachemArithmeticCharge.divModOfRun location
            .bezoutLeftExact encodedLeft xgcdRun.value.gcd
            leftDivision rfl trivial
        let rightDivisionCharge :=
          KannanBachemArithmeticCharge.divModOfRun location
            .bezoutRightExact encodedRight xgcdRun.value.gcd
            rightDivision rfl trivial
        exact
          { charges :=
              [xgcdCharge, zeroCharge, leftDivisionCharge, rightDivisionCharge]
            trace_wellFormed := by
              simp only [ArithmeticChargeListWellFormed,
                List.forall_cons]
              exact
                ⟨KannanBachemArithmeticCharge.boundedXGCDOfRun_wellFormed
                    location encodedLeft encodedRight xgcdRun rfl,
                  KannanBachemArithmeticCharge.zeroTestOfRun_wellFormed
                    location xgcdRun.value.gcd zeroRun rfl,
                  KannanBachemArithmeticCharge.divModOfRun_wellFormed location
                    .bezoutLeftExact encodedLeft xgcdRun.value.gcd
                    leftDivision rfl trivial,
                  KannanBachemArithmeticCharge.divModOfRun_wellFormed location
                    .bezoutRightExact encodedRight xgcdRun.value.gcd
                    rightDivision rfl trivial,
                  by simp⟩ }
  | divMod source destination numerator divisor =>
      let location := ArithmeticChargeLocation.ofIndices .hnfReduceAbove
        dimension [source, destination] (by
          intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact valid.1.trans valid.2
          · exact valid.2)
      let encodedNumerator := SignMagnitude.ofInt numerator
      let encodedDivisor := SignMagnitude.ofInt divisor
      let run := divModWithCost encodedNumerator encodedDivisor
      let charge := KannanBachemArithmeticCharge.divModOfRun
        location .hnfReduceAbove encodedNumerator encodedDivisor run rfl trivial
      exact
        { charges := [charge]
          trace_wellFormed := by
            simp only [ArithmeticChargeListWellFormed,
              List.forall_cons]
            exact
              ⟨KannanBachemArithmeticCharge.divModOfRun_wellFormed location
                  .hnfReduceAbove encodedNumerator encodedDivisor run rfl trivial,
                by simp⟩ }
  | normalize row value =>
      let location := ArithmeticChargeLocation.ofIndices .scalar
        dimension [row] (by
          intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          subst index
          exact valid)
      let encoded := SignMagnitude.ofInt value
      let run := normalizeWithCost encoded
      let charge := KannanBachemArithmeticCharge.normalizationOfRun
        location encoded run rfl
      exact
        { charges := [charge]
          trace_wellFormed := by
            simp only [ArithmeticChargeListWellFormed,
              List.forall_cons]
            exact
              ⟨KannanBachemArithmeticCharge.normalizationOfRun_wellFormed
                  location encoded run rfl,
                by simp⟩ }

/-- Charge an execution-ordered list of principal scalar events. -/
@[expose] public def principalEventListChargeExecution
    (dimension : Nat) :
    (events : List PrincipalArithmeticEvent) →
      events.Forall (PrincipalArithmeticEvent.Valid dimension) →
        ArithmeticLeafExecution
  | [], _ =>
      { charges := []
        trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }
  | event :: tail, valid => by
      have valid' := valid
      rw [List.forall_cons] at valid'
      let head := principalEventChargeExecution dimension event
        valid'.1
      let rest := principalEventListChargeExecution dimension tail
        valid'.2
      exact
        { charges := head.charges ++ rest.charges
          trace_wellFormed :=
            head.trace_wellFormed.append rest.trace_wellFormed }

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

private theorem principalEventChargeExecution_cost_le
    (dimension operandBits : Nat) (event : PrincipalArithmeticEvent)
    (valid : event.Valid dimension)
    (operandBound : event.operandBitLength ≤ operandBits) :
    traceBitCost
        (principalEventChargeExecution dimension event valid).charges ≤
      principalScalarTransitionBitOperationBound operandBits := by
  cases event with
  | xgcd pivot target left right =>
      let encodedLeft := SignMagnitude.ofInt left
      let encodedRight := SignMagnitude.ofInt right
      let xgcdRun := boundedXGCDWithCost encodedLeft encodedRight
      have leftIntWidth : Nat.size left.natAbs ≤ operandBits :=
        (Nat.size_le_size (le_max_left left.natAbs right.natAbs)).trans
          operandBound
      have rightIntWidth : Nat.size right.natAbs ≤ operandBits :=
        (Nat.size_le_size (le_max_right left.natAbs right.natAbs)).trans
          operandBound
      have leftWidth : encodedLeft.bitLength ≤ operandBits := by
        simpa only [encodedLeft,
          SignMagnitude.bitLength_eq_natSize_natAbs,
          SignMagnitude.value_ofInt] using leftIntWidth
      have rightWidth : encodedRight.bitLength ≤ operandBits := by
        simpa only [encodedRight,
          SignMagnitude.bitLength_eq_natSize_natAbs,
          SignMagnitude.value_ofInt] using rightIntWidth
      have gcdWidth : xgcdRun.value.gcd.bitLength ≤ operandBits :=
        (boundedXGCD_gcd_bitLength_le_max encodedLeft encodedRight).trans <|
          max_le leftWidth rightWidth
      have xgcdCost :
          xgcdRun.cost ≤
            Principal.boundedIntXGCDUniformBitOperationBound operandBits := by
        simpa only [xgcdRun, encodedLeft, encodedRight,
          Principal.boundedIntXGCDBitOperationCost] using
          Principal.boundedIntXGCDBitOperationCost_le_uniform
            left right operandBits leftIntWidth rightIntWidth
      have leftDivision :
          (divModWithCost encodedLeft xgcdRun.value.gcd).cost ≤
            Principal.integerDivModBitOperationBound operandBits := by
        exact (divModWithCost_cost_le _ _).trans <|
          Internal.divModBitOperationBound_le_lengths _ _
            operandBits operandBits leftWidth gcdWidth
      have rightDivision :
          (divModWithCost encodedRight xgcdRun.value.gcd).cost ≤
            Principal.integerDivModBitOperationBound operandBits := by
        exact (divModWithCost_cost_le _ _).trans <|
          Internal.divModBitOperationBound_le_lengths _ _
            operandBits operandBits rightWidth gcdWidth
      have xgcdCost' :
          (boundedXGCDWithCost
              (SignMagnitude.ofInt left) (SignMagnitude.ofInt right)).cost ≤
            Principal.boundedIntXGCDUniformBitOperationBound operandBits := by
        simpa only [xgcdRun, encodedLeft, encodedRight] using xgcdCost
      have leftDivision' :
          (divModWithCost (SignMagnitude.ofInt left)
              (boundedXGCDWithCost
                (SignMagnitude.ofInt left)
                (SignMagnitude.ofInt right)).value.gcd).cost ≤
            Principal.integerDivModBitOperationBound operandBits := by
        simpa only [xgcdRun, encodedLeft, encodedRight] using leftDivision
      have rightDivision' :
          (divModWithCost (SignMagnitude.ofInt right)
              (boundedXGCDWithCost
                (SignMagnitude.ofInt left)
                (SignMagnitude.ofInt right)).value.gcd).cost ≤
            Principal.integerDivModBitOperationBound operandBits := by
        simpa only [xgcdRun, encodedLeft, encodedRight] using rightDivision
      simp only [principalEventChargeExecution]
      split <;>
        simp [traceBitCost,
          KannanBachemArithmeticCharge.boundedXGCDOfRun,
          KannanBachemArithmeticCharge.zeroTestOfRun,
          KannanBachemArithmeticCharge.divModOfRun,
          KannanBachemArithmeticCharge.bitCost,
          principalScalarTransitionBitOperationBound] <;>
        omega
  | divMod source destination numerator divisor =>
      have numeratorWidth : Nat.size numerator.natAbs ≤ operandBits :=
        (Nat.size_le_size
          (le_max_left numerator.natAbs divisor.natAbs)).trans operandBound
      have divisorWidth : Nat.size divisor.natAbs ≤ operandBits :=
        (Nat.size_le_size
          (le_max_right numerator.natAbs divisor.natAbs)).trans operandBound
      have divisionCost := Principal.integerDivModBitOperationCost_le
        numerator divisor operandBits numeratorWidth divisorWidth
      simpa [principalEventChargeExecution, traceBitCost,
        KannanBachemArithmeticCharge.divModOfRun,
        KannanBachemArithmeticCharge.bitCost,
        principalScalarTransitionBitOperationBound,
        Principal.integerDivModBitOperationCost] using
        (show Principal.integerDivModBitOperationCost numerator divisor ≤
          principalScalarTransitionBitOperationBound operandBits by
            unfold principalScalarTransitionBitOperationBound
            omega)
  | normalize row value =>
      simp [principalEventChargeExecution, traceBitCost,
        KannanBachemArithmeticCharge.normalizationOfRun,
        KannanBachemArithmeticCharge.bitCost, normalizeWithCost,
        principalScalarTransitionBitOperationBound]

public theorem principalEventListChargeExecution_cost_le
    (dimension operandBits : Nat) (events : List PrincipalArithmeticEvent)
    (valid : events.Forall (PrincipalArithmeticEvent.Valid dimension))
    (allWidths : ∀ event ∈ events,
      event.operandBitLength ≤ operandBits) :
    traceBitCost
        (principalEventListChargeExecution dimension events valid).charges ≤
      events.length * principalScalarTransitionBitOperationBound operandBits := by
  induction events with
  | nil =>
      simp [principalEventListChargeExecution, traceBitCost]
  | cons head tail ih =>
      rw [List.forall_cons] at valid
      simp only [principalEventListChargeExecution, traceBitCost_append]
      have headCost := principalEventChargeExecution_cost_le
        dimension operandBits head valid.1 (allWidths head (by simp))
      have tailCost := ih valid.2 fun event member =>
        allWidths event (by simp [member])
      rw [List.length_cons, Nat.add_mul, one_mul]
      omega

/-- Dense replay of a primitive row trace, carrying both inverse identities. -/
public structure RowTraceExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int)
    (steps : RowTrace Int n) where
  B : Matrix (Fin n) (Fin n) Int
  U : Matrix (Fin n) (Fin n) Int
  Uinv : Matrix (Fin n) (Fin n) Int
  charges : List KannanBachemArithmeticCharge
  B_eq_replay : B = steps.replay A
  U_eq_accumulator : U = steps.accumulator
  Uinv_eq_inverseAccumulator : Uinv = steps.inverseAccumulator
  inverse_identities : Uinv * U = 1 ∧ U * Uinv = 1
  equation : U * A = B
  trace_wellFormed : ArithmeticChargeListWellFormed charges

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

/-- Replay each row step through three dense products for `B`, `U`, and `U⁻¹`. -/
@[expose] public def rowTraceExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    (steps : RowTrace Int n) → RowTraceExecution A steps
  | [] =>
      { B := A
        U := 1
        Uinv := 1
        charges := []
        B_eq_replay := by rfl
        U_eq_accumulator := by rfl
        Uinv_eq_inverseAccumulator := by rfl
        inverse_identities := by constructor <;> simp
        equation := NormalForms.Matrix.Constructive.one_mul A
        trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }
  | step :: tail => by
      let matrixRun := matrixProductExecution step.forward A
      let rest := rowTraceExecution matrixRun.value tail
      let forwardRun := matrixProductExecution rest.U step.forward
      let inverseRun := matrixProductExecution step.backward rest.Uinv
      have matrixValue : matrixRun.value = step.forward * A :=
        matrixProductExecution_value _ _
      have forwardValue : forwardRun.value = rest.U * step.forward :=
        matrixProductExecution_value _ _
      have inverseValue : inverseRun.value = step.backward * rest.Uinv :=
        matrixProductExecution_value _ _
      let charges := matrixRun.charges ++
        (rest.charges ++ (forwardRun.charges ++ inverseRun.charges))
      exact
        { B := rest.B
          U := forwardRun.value
          Uinv := inverseRun.value
          charges
          B_eq_replay := by
            rw [rest.B_eq_replay, RowTrace.replay, matrixValue]
            rfl
          U_eq_accumulator := by
            rw [forwardValue, rest.U_eq_accumulator]
            rfl
          Uinv_eq_inverseAccumulator := by
            rw [inverseValue, rest.Uinv_eq_inverseAccumulator]
            rfl
          inverse_identities := by
            rw [inverseValue, forwardValue, rest.U_eq_accumulator,
              rest.Uinv_eq_inverseAccumulator]
            exact ⟨RowTrace.inverse_mul_accumulator (step :: tail),
              RowTrace.accumulator_mul_inverse (step :: tail)⟩
          equation := by
            rw [forwardValue, rest.U_eq_accumulator, rest.B_eq_replay,
              RowTrace.replay_eq_accumulator_mul, matrixValue]
            simp only [Matrix.mul_assoc]
          trace_wellFormed := by
            apply matrixRun.trace_wellFormed.append
            apply rest.trace_wellFormed.append
            exact forwardRun.trace_wellFormed.append
              inverseRun.trace_wellFormed }

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

private theorem fullAccumulator_bitLength_le {n : Nat}
    (steps : RowTrace Int n) :
    matrixBitLength steps.accumulator ≤
      steps.intermediateMultiplierBitLength := by
  exact Nat.size_le_size
    steps.accumulator_height_le_intermediateMultiplierHeight

private theorem fullInverse_bitLength_le {n : Nat}
    (steps : RowTrace Int n) :
    matrixBitLength steps.inverseAccumulator ≤
      steps.intermediateInverseMultiplierBitLength := by
  exact Nat.size_le_size
    steps.inverseAccumulator_height_le_intermediateInverseMultiplierHeight

private theorem rowTraceExecution_cost_le_suffix {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int)
    (before suffix : RowTrace Int n) :
    let steps := before ++ suffix
    traceBitCost (rowTraceExecution (before.replay A) suffix).charges ≤
      suffix.length *
        (matrixMultiplicationBitOperationBound n
            (rowTraceTransformBitLengthBound n
              steps.intermediateMultiplierBitLength
              steps.intermediateInverseMultiplierBitLength)
            (steps.intermediateMatrixBitLength A) +
          2 * matrixMultiplicationBitOperationBound n
            (rowTraceTransformBitLengthBound n
              steps.intermediateMultiplierBitLength
              steps.intermediateInverseMultiplierBitLength)
            (rowTraceTransformBitLengthBound n
              steps.intermediateMultiplierBitLength
              steps.intermediateInverseMultiplierBitLength)) := by
  induction suffix generalizing before with
  | nil =>
      simp [rowTraceExecution, traceBitCost]
  | cons step tail ih =>
      let steps := before ++ step :: tail
      let nextBefore := before ++ [step]
      let forwardBits := steps.intermediateMultiplierBitLength
      let inverseBits := steps.intermediateInverseMultiplierBitLength
      let matrixBits := steps.intermediateMatrixBitLength A
      let transformBits :=
        rowTraceTransformBitLengthBound n forwardBits inverseBits
      have nextSplit : nextBefore ++ tail = steps := by
        simp [nextBefore, steps, List.append_assoc]
      have beforeForward :
          matrixBitLength before.accumulator ≤ forwardBits := by
        simpa only [steps, forwardBits] using
          prefixAccumulator_bitLength_le before (step :: tail)
      have beforeInverse :
          matrixBitLength before.inverseAccumulator ≤ inverseBits := by
        simpa only [steps, inverseBits] using
          prefixInverse_bitLength_le before (step :: tail)
      have nextForward :
          matrixBitLength nextBefore.accumulator ≤ forwardBits := by
        have bound := prefixAccumulator_bitLength_le nextBefore tail
        simpa only [nextSplit, forwardBits] using bound
      have nextInverse :
          matrixBitLength nextBefore.inverseAccumulator ≤ inverseBits := by
        have bound := prefixInverse_bitLength_le nextBefore tail
        simpa only [nextSplit, inverseBits] using bound
      have stepForwardIdentity :
          step.forward =
            nextBefore.accumulator * before.inverseAccumulator := by
        simp [nextBefore, RowTrace.accumulator_append,
          RowTrace.accumulator, Matrix.mul_assoc,
          RowTrace.accumulator_mul_inverse]
      have stepBackwardIdentity :
          step.backward =
            before.accumulator * nextBefore.inverseAccumulator := by
        rw [show nextBefore.inverseAccumulator =
            before.inverseAccumulator * step.backward by
          simp [nextBefore, RowTrace.inverseAccumulator_append,
            RowTrace.inverseAccumulator]]
        rw [← Matrix.mul_assoc,
          RowTrace.accumulator_mul_inverse,
          NormalForms.Matrix.Constructive.one_mul]
      have stepForward :
          matrixBitLength step.forward ≤ transformBits := by
        rw [stepForwardIdentity]
        exact (matrix_mul_bitLength_le _ _).trans (by
          unfold transformBits rowTraceTransformBitLengthBound
          omega)
      have stepBackward :
          matrixBitLength step.backward ≤ transformBits := by
        rw [stepBackwardIdentity]
        exact (matrix_mul_bitLength_le _ _).trans (by
          unfold transformBits rowTraceTransformBitLengthBound
          omega)
      have currentMatrix :
          matrixBitLength (before.replay A) ≤ matrixBits := by
        simpa only [steps, matrixBits] using
          prefixReplay_bitLength_le A before (step :: tail)
      have fullForward :
          matrixBitLength steps.accumulator ≤ forwardBits := by
        simpa only [forwardBits] using fullAccumulator_bitLength_le steps
      have fullInverse :
          matrixBitLength steps.inverseAccumulator ≤ inverseBits := by
        simpa only [inverseBits] using fullInverse_bitLength_le steps
      have tailForwardIdentity :
          RowTrace.accumulator tail =
            steps.accumulator * nextBefore.inverseAccumulator := by
        rw [← nextSplit, RowTrace.accumulator_append]
        simp only [Matrix.mul_assoc]
        rw [RowTrace.accumulator_mul_inverse, Matrix.mul_one]
      have tailInverseIdentity :
          RowTrace.inverseAccumulator tail =
            nextBefore.accumulator * steps.inverseAccumulator := by
        rw [← nextSplit, RowTrace.inverseAccumulator_append]
        rw [← Matrix.mul_assoc,
          RowTrace.accumulator_mul_inverse,
          NormalForms.Matrix.Constructive.one_mul]
      have tailForward :
          matrixBitLength (RowTrace.accumulator tail) ≤ transformBits := by
        rw [tailForwardIdentity]
        exact (matrix_mul_bitLength_le _ _).trans (by
          unfold transformBits rowTraceTransformBitLengthBound
          omega)
      have tailInverse :
          matrixBitLength (RowTrace.inverseAccumulator tail) ≤ transformBits := by
        rw [tailInverseIdentity]
        exact (matrix_mul_bitLength_le _ _).trans (by
          unfold transformBits rowTraceTransformBitLengthBound
          omega)
      let matrixRun :=
        matrixProductExecution step.forward (before.replay A)
      have matrixValue :
          matrixRun.value = nextBefore.replay A := by
        rw [matrixProductExecution_value]
        simp [nextBefore, RowTrace.replay]
      have restCost := ih nextBefore
      rw [nextSplit] at restCost
      have restCost' :
          traceBitCost
              (rowTraceExecution (nextBefore.replay A) tail).charges ≤
            tail.length *
              (matrixMultiplicationBitOperationBound
                  n transformBits matrixBits +
                2 * matrixMultiplicationBitOperationBound
                  n transformBits transformBits) := by
        simpa only [transformBits, matrixBits, forwardBits,
          inverseBits] using restCost
      have matrixCost :
          matrixMultiplicationBitOperationCost
              step.forward (before.replay A) ≤
            matrixMultiplicationBitOperationBound
              n transformBits matrixBits :=
        matrixMultiplicationBitOperationCost_le _ _
          stepForward currentMatrix
      have forwardCost :
          matrixMultiplicationBitOperationCost
              (rowTraceExecution matrixRun.value tail).U step.forward ≤
            matrixMultiplicationBitOperationBound
              n transformBits transformBits := by
        apply matrixMultiplicationBitOperationCost_le
        · rw [(rowTraceExecution matrixRun.value tail).U_eq_accumulator]
          exact tailForward
        · exact stepForward
      have inverseCost :
          matrixMultiplicationBitOperationCost step.backward
              (rowTraceExecution matrixRun.value tail).Uinv ≤
            matrixMultiplicationBitOperationBound
              n transformBits transformBits := by
        apply matrixMultiplicationBitOperationCost_le
        · exact stepBackward
        · rw [(rowTraceExecution matrixRun.value tail).Uinv_eq_inverseAccumulator]
          exact tailInverse
      rw [rowTraceExecution]
      dsimp only
      simp only [traceBitCost_append, matrixProductExecution_cost_eq]
      rw [matrixValue]
      rw [matrixValue] at forwardCost inverseCost
      change
        matrixMultiplicationBitOperationCost
              step.forward (before.replay A) +
            (traceBitCost
                (rowTraceExecution (nextBefore.replay A) tail).charges +
              (matrixMultiplicationBitOperationCost
                  (rowTraceExecution (nextBefore.replay A) tail).U
                    step.forward +
                matrixMultiplicationBitOperationCost step.backward
                  (rowTraceExecution
                    (nextBefore.replay A) tail).Uinv)) ≤
          (step :: tail).length *
            (matrixMultiplicationBitOperationBound
                n transformBits matrixBits +
              2 * matrixMultiplicationBitOperationBound
                n transformBits transformBits)
      rw [List.length_cons, Nat.add_mul, one_mul]
      omega

public theorem rowTraceExecution_cost_le {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (steps : RowTrace Int n) :
    traceBitCost (rowTraceExecution A steps).charges ≤
      rowTraceDenseBitOperationBound n steps.length
        (steps.intermediateMatrixBitLength A)
        steps.intermediateMultiplierBitLength
        steps.intermediateInverseMultiplierBitLength := by
  simpa [rowTraceDenseBitOperationBound, RowTrace.replay] using
    rowTraceExecution_cost_le_suffix A [] steps

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
  chargeOwnership : ∀ charge ∈ charges, charge.WellFormed

/--
Run the principal transition schedule.  `Principal.compute` supplies only the
primitive control trace and operands; the three output matrices come from the
dense replay execution above.
-/
@[expose] public def principalExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) : PrincipalExecution A := by
  let schedule :=
    NormalForms.Research.KannanBachem.Hermite.principalSchedule A
  let scalar := principalEventListChargeExecution n schedule.arithmeticEvents
    schedule.validArithmeticEvents
  let replay := rowTraceExecution A schedule.steps
  let charges := scalar.charges ++ replay.charges
  have chargesWellFormed : ArithmeticChargeListWellFormed charges :=
    scalar.trace_wellFormed.append replay.trace_wellFormed
  exact
    { B := replay.B
      U := replay.U
      Uinv := replay.Uinv
      charges
      replay := by
        simpa only [principalRun, principalSchedule, schedule] using
          replay.B_eq_replay
      value_refinement := by
        have matrixEquality :
            replay.B = (principalRun A).matrix := by
          rw [replay.B_eq_replay]
          have scheduleSteps :
              schedule.steps = (principalRun A).steps := by
            rfl
          rw [scheduleSteps, principalRun_replay]
        exact
          ⟨matrixEquality,
            by simpa only [principalRun, principalSchedule, schedule] using
              replay.U_eq_accumulator,
            by simpa only [principalRun, principalSchedule, schedule] using
              replay.Uinv_eq_inverseAccumulator⟩
      equation := replay.equation
      inverse_identities := replay.inverse_identities
      trace_wellFormed := chargesWellFormed
      chargeOwnership :=
        List.forall_iff_forall_mem.mp chargesWellFormed }

public theorem principalExecution_cost_le_of_ready {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int)
    (ready : Principal.PrincipalReady A) :
    traceBitCost (principalExecution A).charges ≤
      principalExecutionBitOperationBound n (matrixBitLength A) := by
  let schedule :=
    NormalForms.Research.KannanBachem.Hermite.principalSchedule A
  let operandBits :=
    Principal.principalPolynomialBitLengthBound n (matrixBitLength A)
  have scheduleEvents :
      schedule.arithmeticEvents = (principalRun A).arithmeticEvents := rfl
  have scheduleSteps :
      schedule.steps = (principalRun A).steps := rfl
  have allWidths : ∀ event ∈ schedule.arithmeticEvents,
      event.operandBitLength ≤ operandBits := by
    intro event member
    rw [scheduleEvents] at member
    exact
      (event.operandBitLength_le_list_of_mem
        (principalRun A).arithmeticEvents member).trans
        (principalArithmeticOperandBitLength_le_polynomial_of_ready A ready)
  have scalarCost :=
    principalEventListChargeExecution_cost_le n operandBits
      schedule.arithmeticEvents schedule.validArithmeticEvents allWidths
  have scalarLength :
      schedule.arithmeticEvents.length ≤ n ^ 3 := by
    rw [scheduleEvents]
    exact principalRun_arithmeticEvents_length_le A
  have scalarClosed :
      traceBitCost
          (principalEventListChargeExecution n schedule.arithmeticEvents
            schedule.validArithmeticEvents).charges ≤
        n ^ 3 * principalScalarTransitionBitOperationBound operandBits :=
    scalarCost.trans <| Nat.mul_le_mul_right _ scalarLength
  have replayCost := rowTraceExecution_cost_le A schedule.steps
  have replayLength : schedule.steps.length ≤ n ^ 3 := by
    rw [scheduleSteps]
    exact principalRun_steps_length_le A
  have replayMatrix :
      schedule.steps.intermediateMatrixBitLength A ≤ operandBits := by
    rw [scheduleSteps]
    simpa only [operandBits, principalIntermediateMatrixBitLength,
      principalIntermediateMatrixHeight,
      RowTrace.intermediateMatrixBitLength] using
      principalIntermediateMatrixBitLength_le_polynomial_of_ready A ready
  have replayForward :
      schedule.steps.intermediateMultiplierBitLength ≤
        Principal.principalMultiplierPrefixPolynomialBitLengthBound
          n (matrixBitLength A) := by
    rw [scheduleSteps]
    simpa only [principalIntermediateMultiplierBitLength,
      principalIntermediateMultiplierHeight,
      RowTrace.intermediateMultiplierBitLength] using
      principalIntermediateMultiplierBitLength_le_polynomial_of_ready A ready
  have replayInverse :
      schedule.steps.intermediateInverseMultiplierBitLength ≤
        Principal.principalInversePrefixPolynomialBitLengthBound
          n (matrixBitLength A) := by
    rw [scheduleSteps]
    simpa only [principalIntermediateInverseBitLength,
      principalIntermediateInverseHeight,
      RowTrace.intermediateInverseMultiplierBitLength] using
      principalIntermediateInverseBitLength_le_polynomial_of_ready A ready
  have replayClosed :
      traceBitCost (rowTraceExecution A schedule.steps).charges ≤
        rowTraceDenseBitOperationBound n (n ^ 3) operandBits
          (Principal.principalMultiplierPrefixPolynomialBitLengthBound
            n (matrixBitLength A))
          (Principal.principalInversePrefixPolynomialBitLengthBound
            n (matrixBitLength A)) :=
    replayCost.trans <|
      rowTraceDenseBitOperationBound_mono n replayLength replayMatrix
        replayForward replayInverse
  change
    traceBitCost
        ((principalEventListChargeExecution n schedule.arithmeticEvents
          schedule.validArithmeticEvents).charges ++
          (rowTraceExecution A schedule.steps).charges) ≤
      principalExecutionBitOperationBound n (matrixBitLength A)
  rw [traceBitCost_append]
  unfold principalExecutionBitOperationBound
  dsimp only
  exact Nat.add_le_add scalarClosed replayClosed

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

public theorem principalExecution_chargeOwnership {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) :
    ∀ charge ∈ (principalExecution A).charges, charge.WellFormed :=
  (principalExecution A).chargeOwnership

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
