/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Charge
public import NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminantCost

/-! # Leaf-expanded Bird Determinant Execution -/

public section

namespace NormalForms.Research.KannanBachem

open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminant

/-- A determinant scalar together with its non-overlapping primitive leaves. -/
public structure DeterminantScalarExecution where
  value : SignMagnitude
  charges : List KannanBachemArithmeticCharge
  trace_wellFormed : ArithmeticChargeListWellFormed charges

@[expose] public def determinantAddExecution
    (left right : SignMagnitude) : DeterminantScalarExecution :=
  let run := addWithCost left right
  let charge := KannanBachemArithmeticCharge.additionOfRun
    .scalar left right run rfl
  { value := run.value
    charges := [charge]
    trace_wellFormed := by
      simp only [ArithmeticChargeListWellFormed, List.forall_cons]
      exact
        ⟨KannanBachemArithmeticCharge.additionOfRun_wellFormed
            .scalar left right run rfl,
          by simp⟩ }

@[expose] public def determinantMulExecution
    (left right : SignMagnitude) : DeterminantScalarExecution :=
  let run := mulWithCost left right
  let charge := KannanBachemArithmeticCharge.multiplicationOfRun
    .scalar left right run rfl
  { value := run.value
    charges := [charge]
    trace_wellFormed := by
      simp only [ArithmeticChargeListWellFormed, List.forall_cons]
      exact
        ⟨KannanBachemArithmeticCharge.multiplicationOfRun_wellFormed
            .scalar left right run rfl,
          by simp⟩ }

@[expose] public def determinantSumExecution :
    List SignMagnitude → DeterminantScalarExecution
  | [] =>
      { value := 0
        charges := []
        trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }
  | head :: tail =>
      let rest := determinantSumExecution tail
      let addition := determinantAddExecution head rest.value
      { value := addition.value
        charges := rest.charges ++ addition.charges
        trace_wellFormed :=
          rest.trace_wellFormed.append addition.trace_wellFormed }

public theorem determinantSumExecution_value (values : List SignMagnitude) :
    (determinantSumExecution values).value.value =
      (values.map SignMagnitude.value).sum := by
  induction values with
  | nil => simp [determinantSumExecution]
  | cons head tail ih =>
      simp only [determinantSumExecution, determinantAddExecution,
        addWithCost_value, List.map_cons, List.sum_cons]
      rw [ih]

@[expose] public def determinantDotExecution {ι : Type*}
    (indices : List ι) (left right : ι → SignMagnitude) :
    DeterminantScalarExecution :=
  match indices with
  | [] =>
      { value := 0
        charges := []
        trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }
  | index :: tail =>
      let product := determinantMulExecution (left index) (right index)
      let rest := determinantDotExecution tail left right
      let addition := determinantAddExecution product.value rest.value
      { value := addition.value
        charges := product.charges ++
          (rest.charges ++ addition.charges)
        trace_wellFormed := product.trace_wellFormed.append <|
          rest.trace_wellFormed.append addition.trace_wellFormed }

public theorem determinantDotExecution_value {ι : Type*}
    (indices : List ι) (left right : ι → SignMagnitude) :
    (determinantDotExecution indices left right).value.value =
      (indices.map fun index =>
        (left index).value * (right index).value).sum := by
  induction indices with
  | nil => simp [determinantDotExecution]
  | cons index tail ih =>
      simp only [determinantDotExecution, determinantMulExecution,
        determinantAddExecution, mulWithCost_value, addWithCost_value,
        List.map_cons, List.sum_cons]
      rw [ih]

public theorem determinantSumExecution_value_eq
    (values : List SignMagnitude) :
    (determinantSumExecution values).value = (sumWithCost values).value := by
  apply signMagnitude_value_injective
  rw [determinantSumExecution_value, sumWithCost_value]

public theorem determinantDotExecution_value_eq {ι : Type*}
    (indices : List ι) (left right : ι → SignMagnitude) :
    (determinantDotExecution indices left right).value =
      (dotWithCost indices left right).value := by
  apply signMagnitude_value_injective
  rw [determinantDotExecution_value, dotWithCost_value]

@[simp] public theorem determinantAddExecution_cost
    (left right : SignMagnitude) :
    traceBitCost (determinantAddExecution left right).charges =
      (addWithCost left right).cost := by
  simp only [determinantAddExecution, traceBitCost, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    KannanBachemArithmeticCharge.bitCost_additionOfRun]

@[simp] public theorem determinantMulExecution_cost
    (left right : SignMagnitude) :
    traceBitCost (determinantMulExecution left right).charges =
      (mulWithCost left right).cost := by
  simp only [determinantMulExecution, traceBitCost, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    KannanBachemArithmeticCharge.bitCost_multiplicationOfRun]

public theorem determinantSumExecution_cost (values : List SignMagnitude) :
    traceBitCost (determinantSumExecution values).charges =
      (sumWithCost values).cost := by
  induction values with
  | nil => simp [determinantSumExecution, sumWithCost, traceBitCost]
  | cons head tail ih =>
      rw [determinantSumExecution]
      dsimp only
      rw [traceBitCost_append, ih, determinantAddExecution_cost,
        determinantSumExecution_value_eq]
      rfl

public theorem determinantDotExecution_cost {ι : Type*}
    (indices : List ι) (left right : ι → SignMagnitude) :
    traceBitCost (determinantDotExecution indices left right).charges =
      (dotWithCost indices left right).cost := by
  induction indices with
  | nil => simp [determinantDotExecution, dotWithCost, traceBitCost]
  | cons index tail ih =>
      rw [determinantDotExecution]
      dsimp only
      rw [traceBitCost_append, traceBitCost_append,
        determinantMulExecution_cost, ih, determinantAddExecution_cost,
        determinantDotExecution_value_eq]
      simp only [determinantMulExecution, dotWithCost]
      omega

/-- One Bird recurrence entry using only addition and multiplication leaves. -/
@[expose] public def determinantEntryExecution {n : Nat}
    (input current : Matrix (Fin n) (Fin n) SignMagnitude)
    (row column : Fin n) : DeterminantScalarExecution :=
  let indices := upperIndices row
  let diagonal := determinantSumExecution
    (indices.map fun index ↦ current index index)
  let negated := determinantMulExecution
    (SignMagnitude.ofInt (-1)) diagonal.value
  let leading := determinantMulExecution negated.value (input row column)
  let trailing := determinantDotExecution indices
    (fun index ↦ current row index) (fun index ↦ input index column)
  let result := determinantAddExecution leading.value trailing.value
  { value := result.value
    charges := diagonal.charges ++
      (negated.charges ++ (leading.charges ++
        (trailing.charges ++ result.charges)))
    trace_wellFormed := diagonal.trace_wellFormed.append <|
      negated.trace_wellFormed.append <|
        leading.trace_wellFormed.append <|
          trailing.trace_wellFormed.append result.trace_wellFormed }

public theorem determinantEntryExecution_value {n : Nat}
    (input current : Matrix (Fin n) (Fin n) SignMagnitude)
    (row column : Fin n) :
    (determinantEntryExecution input current row column).value.value =
      entry (fun i j ↦ (input i j).value)
        (fun i j ↦ (current i j).value) row column := by
  simp only [determinantEntryExecution, determinantAddExecution,
    determinantMulExecution, addWithCost_value, mulWithCost_value,
    SignMagnitude.value_ofInt, determinantSumExecution_value,
    determinantDotExecution_value, entry, List.map_map]
  have diagonalMap :
      (SignMagnitude.value ∘ fun index ↦ current index index) =
        (fun index ↦ (current index index).value) := rfl
  rw [diagonalMap]
  ring

/-- One leaf-expanded Bird entry, including explicit scalar negation. -/
@[expose] public def determinantEntryExecutionBitOperationBound
    (dimension inputBits currentBits : Nat) : Nat :=
  entryBitOperationBound dimension inputBits currentBits +
    multiplicationCostForBitLengths 1
      (dimension * (currentBits + 1))

public theorem determinantEntryExecution_cost_le {n : Nat}
    (input current : Matrix (Fin n) (Fin n) SignMagnitude)
    (row column : Fin n) (inputBits currentBits : Nat)
    (inputBound : ∀ i j, (input i j).bitLength ≤ inputBits)
    (currentBound : ∀ i j, (current i j).bitLength ≤ currentBits) :
    traceBitCost (determinantEntryExecution input current row column).charges ≤
      determinantEntryExecutionBitOperationBound n inputBits currentBits := by
  let indices := upperIndices row
  let diagonalValues := indices.map fun index ↦ current index index
  let diagonal := determinantSumExecution diagonalValues
  let negated := determinantMulExecution
    (SignMagnitude.ofInt (-1)) diagonal.value
  let leading := determinantMulExecution negated.value (input row column)
  let trailing := determinantDotExecution indices
    (fun index ↦ current row index) (fun index ↦ input index column)
  let result := determinantAddExecution leading.value trailing.value
  have indicesLength : indices.length ≤ n := upperIndices_length_le row
  have diagonalOperands :
      ∀ value ∈ diagonalValues, value.bitLength ≤ currentBits := by
    intro value member
    simp only [diagonalValues, List.mem_map] at member
    obtain ⟨index, _member, rfl⟩ := member
    exact currentBound index index
  have diagonalListLength : diagonalValues.length ≤ n := by
    simp only [diagonalValues, List.length_map]
    exact indicesLength
  have diagonalCost :
      traceBitCost diagonal.charges ≤
        n * additionCostForBitLengths currentBits
          (n * (currentBits + 1)) := by
    change traceBitCost (determinantSumExecution diagonalValues).charges ≤ _
    rw [determinantSumExecution_cost]
    exact (sumWithCost_cost_le diagonalValues n currentBits
      diagonalListLength diagonalOperands).trans
        (Nat.mul_le_mul_right _ diagonalListLength)
  have diagonalWidth :
      diagonal.value.bitLength ≤ n * (currentBits + 1) := by
    have valueEq : diagonal.value = (sumWithCost diagonalValues).value := by
      apply signMagnitude_value_injective
      rw [determinantSumExecution_value, sumWithCost_value]
    rw [valueEq]
    exact (sumWithCost_value_bitLength_le diagonalValues currentBits
      diagonalOperands).trans
        (Nat.mul_le_mul_right (currentBits + 1) diagonalListLength)
  have negatedCost :
      traceBitCost negated.charges ≤
        multiplicationCostForBitLengths 1
          (n * (currentBits + 1)) := by
    change traceBitCost
      (determinantMulExecution (SignMagnitude.ofInt (-1))
        diagonal.value).charges ≤ _
    rw [determinantMulExecution_cost]
    apply (mulWithCost_cost_le _ _).trans
    apply Internal.mulBitOperationBound_le_lengths
    · simp [SignMagnitude.bitLength_eq_natSize_natAbs,
        SignMagnitude.value_ofInt]
    · exact diagonalWidth
  have negatedWidth :
      negated.value.bitLength ≤ n * (currentBits + 1) := by
    have valueEq : negated.value = -diagonal.value := by
      apply signMagnitude_value_injective
      simp [negated, determinantMulExecution, mulWithCost_value,
        SignMagnitude.value_ofInt]
    rw [valueEq, SignMagnitude.bitLength_neg]
    exact diagonalWidth
  have leadingCost :
      traceBitCost leading.charges ≤
        multiplicationCostForBitLengths
          (n * (currentBits + 1)) inputBits := by
    change traceBitCost
      (determinantMulExecution negated.value (input row column)).charges ≤ _
    rw [determinantMulExecution_cost]
    exact (mulWithCost_cost_le _ _).trans
      (Internal.mulBitOperationBound_le_lengths _ _ _ _
        negatedWidth (inputBound row column))
  have leadingWidth :
      leading.value.bitLength ≤
        n * (currentBits + 1) + inputBits := by
    change
      (determinantMulExecution negated.value
        (input row column)).value.bitLength ≤ _
    simp only [determinantMulExecution]
    exact (mulWithCost_value_bitLength_le _ _).trans (by
      have inputWidth := inputBound row column
      omega)
  have trailingCost :
      traceBitCost trailing.charges ≤
        n * dotTermBitOperationBound n currentBits inputBits := by
    change traceBitCost
      (determinantDotExecution indices
        (fun index ↦ current row index)
        (fun index ↦ input index column)).charges ≤ _
    rw [determinantDotExecution_cost]
    exact (dotWithCost_cost_le indices _ _ n currentBits inputBits
      indicesLength
      (fun index _ ↦ currentBound row index)
      (fun index _ ↦ inputBound index column)).trans (by gcongr)
  have trailingWidth :
      trailing.value.bitLength ≤
        n * (currentBits + inputBits + 1) := by
    have valueEq : trailing.value =
        (dotWithCost indices
          (fun index ↦ current row index)
          (fun index ↦ input index column)).value := by
      apply signMagnitude_value_injective
      rw [determinantDotExecution_value, dotWithCost_value]
    rw [valueEq]
    exact (dotWithCost_value_bitLength_le indices _ _
      currentBits inputBits
      (fun index _ ↦ currentBound row index)
      (fun index _ ↦ inputBound index column)).trans (by gcongr)
  have resultCost :
      traceBitCost result.charges ≤
        additionCostForBitLengths
          (n * (currentBits + 1) + inputBits)
          (n * (currentBits + inputBits + 1)) := by
    change traceBitCost
      (determinantAddExecution leading.value trailing.value).charges ≤ _
    rw [determinantAddExecution_cost]
    exact (addWithCost_cost_le _ _).trans
      (Internal.addBitOperationBound_le_lengths _ _ _ _
        leadingWidth trailingWidth)
  simp only [determinantEntryExecution, traceBitCost_append,
    determinantEntryExecutionBitOperationBound, entryBitOperationBound]
  dsimp only [indices, diagonalValues, diagonal, negated, leading,
    trailing, result] at diagonalCost negatedCost leadingCost trailingCost resultCost
  omega

/-- All entries of one materialized Bird recurrence step. -/
public structure DeterminantMatrixExecution (n : Nat) where
  entries : Fin n → Fin n → DeterminantScalarExecution

namespace DeterminantMatrixExecution

@[expose] public def value {n : Nat}
    (execution : DeterminantMatrixExecution n) :
    DenseMatrix n SignMagnitude :=
  DenseMatrix.ofMatrix fun row column ↦
    (execution.entries row column).value

@[expose] public def charges {n : Nat}
    (execution : DeterminantMatrixExecution n) :
    List KannanBachemArithmeticCharge :=
  (List.finRange n).flatMap fun row ↦
    (List.finRange n).flatMap fun column ↦
      (execution.entries row column).charges

public theorem trace_wellFormed {n : Nat}
    (execution : DeterminantMatrixExecution n) :
    ArithmeticChargeListWellFormed execution.charges := by
  rw [ArithmeticChargeListWellFormed, List.forall_iff_forall_mem]
  intro charge member
  rw [charges, List.mem_flatMap] at member
  obtain ⟨row, _rowMember, member⟩ := member
  rw [List.mem_flatMap] at member
  obtain ⟨column, _columnMember, member⟩ := member
  exact (List.forall_iff_forall_mem.mp
    (execution.entries row column).trace_wellFormed) charge member

end DeterminantMatrixExecution

@[expose] public def determinantDenseStepExecution {n : Nat}
    (input current : DenseMatrix n SignMagnitude) :
    DeterminantMatrixExecution n :=
  { entries := fun row column ↦
      determinantEntryExecution input.toMatrix current.toMatrix row column }

public theorem determinantDenseStepExecution_value {n : Nat}
    (input current : DenseMatrix n SignMagnitude) :
    (determinantDenseStepExecution input current).value.decode =
      matrixStep input.decode current.decode := by
  ext row column
  simp only [determinantDenseStepExecution,
    DeterminantMatrixExecution.value, DenseMatrix.decode,
    DenseMatrix.get_ofMatrix, matrixStep]
  exact determinantEntryExecution_value
    input.toMatrix current.toMatrix row column

private theorem determinantTraceBitCost_flatMap {α : Type*}
    (values : List α) (f : α → List KannanBachemArithmeticCharge) :
    traceBitCost (values.flatMap f) =
      (values.map fun value ↦ traceBitCost (f value)).sum := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [traceBitCost_append, ih]

public theorem determinantDenseStepExecution_cost_le {n : Nat}
    (input current : DenseMatrix n SignMagnitude) :
    traceBitCost (determinantDenseStepExecution input current).charges ≤
      n * n * determinantEntryExecutionBitOperationBound n
        (matrixBitLength input.decode) (matrixBitLength current.decode) := by
  rw [DeterminantMatrixExecution.charges]
  simp only [determinantDenseStepExecution]
  rw [determinantTraceBitCost_flatMap]
  simp_rw [determinantTraceBitCost_flatMap]
  calc
    (List.finRange n |>.map fun row ↦
        (List.finRange n |>.map fun column ↦
          traceBitCost
            (determinantEntryExecution input.toMatrix current.toMatrix
              row column).charges).sum).sum ≤
        (List.finRange n |>.map fun _row ↦
          (List.finRange n |>.map fun _column ↦
            determinantEntryExecutionBitOperationBound n
              (matrixBitLength input.decode)
              (matrixBitLength current.decode)).sum).sum := by
      apply List.sum_le_sum
      intro row _rowMember
      apply List.sum_le_sum
      intro column _columnMember
      apply determinantEntryExecution_cost_le
      · intro i j
        exact DenseMatrix.entry_bitLength_le_decode input i j
      · intro i j
        exact DenseMatrix.entry_bitLength_le_decode current i j
    _ = n * n * determinantEntryExecutionBitOperationBound n
          (matrixBitLength input.decode)
          (matrixBitLength current.decode) := by
      simp
      ring

public theorem determinantEntryExecutionBitOperationBound_mono
    (dimension : Nat)
    {inputBits currentBits largerInputBits largerCurrentBits : Nat}
    (inputMono : inputBits ≤ largerInputBits)
    (currentMono : currentBits ≤ largerCurrentBits) :
    determinantEntryExecutionBitOperationBound
        dimension inputBits currentBits ≤
      determinantEntryExecutionBitOperationBound
        dimension largerInputBits largerCurrentBits := by
  unfold determinantEntryExecutionBitOperationBound
    multiplicationCostForBitLengths
  exact Nat.add_le_add
    (entryBitOperationBound_mono dimension inputMono currentMono) (by gcongr)

/-- Iterated Bird recurrence, retaining only the current matrix and flat trace. -/
public structure DeterminantIterationExecution (n : Nat) where
  value : DenseMatrix n SignMagnitude
  charges : List KannanBachemArithmeticCharge
  trace_wellFormed : ArithmeticChargeListWellFormed charges

@[expose] public def determinantIterateExecution {n : Nat}
    (input : DenseMatrix n SignMagnitude) :
    Nat → DeterminantIterationExecution n
  | 0 =>
      { value := input
        charges := []
        trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }
  | steps + 1 =>
      let previous := determinantIterateExecution input steps
      let following := determinantDenseStepExecution input previous.value
      { value := following.value
        charges := previous.charges ++ following.charges
        trace_wellFormed :=
          previous.trace_wellFormed.append following.trace_wellFormed }

public theorem determinantIterateExecution_value {n : Nat}
    (input : DenseMatrix n SignMagnitude) (steps : Nat) :
    (determinantIterateExecution input steps).value.decode =
      matrixIterate input.decode steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [determinantIterateExecution, matrixIterate]
      rw [determinantDenseStepExecution_value, ih]

public theorem determinantIterateExecution_cost_le {n : Nat}
    (input : Matrix (Fin n) (Fin n) Int)
    (steps maxSteps : Nat) (stepsLe : steps ≤ maxSteps) :
    traceBitCost
        (determinantIterateExecution (DenseMatrix.encode input) steps).charges ≤
      steps * n * n *
        determinantEntryExecutionBitOperationBound n
          (matrixBitLength input)
          (iterationBitLengthBound n (matrixBitLength input) maxSteps) := by
  induction steps with
  | zero => simp [determinantIterateExecution, traceBitCost]
  | succ steps ih =>
      have previousLe : steps ≤ maxSteps := by omega
      have previousCost := ih previousLe
      let encoded := DenseMatrix.encode input
      let previous := determinantIterateExecution encoded steps
      have inputDecoded : encoded.decode = input :=
        DenseMatrix.decode_encode input
      have previousDecoded :
          previous.value.decode = matrixIterate input steps := by
        calc
          previous.value.decode =
              matrixIterate encoded.decode steps := by
            simpa only [previous] using
              determinantIterateExecution_value encoded steps
          _ = matrixIterate input steps := by rw [inputDecoded]
      have rawStepCost :=
        determinantDenseStepExecution_cost_le encoded previous.value
      rw [inputDecoded, previousDecoded] at rawStepCost
      have currentWidth :
          matrixBitLength (matrixIterate input steps) ≤
            iterationBitLengthBound n (matrixBitLength input) maxSteps :=
        (matrixIterate_bitLength_le input steps).trans
          (iterationBitLengthBound_mono_steps n
            (matrixBitLength input) previousLe)
      have entryMono :=
        determinantEntryExecutionBitOperationBound_mono n
          (inputBits := matrixBitLength input)
          (currentBits := matrixBitLength (matrixIterate input steps))
          (largerInputBits := matrixBitLength input)
          (largerCurrentBits :=
            iterationBitLengthBound n (matrixBitLength input) maxSteps)
          le_rfl currentWidth
      have followingCost :
          traceBitCost
              (determinantDenseStepExecution encoded previous.value).charges ≤
            n * n *
              determinantEntryExecutionBitOperationBound n
                (matrixBitLength input)
                (iterationBitLengthBound n
                  (matrixBitLength input) maxSteps) :=
        rawStepCost.trans (Nat.mul_le_mul_left (n * n) entryMono)
      rw [determinantIterateExecution, traceBitCost_append]
      change traceBitCost previous.charges +
          traceBitCost
            (determinantDenseStepExecution encoded previous.value).charges ≤ _
      calc
        _ ≤ steps * n * n *
                determinantEntryExecutionBitOperationBound n
                  (matrixBitLength input)
                  (iterationBitLengthBound n
                    (matrixBitLength input) maxSteps) +
              n * n *
                determinantEntryExecutionBitOperationBound n
                  (matrixBitLength input)
                  (iterationBitLengthBound n
                    (matrixBitLength input) maxSteps) :=
          Nat.add_le_add previousCost followingCost
        _ = (steps + 1) * n * n *
              determinantEntryExecutionBitOperationBound n
                (matrixBitLength input)
                (iterationBitLengthBound n
                  (matrixBitLength input) maxSteps) := by ring

/-- One fully leaf-expanded determinant result. -/
public structure DeterminantExecution {n : Nat}
    (input : Matrix (Fin n) (Fin n) Int) where
  value : SignMagnitude
  charges : List KannanBachemArithmeticCharge
  value_eq : value.value = input.det
  trace_wellFormed : ArithmeticChargeListWellFormed charges

@[expose] public def determinantExecution {n : Nat}
    (input : Matrix (Fin n) (Fin n) Int) : DeterminantExecution input := by
  match n with
  | 0 =>
      exact
        { value := SignMagnitude.ofInt 1
          charges := []
          value_eq := by simp [SignMagnitude.value_ofInt]
          trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }
  | steps + 1 =>
      let encoded := DenseMatrix.encode input
      let iteration := determinantIterateExecution encoded steps
      let sign := SignMagnitude.ofInt ((-1 : Int) ^ steps)
      let result := determinantMulExecution sign
        ((iteration.value.get 0).get 0)
      have resultValue : result.value.value = input.det := by
        rw [show result.value.value =
            sign.value * ((iteration.value.get 0).get 0).value by
          exact mulWithCost_value sign ((iteration.value.get 0).get 0)]
        rw [show sign.value = ((-1 : Int) ^ steps) by
          exact SignMagnitude.value_ofInt _]
        have decoded := determinantIterateExecution_value encoded steps
        have entryEquality := congrFun (congrFun decoded 0) 0
        rw [DenseMatrix.decode_encode] at entryEquality
        exact (congrArg
          (fun value ↦ ((-1 : Int) ^ steps) * value)
          entryEquality).trans <|
            (matrixBirdDet_eq_det input)
      exact
        { value := result.value
          charges := iteration.charges ++ result.charges
          value_eq := resultValue
          trace_wellFormed :=
            iteration.trace_wellFormed.append result.trace_wellFormed }

public theorem determinantExecution_value_eq_evaluateWithCost {n : Nat}
    (input : Matrix (Fin n) (Fin n) Int) :
    (determinantExecution input).value = (evaluateWithCost input).value := by
  apply signMagnitude_value_injective
  rw [(determinantExecution input).value_eq,
    evaluateWithCost_value_eq_det]

/-- Closed leaf-trace budget for one determinant evaluation. -/
@[expose] public def determinantExecutionBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  let operandBits :=
    iterationBitLengthBound dimension inputBits dimension
  dimension * dimension * dimension *
      determinantEntryExecutionBitOperationBound
        dimension inputBits operandBits +
    multiplicationCostForBitLengths 1 operandBits

public theorem determinantExecutionBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    determinantExecutionBitOperationBound dimension smaller ≤
      determinantExecutionBitOperationBound dimension larger := by
  unfold determinantExecutionBitOperationBound iterationBitLengthBound
    determinantEntryExecutionBitOperationBound entryBitOperationBound
    dotTermBitOperationBound additionCostForBitLengths
    multiplicationCostForBitLengths
  dsimp only
  gcongr

public theorem determinantExecution_cost_le {n : Nat}
    (input : Matrix (Fin n) (Fin n) Int) :
    traceBitCost (determinantExecution input).charges ≤
      determinantExecutionBitOperationBound n (matrixBitLength input) := by
  cases n with
  | zero =>
      simp [determinantExecution, determinantExecutionBitOperationBound,
        traceBitCost]
  | succ steps =>
      let encoded := DenseMatrix.encode input
      let iteration := determinantIterateExecution encoded steps
      let sign := SignMagnitude.ofInt ((-1 : Int) ^ steps)
      let result := determinantMulExecution sign
        ((iteration.value.get 0).get 0)
      let operandBits := iterationBitLengthBound (steps + 1)
        (matrixBitLength input) (steps + 1)
      have stepsLe : steps ≤ steps + 1 := Nat.le_succ _
      have iterationCost :
          traceBitCost iteration.charges ≤
            steps * (steps + 1) * (steps + 1) *
              determinantEntryExecutionBitOperationBound (steps + 1)
                (matrixBitLength input) operandBits := by
        simpa only [encoded, iteration, operandBits] using
          determinantIterateExecution_cost_le input
            steps (steps + 1) stepsLe
      have iterationDecoded :
          iteration.value.decode = matrixIterate input steps := by
        calc
          iteration.value.decode =
              matrixIterate encoded.decode steps := by
            simpa only [iteration] using
              determinantIterateExecution_value encoded steps
          _ = matrixIterate input steps := by
            rw [DenseMatrix.decode_encode]
      have entryWidth :
          ((iteration.value.get 0).get 0).bitLength ≤ operandBits := by
        calc
          ((iteration.value.get 0).get 0).bitLength ≤
              matrixBitLength iteration.value.decode :=
            DenseMatrix.entry_bitLength_le_decode iteration.value 0 0
          _ = matrixBitLength (matrixIterate input steps) := by
            rw [iterationDecoded]
          _ ≤ iterationBitLengthBound (steps + 1)
                (matrixBitLength input) steps :=
            matrixIterate_bitLength_le input steps
          _ ≤ operandBits :=
            iterationBitLengthBound_mono_steps (steps + 1)
              (matrixBitLength input) stepsLe
      have signWidth : sign.bitLength ≤ 1 := by
        simp only [sign, SignMagnitude.bitLength_eq_natSize_natAbs,
          SignMagnitude.value_ofInt, Int.natAbs_pow, Int.natAbs_neg,
          Int.natAbs_one, one_pow]
        decide
      have resultCost :
          traceBitCost result.charges ≤
            multiplicationCostForBitLengths 1 operandBits := by
        change traceBitCost
          (determinantMulExecution sign
            ((iteration.value.get 0).get 0)).charges ≤ _
        rw [determinantMulExecution_cost]
        exact (mulWithCost_cost_le _ _).trans
          (Internal.mulBitOperationBound_le_lengths _ _ _ _
            signWidth entryWidth)
      simp only [determinantExecution, traceBitCost_append]
      change traceBitCost iteration.charges + traceBitCost result.charges ≤ _
      unfold determinantExecutionBitOperationBound
      dsimp only
      calc
        _ ≤ steps * (steps + 1) * (steps + 1) *
                determinantEntryExecutionBitOperationBound (steps + 1)
                  (matrixBitLength input) operandBits +
              multiplicationCostForBitLengths 1 operandBits :=
          Nat.add_le_add iterationCost resultCost
        _ ≤ (steps + 1) * (steps + 1) * (steps + 1) *
                determinantEntryExecutionBitOperationBound (steps + 1)
                  (matrixBitLength input) operandBits +
              multiplicationCostForBitLengths 1 operandBits := by
          gcongr

end NormalForms.Research.KannanBachem
