/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminantCorrectness
public import NormalForms.Research.BitCost.XGCD

/-!
# Exact Reference Cost for the Cached Bird Recurrence

This module executes the cached recurrence over the explicit binary
sign-magnitude integers from `Research.BitCost`.  Every scalar sum and product
uses the already verified schoolbook primitives.  The returned cost is the
sum of those concrete primitive charges; vector construction and indexing are
kept as the surrounding RAM-model control cost and are bounded separately.

The value proof factors through `matrixBirdDet`; the separate algebraic
correctness module identifies that recurrence with `Matrix.det`.  This keeps
the executable arithmetic argument independent from the bordered-minor proof.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

open scoped BigOperators
open NormalForms.Research.BitCost

namespace DivisionFreeDeterminant

/-- Costed left-associated sum with an explicit zero accumulator. -/
@[expose] public def sumWithCost : List SignMagnitude → WithCost SignMagnitude
  | [] => WithCost.pure 0
  | head :: tail =>
      let tailResult := sumWithCost tail
      let result := addWithCost head tailResult.value
      { value := result.value
        cost := tailResult.cost + result.cost }

@[simp] public theorem sumWithCost_value (values : List SignMagnitude) :
    (sumWithCost values).value.value =
      (values.map SignMagnitude.value).sum := by
  induction values with
  | nil => simp [sumWithCost, WithCost.pure]
  | cons head tail ih =>
      simp only [sumWithCost, List.map_cons, List.sum_cons]
      rw [addWithCost_value, ih]

/-- Costed dot product over an explicit finite index list. -/
@[expose] public def dotWithCost {ι : Type*}
    (indices : List ι) (left right : ι → SignMagnitude) :
    WithCost SignMagnitude :=
  match indices with
  | [] => WithCost.pure 0
  | index :: tail =>
      let product := mulWithCost (left index) (right index)
      let tailResult := dotWithCost tail left right
      let result := addWithCost product.value tailResult.value
      { value := result.value
        cost := product.cost + tailResult.cost + result.cost }

@[simp] public theorem dotWithCost_value {ι : Type*}
    (indices : List ι) (left right : ι → SignMagnitude) :
    (dotWithCost indices left right).value.value =
      (indices.map fun index =>
        (left index).value * (right index).value).sum := by
  induction indices with
  | nil => simp [dotWithCost, WithCost.pure]
  | cons index tail ih =>
      simp only [dotWithCost, List.map_cons, List.sum_cons]
      rw [addWithCost_value, mulWithCost_value, ih]

/-- One fully charged scalar entry of the Bird recurrence. -/
@[expose] public def entryWithCost {n : Nat}
    (input current : _root_.Matrix (Fin n) (Fin n) SignMagnitude)
    (i j : Fin n) : WithCost SignMagnitude :=
  let indices := upperIndices i
  let diagonal := sumWithCost (indices.map fun k => current k k)
  let leading := mulWithCost (-diagonal.value) (input i j)
  let trailing := dotWithCost indices
    (fun k => current i k) (fun k => input k j)
  let result := addWithCost leading.value trailing.value
  { value := result.value
    cost := diagonal.cost + 1 + leading.cost + trailing.cost + result.cost }

/-- Decoding a charged entry gives exactly the mathematical scalar step. -/
public theorem entryWithCost_value {n : Nat}
    (input current : _root_.Matrix (Fin n) (Fin n) SignMagnitude)
    (i j : Fin n) :
    (entryWithCost input current i j).value.value =
      entry (fun row column => (input row column).value)
        (fun row column => (current row column).value) i j := by
  simp only [entryWithCost, addWithCost_value, mulWithCost_value,
    SignMagnitude.value_neg, sumWithCost_value, dotWithCost_value,
    entry, List.map_map]
  have diagonalMap :
      (SignMagnitude.value ∘ fun k => current k k) =
        (fun k => (current k k).value) := by
    rfl
  rw [diagonalMap]

namespace DenseMatrix

/-- Decode a dense sign-magnitude matrix to ordinary integers. -/
@[expose] public def decode {n : Nat}
    (A : DenseMatrix n SignMagnitude) :
    _root_.Matrix (Fin n) (Fin n) Int :=
  fun i j => ((A.get i).get j).value

/-- Encode an integer matrix in canonical sign-magnitude words. -/
@[expose] public def encode {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    DenseMatrix n SignMagnitude :=
  ofMatrix fun i j => SignMagnitude.ofInt (A i j)

@[simp] public theorem decode_encode {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    decode (encode A) = A := by
  ext i j
  simp [decode, encode, SignMagnitude.value_ofInt]

end DenseMatrix

/-- One materialized matrix step and the sum of all scalar primitive costs. -/
@[expose] public def denseStepWithCost {n : Nat}
    (input current : DenseMatrix n SignMagnitude) :
    WithCost (DenseMatrix n SignMagnitude) :=
  let charged := fun i j =>
    entryWithCost input.toMatrix current.toMatrix i j
  { value := DenseMatrix.ofMatrix fun i j => (charged i j).value
    cost := ∑ i, ∑ j, (charged i j).cost }

/-- One charged dense step decodes to one mathematical matrix step. -/
public theorem DenseMatrix.decode_denseStepWithCost {n : Nat}
    (input current : DenseMatrix n SignMagnitude) :
    (denseStepWithCost input current).value.decode =
      matrixStep input.decode current.decode := by
  ext i j
  simp only [denseStepWithCost, DenseMatrix.decode,
    DenseMatrix.get_ofMatrix]
  exact entryWithCost_value input.toMatrix current.toMatrix i j

/-- Iterate the exact charged program while retaining each previous stage once. -/
@[expose] public def denseIterateWithCost {n : Nat}
    (input : DenseMatrix n SignMagnitude) : Nat →
      WithCost (DenseMatrix n SignMagnitude)
  | 0 => WithCost.pure input
  | steps + 1 =>
      let previous := denseIterateWithCost input steps
      let following := denseStepWithCost input previous.value
      { value := following.value
        cost := previous.cost + following.cost }

/-- Every charged stage decodes to the matching mathematical recurrence stage. -/
public theorem DenseMatrix.decode_denseIterateWithCost {n : Nat}
    (input : DenseMatrix n SignMagnitude) (steps : Nat) :
    (denseIterateWithCost input steps).value.decode =
      matrixIterate input.decode steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [denseIterateWithCost, matrixIterate]
      rw [DenseMatrix.decode_denseStepWithCost, ih]

/-- Exact schoolbook-arithmetic execution of the cached Bird recurrence. -/
@[expose] public def evaluateWithCost {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) Int) :
    WithCost SignMagnitude :=
  match n with
  | 0 => WithCost.pure (SignMagnitude.ofInt 1)
  | k + 1 =>
      let encoded := DenseMatrix.encode input
      let iteration := denseIterateWithCost encoded k
      let sign := SignMagnitude.ofInt ((-1 : Int) ^ k)
      let result := mulWithCost sign
        ((iteration.value.get 0).get 0)
      { value := result.value
        cost := iteration.cost + result.cost }

/-- The exact costed program computes the cached algebraic recurrence value. -/
public theorem evaluateWithCost_value {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) Int) :
    (evaluateWithCost input).value.value = matrixBirdDet input := by
  cases n with
  | zero =>
      simp [evaluateWithCost, matrixBirdDet,
        SignMagnitude.value_ofInt]
  | succ k =>
      simp only [evaluateWithCost, matrixBirdDet, mulWithCost_value,
        SignMagnitude.value_ofInt]
      have decoded := DenseMatrix.decode_denseIterateWithCost
        (DenseMatrix.encode input) k
      have entryEquality := congrFun (congrFun decoded 0) 0
      simpa [DenseMatrix.decode, DenseMatrix.decode_encode] using
        congrArg (fun value => ((-1 : Int) ^ k) * value) entryEquality

/-- The exact charged program computes the standard integer determinant. -/
public theorem evaluateWithCost_value_eq_det {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) Int) :
    (evaluateWithCost input).value.value = input.det :=
  (evaluateWithCost_value input).trans (matrixBirdDet_eq_det input)

/-- Decoding explicit sign-magnitude words is injective. -/
public theorem signMagnitude_value_injective :
    Function.Injective SignMagnitude.value := by
  intro left right equality
  rw [← SignMagnitude.ofInt_value left, ← SignMagnitude.ofInt_value right,
    equality]

/-- Structural nonzeroness of the charged result is standard nonsingularity. -/
public theorem evaluateWithCost_value_ne_zero_iff {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) Int) :
    (evaluateWithCost input).value ≠ 0 ↔ input.det ≠ 0 := by
  rw [← evaluateWithCost_value_eq_det input]
  simpa using not_congr
    (signMagnitude_value_injective.eq_iff
      (a := (evaluateWithCost input).value) (b := 0)).symm

/-! ## Uniform primitive-cost bounds -/

/-- A sequential sum has a polynomial accumulator-width envelope. -/
public theorem sumWithCost_value_bitLength_le
    (values : List SignMagnitude) (operandBits : Nat)
    (bounded : ∀ value ∈ values, value.bitLength ≤ operandBits) :
    (sumWithCost values).value.bitLength ≤
      values.length * (operandBits + 1) := by
  induction values with
  | nil =>
      simp only [sumWithCost, WithCost.pure, List.length_nil,
        Nat.zero_mul, SignMagnitude.bitLength_zero]
      omega
  | cons head tail ih =>
      have headWidth := bounded head (by simp)
      have tailWidth := ih fun value member => bounded value (by simp [member])
      rw [sumWithCost]
      calc
        (addWithCost head (sumWithCost tail).value).value.bitLength ≤
            head.bitLength +
              (sumWithCost tail).value.bitLength + 1 :=
          addWithCost_value_bitLength_le _ _
        _ ≤ operandBits + tail.length * (operandBits + 1) + 1 := by
          omega
        _ = (head :: tail).length * (operandBits + 1) := by
          simp only [List.length_cons]
          ring

/-- Uniform charge for every addition in a sequential sum. -/
public theorem sumWithCost_cost_le
    (values : List SignMagnitude) (count operandBits : Nat)
    (lengthBound : values.length ≤ count)
    (bounded : ∀ value ∈ values, value.bitLength ≤ operandBits) :
    (sumWithCost values).cost ≤
      values.length *
        additionCostForBitLengths operandBits (count * (operandBits + 1)) := by
  induction values with
  | nil => simp [sumWithCost]
  | cons head tail ih =>
      have tailLength : tail.length ≤ count := by simp at lengthBound; omega
      have headWidth := bounded head (by simp)
      have tailBound : ∀ value ∈ tail, value.bitLength ≤ operandBits := by
        intro value member
        exact bounded value (by simp [member])
      have tailCost := ih tailLength tailBound
      have tailWidth :
          (sumWithCost tail).value.bitLength ≤
            count * (operandBits + 1) :=
        (sumWithCost_value_bitLength_le tail operandBits tailBound).trans <| by
          gcongr
      have additionCost :
          (addWithCost head (sumWithCost tail).value).cost ≤
            additionCostForBitLengths operandBits
              (count * (operandBits + 1)) :=
        (addWithCost_cost_le _ _).trans
          (Internal.addBitOperationBound_le_lengths _ _ _ _
            headWidth tailWidth)
      rw [sumWithCost]
      calc
        (sumWithCost tail).cost +
              (addWithCost head (sumWithCost tail).value).cost ≤
            tail.length *
                additionCostForBitLengths operandBits
                  (count * (operandBits + 1)) +
              additionCostForBitLengths operandBits
                (count * (operandBits + 1)) :=
          Nat.add_le_add tailCost additionCost
        _ = (head :: tail).length *
              additionCostForBitLengths operandBits
                (count * (operandBits + 1)) := by
          simp only [List.length_cons]
          ring

/-- A dot-product accumulator remains polynomially bounded in the list length. -/
public theorem dotWithCost_value_bitLength_le {ι : Type*}
    (indices : List ι) (left right : ι → SignMagnitude)
    (leftBits rightBits : Nat)
    (leftBound : ∀ index ∈ indices, (left index).bitLength ≤ leftBits)
    (rightBound : ∀ index ∈ indices, (right index).bitLength ≤ rightBits) :
    (dotWithCost indices left right).value.bitLength ≤
      indices.length * (leftBits + rightBits + 1) := by
  induction indices with
  | nil =>
      simp only [dotWithCost, WithCost.pure, List.length_nil,
        Nat.zero_mul, SignMagnitude.bitLength_zero]
      omega
  | cons index tail ih =>
      have leftWidth := leftBound index (by simp)
      have rightWidth := rightBound index (by simp)
      have productWidth := mulWithCost_value_bitLength_le
        (left index) (right index)
      have tailWidth := ih
        (fun next member => leftBound next (by simp [member]))
        (fun next member => rightBound next (by simp [member]))
      rw [dotWithCost]
      calc
        (addWithCost (mulWithCost (left index) (right index)).value
              (dotWithCost tail left right).value).value.bitLength ≤
            (mulWithCost (left index) (right index)).value.bitLength +
              (dotWithCost tail left right).value.bitLength + 1 :=
          addWithCost_value_bitLength_le _ _
        _ ≤ (leftBits + rightBits) +
              tail.length * (leftBits + rightBits + 1) + 1 := by
          omega
        _ = (index :: tail).length *
              (leftBits + rightBits + 1) := by
          simp only [List.length_cons]
          ring

/-- Per-index schoolbook budget used by a uniform dot product. -/
@[expose] public def dotTermBitOperationBound
    (count leftBits rightBits : Nat) : Nat :=
  multiplicationCostForBitLengths leftBits rightBits +
    additionCostForBitLengths (leftBits + rightBits)
      (count * (leftBits + rightBits + 1))

public theorem dotWithCost_cost_le {ι : Type*}
    (indices : List ι) (left right : ι → SignMagnitude)
    (count leftBits rightBits : Nat)
    (lengthBound : indices.length ≤ count)
    (leftBound : ∀ index ∈ indices, (left index).bitLength ≤ leftBits)
    (rightBound : ∀ index ∈ indices, (right index).bitLength ≤ rightBits) :
    (dotWithCost indices left right).cost ≤
      indices.length * dotTermBitOperationBound count leftBits rightBits := by
  induction indices with
  | nil => simp [dotWithCost]
  | cons index tail ih =>
      have tailLength : tail.length ≤ count := by simp at lengthBound; omega
      have leftWidth := leftBound index (by simp)
      have rightWidth := rightBound index (by simp)
      have tailLeft : ∀ next ∈ tail, (left next).bitLength ≤ leftBits := by
        intro next member
        exact leftBound next (by simp [member])
      have tailRight : ∀ next ∈ tail, (right next).bitLength ≤ rightBits := by
        intro next member
        exact rightBound next (by simp [member])
      have tailCost := ih tailLength tailLeft tailRight
      have productCost :
          (mulWithCost (left index) (right index)).cost ≤
            multiplicationCostForBitLengths leftBits rightBits :=
        (mulWithCost_cost_le _ _).trans
          (Internal.mulBitOperationBound_le_lengths _ _ _ _
            leftWidth rightWidth)
      have productWidth :
          (mulWithCost (left index) (right index)).value.bitLength ≤
            leftBits + rightBits :=
        (mulWithCost_value_bitLength_le _ _).trans <| by omega
      have tailWidth :
          (dotWithCost tail left right).value.bitLength ≤
            count * (leftBits + rightBits + 1) :=
        (dotWithCost_value_bitLength_le tail left right leftBits rightBits
          tailLeft tailRight).trans <| by gcongr
      have additionCost :
          (addWithCost (mulWithCost (left index) (right index)).value
              (dotWithCost tail left right).value).cost ≤
            additionCostForBitLengths (leftBits + rightBits)
              (count * (leftBits + rightBits + 1)) :=
        (addWithCost_cost_le _ _).trans
          (Internal.addBitOperationBound_le_lengths _ _ _ _
            productWidth tailWidth)
      rw [dotWithCost]
      calc
        (mulWithCost (left index) (right index)).cost +
              (dotWithCost tail left right).cost +
              (addWithCost (mulWithCost (left index) (right index)).value
                (dotWithCost tail left right).value).cost ≤
            multiplicationCostForBitLengths leftBits rightBits +
              tail.length * dotTermBitOperationBound count leftBits rightBits +
              additionCostForBitLengths (leftBits + rightBits)
                (count * (leftBits + rightBits + 1)) :=
          Nat.add_le_add
            (Nat.add_le_add productCost tailCost) additionCost
        _ = (index :: tail).length *
              dotTermBitOperationBound count leftBits rightBits := by
          simp only [dotTermBitOperationBound, List.length_cons]
          ring

/-- One scalar Bird entry, including both sums and the final addition. -/
@[expose] public def entryBitOperationBound
    (dimension inputBits currentBits : Nat) : Nat :=
  let diagonalBits := dimension * (currentBits + 1)
  let trailingBits := dimension * (currentBits + inputBits + 1)
  dimension *
      additionCostForBitLengths currentBits diagonalBits + 1 +
    multiplicationCostForBitLengths diagonalBits inputBits +
    dimension *
      dotTermBitOperationBound dimension currentBits inputBits +
    additionCostForBitLengths (diagonalBits + inputBits) trailingBits

public theorem entryWithCost_cost_le {n : Nat}
    (input current : _root_.Matrix (Fin n) (Fin n) SignMagnitude)
    (i j : Fin n) (inputBits currentBits : Nat)
    (inputBound : ∀ row column, (input row column).bitLength ≤ inputBits)
    (currentBound : ∀ row column, (current row column).bitLength ≤ currentBits) :
    (entryWithCost input current i j).cost ≤
      entryBitOperationBound n inputBits currentBits := by
  let indices := upperIndices i
  let diagonal := sumWithCost (indices.map fun k => current k k)
  let leading := mulWithCost (-diagonal.value) (input i j)
  let trailing := dotWithCost indices
    (fun k => current i k) (fun k => input k j)
  let result := addWithCost leading.value trailing.value
  have indicesLength : indices.length ≤ n := upperIndices_length_le i
  have diagonalOperands :
      ∀ value ∈ indices.map (fun k => current k k),
        value.bitLength ≤ currentBits := by
    intro value member
    rw [List.mem_map] at member
    obtain ⟨k, _member, rfl⟩ := member
    exact currentBound k k
  have diagonalListLength :
      (indices.map fun k => current k k).length ≤ n := by
    rw [List.length_map (fun k => current k k)]
    exact indicesLength
  have diagonalCost : diagonal.cost ≤
      n * additionCostForBitLengths currentBits
        (n * (currentBits + 1)) := by
    exact (sumWithCost_cost_le _ n currentBits
      diagonalListLength diagonalOperands).trans
        (Nat.mul_le_mul_right _ diagonalListLength)
  have diagonalWidth : diagonal.value.bitLength ≤
      n * (currentBits + 1) :=
    (sumWithCost_value_bitLength_le _ currentBits diagonalOperands).trans <| by
      exact Nat.mul_le_mul_right (currentBits + 1) diagonalListLength
  have leadingCost : leading.cost ≤
      multiplicationCostForBitLengths
        (n * (currentBits + 1)) inputBits := by
    apply (mulWithCost_cost_le _ _).trans
    apply Internal.mulBitOperationBound_le_lengths
    · simpa using diagonalWidth
    · exact inputBound i j
  have leadingWidth : leading.value.bitLength ≤
      n * (currentBits + 1) + inputBits :=
    (mulWithCost_value_bitLength_le _ _).trans <| by
      have negDiagonalWidth :
          (-diagonal.value).bitLength ≤ n * (currentBits + 1) := by
        simpa using diagonalWidth
      have inputWidth := inputBound i j
      omega
  have trailingCost : trailing.cost ≤
      n * dotTermBitOperationBound n currentBits inputBits := by
    exact (dotWithCost_cost_le indices _ _ n currentBits inputBits
      indicesLength
      (fun k _ => currentBound i k)
      (fun k _ => inputBound k j)).trans <| by gcongr
  have trailingWidth : trailing.value.bitLength ≤
      n * (currentBits + inputBits + 1) :=
    (dotWithCost_value_bitLength_le indices _ _ currentBits inputBits
      (fun k _ => currentBound i k)
      (fun k _ => inputBound k j)).trans <| by gcongr
  have resultCost : result.cost ≤
      additionCostForBitLengths
        (n * (currentBits + 1) + inputBits)
        (n * (currentBits + inputBits + 1)) := by
    apply (addWithCost_cost_le _ _).trans
    exact Internal.addBitOperationBound_le_lengths _ _ _ _
      leadingWidth trailingWidth
  simp only [entryWithCost]
  change diagonal.cost + 1 + leading.cost + trailing.cost + result.cost ≤
    n * additionCostForBitLengths currentBits (n * (currentBits + 1)) + 1 +
      multiplicationCostForBitLengths (n * (currentBits + 1)) inputBits +
      n * dotTermBitOperationBound n currentBits inputBits +
      additionCostForBitLengths
        (n * (currentBits + 1) + inputBits)
        (n * (currentBits + inputBits + 1))
  omega

public theorem DenseMatrix.entry_bitLength_le_decode {n : Nat}
    (A : DenseMatrix n SignMagnitude) (i j : Fin n) :
    ((A.get i).get j).bitLength ≤ matrixBitLength A.decode := by
  rw [SignMagnitude.bitLength_eq_natSize_natAbs]
  exact entry_bitLength_le_matrixBitLength A.decode i j

/-- One materialized stage charges exactly `n²` uniformly bounded entries. -/
public theorem denseStepWithCost_cost_le {n : Nat}
    (input current : DenseMatrix n SignMagnitude) :
    (denseStepWithCost input current).cost ≤
      n * n * entryBitOperationBound n
        (matrixBitLength input.decode) (matrixBitLength current.decode) := by
  simp only [denseStepWithCost]
  calc
    (∑ i, ∑ j,
        (entryWithCost input.toMatrix current.toMatrix i j).cost) ≤
        ∑ _i : Fin n, ∑ _j : Fin n,
          entryBitOperationBound n
            (matrixBitLength input.decode)
            (matrixBitLength current.decode) := by
      gcongr with i j
      apply entryWithCost_cost_le
      · intro row column
        exact DenseMatrix.entry_bitLength_le_decode input row column
      · intro row column
        exact DenseMatrix.entry_bitLength_le_decode current row column
    _ = n * n * entryBitOperationBound n
          (matrixBitLength input.decode)
          (matrixBitLength current.decode) := by
      simp
      ring

public theorem entryBitOperationBound_mono
    (dimension : Nat)
    {inputBits currentBits largerInputBits largerCurrentBits : Nat}
    (inputMono : inputBits ≤ largerInputBits)
    (currentMono : currentBits ≤ largerCurrentBits) :
    entryBitOperationBound dimension inputBits currentBits ≤
      entryBitOperationBound dimension largerInputBits largerCurrentBits := by
  unfold entryBitOperationBound dotTermBitOperationBound
    additionCostForBitLengths multiplicationCostForBitLengths
  dsimp only
  gcongr

public theorem iterationBitLengthBound_mono_steps
    (dimension inputBits : Nat) {steps largerSteps : Nat}
    (stepsMono : steps ≤ largerSteps) :
    iterationBitLengthBound dimension inputBits steps ≤
      iterationBitLengthBound dimension inputBits largerSteps := by
  unfold iterationBitLengthBound
  gcongr

/-- Uniform bound for any prefix of the cached, charged iteration. -/
public theorem denseIterateWithCost_cost_le {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) Int)
    (steps maxSteps : Nat) (stepsLe : steps ≤ maxSteps) :
    (denseIterateWithCost (DenseMatrix.encode input) steps).cost ≤
      steps * n * n *
        entryBitOperationBound n (matrixBitLength input)
          (iterationBitLengthBound n (matrixBitLength input) maxSteps) := by
  induction steps with
  | zero => simp [denseIterateWithCost]
  | succ steps ih =>
      have previousLe : steps ≤ maxSteps := by omega
      have previousCost := ih previousLe
      let encoded := DenseMatrix.encode input
      let previous := denseIterateWithCost encoded steps
      have inputDecoded : encoded.decode = input := by
        exact DenseMatrix.decode_encode input
      have previousDecoded : previous.value.decode =
          matrixIterate input steps := by
        simpa only [encoded, previous, inputDecoded] using
          DenseMatrix.decode_denseIterateWithCost encoded steps
      have rawStepCost := denseStepWithCost_cost_le encoded previous.value
      rw [inputDecoded, previousDecoded] at rawStepCost
      have currentWidth :
          matrixBitLength (matrixIterate input steps) ≤
            iterationBitLengthBound n (matrixBitLength input) maxSteps :=
        (matrixIterate_bitLength_le input steps).trans
          (iterationBitLengthBound_mono_steps n (matrixBitLength input)
            previousLe)
      have entryMono := entryBitOperationBound_mono n
        (inputBits := matrixBitLength input)
        (currentBits := matrixBitLength (matrixIterate input steps))
        (largerInputBits := matrixBitLength input)
        (largerCurrentBits :=
          iterationBitLengthBound n (matrixBitLength input) maxSteps)
        (inputMono := le_rfl) (currentMono := currentWidth)
      have followingCost :
          (denseStepWithCost encoded previous.value).cost ≤
            n * n *
              entryBitOperationBound n (matrixBitLength input)
                (iterationBitLengthBound n (matrixBitLength input) maxSteps) :=
        rawStepCost.trans <| by
          exact Nat.mul_le_mul_left (n * n) entryMono
      rw [denseIterateWithCost]
      change previous.cost + (denseStepWithCost encoded previous.value).cost ≤ _
      calc
        previous.cost + (denseStepWithCost encoded previous.value).cost ≤
            steps * n * n *
                entryBitOperationBound n (matrixBitLength input)
                  (iterationBitLengthBound n (matrixBitLength input) maxSteps) +
              n * n *
                entryBitOperationBound n (matrixBitLength input)
                  (iterationBitLengthBound n (matrixBitLength input) maxSteps) :=
          Nat.add_le_add previousCost followingCost
        _ = (steps + 1) * n * n *
              entryBitOperationBound n (matrixBitLength input)
                (iterationBitLengthBound n (matrixBitLength input) maxSteps) := by
          ring

/-- Closed scalar-arithmetic budget for one cached determinant evaluation. -/
@[expose] public def determinantBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  let operandBits := iterationBitLengthBound dimension inputBits dimension
  dimension * dimension * dimension *
      entryBitOperationBound dimension inputBits operandBits +
    multiplicationCostForBitLengths 1 operandBits

/-- The closed determinant budget is monotone in the input width. -/
public theorem determinantBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    determinantBitOperationBound dimension smaller ≤
      determinantBitOperationBound dimension larger := by
  unfold determinantBitOperationBound iterationBitLengthBound
    entryBitOperationBound dotTermBitOperationBound
    additionCostForBitLengths multiplicationCostForBitLengths
  dsimp only
  gcongr

/-- The closed determinant budget is monotone in the matrix dimension. -/
public theorem determinantBitOperationBound_mono_dimension
    (inputBits : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    determinantBitOperationBound smaller inputBits ≤
      determinantBitOperationBound larger inputBits := by
  unfold determinantBitOperationBound iterationBitLengthBound
    entryBitOperationBound dotTermBitOperationBound
    additionCostForBitLengths multiplicationCostForBitLengths
  dsimp only
  have sizeLe : Nat.size smaller ≤ Nat.size larger := Nat.size_le_size hle
  gcongr

public theorem evaluateWithCost_cost_le {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) Int) :
    (evaluateWithCost input).cost ≤
      determinantBitOperationBound n (matrixBitLength input) := by
  cases n with
  | zero =>
      simp [evaluateWithCost, determinantBitOperationBound]
  | succ steps =>
      let encoded := DenseMatrix.encode input
      let iteration := denseIterateWithCost encoded steps
      let sign := SignMagnitude.ofInt ((-1 : Int) ^ steps)
      let result := mulWithCost sign ((iteration.value.get 0).get 0)
      let operandBits := iterationBitLengthBound (steps + 1)
        (matrixBitLength input) (steps + 1)
      have stepsLe : steps ≤ steps + 1 := Nat.le_succ _
      have iterationCost : iteration.cost ≤
          steps * (steps + 1) * (steps + 1) *
            entryBitOperationBound (steps + 1) (matrixBitLength input)
              operandBits := by
        simpa only [encoded, iteration, operandBits] using
          denseIterateWithCost_cost_le input steps (steps + 1) stepsLe
      have iterationDecoded : iteration.value.decode =
          matrixIterate input steps := by
        calc
          iteration.value.decode = matrixIterate encoded.decode steps := by
            simpa only [iteration] using
              DenseMatrix.decode_denseIterateWithCost encoded steps
          _ = matrixIterate input steps := by
            rw [DenseMatrix.decode_encode]
      have entryWidth : ((iteration.value.get 0).get 0).bitLength ≤
          operandBits := by
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
      have resultCost : result.cost ≤
          multiplicationCostForBitLengths 1 operandBits := by
        exact (mulWithCost_cost_le _ _).trans
          (Internal.mulBitOperationBound_le_lengths _ _ _ _
            signWidth entryWidth)
      simp only [evaluateWithCost]
      change iteration.cost + result.cost ≤ _
      unfold determinantBitOperationBound
      dsimp only
      calc
        iteration.cost + result.cost ≤
            steps * (steps + 1) * (steps + 1) *
                entryBitOperationBound (steps + 1) (matrixBitLength input)
                  operandBits +
              multiplicationCostForBitLengths 1 operandBits :=
          Nat.add_le_add iterationCost resultCost
        _ ≤ (steps + 1) * (steps + 1) * (steps + 1) *
                entryBitOperationBound (steps + 1) (matrixBitLength input)
                  operandBits +
              multiplicationCostForBitLengths 1 operandBits := by
          gcongr

end DivisionFreeDeterminant

end NormalForms.Research.KannanBachem.Hermite
