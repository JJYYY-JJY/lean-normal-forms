/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.Cost
public import NormalForms.Research.LLL.HexBackend
import all NormalForms.Research.LLL.Internal.Algorithm

/-!
# Explicit-transform trace for the verified dense LLL reducer

This internal module mirrors the control flow of `Hex.lllNative` while carrying
the project's constructive row-transform state.  The dense reducer remains the
source of termination and reducedness; every basis mutation is replayed as an
elementary row operation with an explicit inverse certificate.
-/

namespace NormalForms.Research.LLL.Internal.HexTrace

open scoped Matrix
open NormalForms.Matrix.Elementary
open NormalForms.Research.LLL

/-- A dense LLL state synchronized with the project's strong transform state. -/
private structure TraceState {m n : Nat}
    (input : Matrix (Fin m) (Fin n) Int) where
  core : Hex.Internal.LLLState m n
  transformState : Internal.State input
  aligned : transformState.basis = ofDense core.b
  intermediateCoefficientHeight : Nat
  basis_height_le :
    basisHeight transformState.basis <= intermediateCoefficientHeight

/-- Initial dense and certificate states represent the same input matrix. -/
private def TraceState.initial {m n : Nat}
    (input : Matrix (Fin m) (Fin n) Int) : TraceState input :=
  { core := Hex.Internal.LLLState.ofBasis (toDense input)
    transformState := Internal.State.initial input
    aligned := by simp [Internal.State.initial, Hex.Internal.LLLState.ofBasis]
    intermediateCoefficientHeight := basisHeight input
    basis_height_le := by simp [Internal.State.initial] }

/-- Mirror one exact dense size-reduction update and its elementary matrix. -/
private def TraceState.sizeReduceColumn {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : TraceState input)
    (column row : Fin m) (less : column.val < row.val) : TraceState input := by
  let coefficient := (state.core.ν.getRow row).get column
  let denominator := state.core.d.get
    ⟨column.val + 1, Nat.succ_lt_succ column.isLt⟩
  if reduce : 2 * Int.natAbs coefficient > denominator then
    let quotient := Hex.Internal.LLLState.nearestQuotient coefficient denominator
    let nextTransform := state.transformState.addRow column row (-quotient)
      (Fin.ne_of_lt less)
    exact
      { core := state.core.sizeReduceColumn column row less
        transformState := nextTransform
        aligned := by
          have current := state.aligned
          change applyRowOperation state.transformState.basis
              (.add column row (-quotient)) =
            ofDense (state.core.sizeReduceColumn column row less).b
          rw [current]
          unfold Hex.Internal.LLLState.sizeReduceColumn
          rw [dif_pos reduce]
          change applyRowOperation (ofDense state.core.b)
              (.add column row (-quotient)) =
            ofDense (Hex.GramSchmidt.Int.sizeReduce state.core.b column row quotient)
          rw [Hex.GramSchmidt.Int.sizeReduce, ofDense_rowAdd]
        intermediateCoefficientHeight :=
          max state.intermediateCoefficientHeight
            (max (basisHeight nextTransform.basis) quotient.natAbs)
        basis_height_le :=
          (le_max_left _ _).trans (le_max_right _ _) }
  else
    exact
      { core := state.core.sizeReduceColumn column row less
        transformState := state.transformState
        aligned := by
          simpa [Hex.Internal.LLLState.sizeReduceColumn, coefficient,
            denominator, reduce] using state.aligned
        intermediateCoefficientHeight := state.intermediateCoefficientHeight
        basis_height_le := state.basis_height_le }

/-- Projection of a traced size-reduction step is exactly the dense step. -/
@[simp] private theorem TraceState.sizeReduceColumn_core {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : TraceState input)
    (column row : Fin m) (less : column.val < row.val) :
    (state.sizeReduceColumn column row less).core =
      state.core.sizeReduceColumn column row less := by
  unfold TraceState.sizeReduceColumn
  dsimp only
  split <;> rfl

/-- A projection commuting with every step commutes with `Fin.foldr`. -/
private theorem foldr_project {State Core : Type _} (project : State → Core) :
    ∀ (count : Nat) (step : Fin count → State → State)
      (coreStep : Fin count → Core → Core),
      (∀ index state, project (step index state) = coreStep index (project state)) →
      ∀ state, project (Fin.foldr count step state) =
        Fin.foldr count coreStep (project state) := by
  intro count
  induction count with
  | zero =>
      intro step coreStep commutes state
      simp
  | succ count inductionHypothesis =>
      intro step coreStep commutes state
      rw [Fin.foldr_succ, Fin.foldr_succ, commutes]
      congr 1
      exact inductionHypothesis (fun index => step index.succ)
        (fun index => coreStep index.succ)
        (fun index next => commutes index.succ next) state

/-- Mirror Hex's descending size-reduction sweep. -/
private def TraceState.sizeReduce {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : TraceState input)
    (k : Nat) : TraceState input :=
  if inRange : k < m then
    let row : Fin m := ⟨k, inRange⟩
    Fin.foldr k
      (fun column next =>
        let column' : Fin m := ⟨column.val, Nat.lt_trans column.isLt inRange⟩
        next.sizeReduceColumn column' row column.isLt)
      state
  else
    state

/-- Projection of the traced sweep is exactly Hex's dense sweep. -/
private theorem TraceState.sizeReduce_core {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : TraceState input) (k : Nat) :
    (state.sizeReduce k).core = state.core.sizeReduce k := by
  unfold TraceState.sizeReduce Hex.Internal.LLLState.sizeReduce
  by_cases inRange : k < m
  · rw [dif_pos inRange, dif_pos inRange]
    exact foldr_project (fun next : TraceState input => next.core) k
      (fun column next =>
        next.sizeReduceColumn
          ⟨column.val, Nat.lt_trans column.isLt inRange⟩ ⟨k, inRange⟩ column.isLt)
      (fun column next =>
        next.sizeReduceColumn
          ⟨column.val, Nat.lt_trans column.isLt inRange⟩ ⟨k, inRange⟩ column.isLt)
      (fun column next => next.sizeReduceColumn_core
        ⟨column.val, Nat.lt_trans column.isLt inRange⟩ ⟨k, inRange⟩ column.isLt)
      state
  · rw [dif_neg inRange, dif_neg inRange]

/-- Mirror one adjacent dense swap and its self-inverse elementary matrix. -/
private def TraceState.swapStep {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : TraceState input)
    (k : Nat) : TraceState input := by
  if inRange : k < m then
    if positive : 0 < k then
      let row : Fin m := ⟨k, inRange⟩
      let previous : Fin m := Hex.GramSchmidt.prevRow row positive
      let nextTransform := state.transformState.swapRows previous row
      exact
        { core := state.core.swapStep k
          transformState := nextTransform
          aligned := by
            change applyRowOperation state.transformState.basis (.swap previous row) =
              ofDense (state.core.swapStep k).b
            rw [state.aligned]
            unfold Hex.Internal.LLLState.swapStep
            rw [dif_pos inRange, dif_pos positive]
            change applyRowOperation (ofDense state.core.b) (.swap previous row) =
              ofDense (Hex.GramSchmidt.Int.adjacentSwap state.core.b row positive)
            rw [Hex.GramSchmidt.Int.adjacentSwap, ofDense_rowSwap]
          intermediateCoefficientHeight :=
            max state.intermediateCoefficientHeight (basisHeight nextTransform.basis)
          basis_height_le := le_max_right _ _ }
    else
      exact
        { core := state.core.swapStep k
          transformState := state.transformState
          aligned := by
            simpa [Hex.Internal.LLLState.swapStep, inRange, positive] using state.aligned
          intermediateCoefficientHeight := state.intermediateCoefficientHeight
          basis_height_le := state.basis_height_le }
  else
    exact
      { core := state.core.swapStep k
        transformState := state.transformState
        aligned := by
          simpa [Hex.Internal.LLLState.swapStep, inRange] using state.aligned
        intermediateCoefficientHeight := state.intermediateCoefficientHeight
        basis_height_le := state.basis_height_le }

/-- Projection of a traced swap is exactly the dense swap. -/
@[simp] private theorem TraceState.swapStep_core {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : TraceState input) (k : Nat) :
    (state.swapStep k).core = state.core.swapStep k := by
  unfold TraceState.swapStep
  dsimp only
  split
  · split <;> rfl
  · rfl

@[simp] private theorem state_addRow_operations_total {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : Internal.State input)
    (source target : Fin m) (coefficient : Int) (distinct : source ≠ target) :
    (state.addRow source target coefficient distinct).operations.total =
      state.operations.total + 2 := by
  simp [Internal.State.addRow, Internal.OperationCount.addSizeReduction,
    Internal.OperationCount.total]
  omega

private theorem TraceState.sizeReduceColumn_operations_total_le {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : TraceState input)
    (column row : Fin m) (less : column.val < row.val) :
    (state.sizeReduceColumn column row less).transformState.operations.total <=
      state.transformState.operations.total + 2 := by
  unfold TraceState.sizeReduceColumn
  dsimp only
  split
  · simp
  · simp

private theorem foldr_nat_le {State : Type _} (project : State -> Nat) :
    forall (count charge : Nat) (step : Fin count -> State -> State),
      (forall index state,
        project (step index state) <= project state + charge) ->
      forall state, project (Fin.foldr count step state) <=
        project state + count * charge := by
  intro count
  induction count with
  | zero =>
      intro charge step stepBound state
      simp
  | succ count inductionHypothesis =>
      intro charge step stepBound state
      rw [Fin.foldr_succ]
      have tailBound := inductionHypothesis charge
        (fun index => step index.succ)
        (fun index next => stepBound index.succ next) state
      have headBound := stepBound (0 : Fin (count + 1))
        (Fin.foldr count (fun index => step index.succ) state)
      calc
        project
              (step 0 (Fin.foldr count (fun index => step index.succ) state)) <=
            project (Fin.foldr count (fun index => step index.succ) state) +
              charge := headBound
        _ <= (project state + count * charge) + charge :=
          Nat.add_le_add_right tailBound charge
        _ = project state + (count + 1) * charge := by ring

private theorem TraceState.sizeReduce_operations_total_le {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : TraceState input) (k : Nat) :
    (state.sizeReduce k).transformState.operations.total <=
      state.transformState.operations.total + 2 * m := by
  unfold TraceState.sizeReduce
  split
  · let row : Fin m := ⟨k, by assumption⟩
    have folded := foldr_nat_le
      (fun next : TraceState input => next.transformState.operations.total)
      k 2
      (fun column next =>
        next.sizeReduceColumn
          ⟨column.val, Nat.lt_trans column.isLt row.isLt⟩ row column.isLt)
      (fun column next => next.sizeReduceColumn_operations_total_le
        ⟨column.val, Nat.lt_trans column.isLt row.isLt⟩ row column.isLt)
      state
    change
      (Fin.foldr k
          (fun column next =>
            next.sizeReduceColumn
              ⟨column.val, Nat.lt_trans column.isLt row.isLt⟩ row column.isLt)
          state).transformState.operations.total <=
        state.transformState.operations.total + 2 * m
    calc
      _ <= state.transformState.operations.total + k * 2 := folded
      _ <= state.transformState.operations.total + 2 * m := by omega
  · omega

@[simp] private theorem state_swapRows_operations_total {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : Internal.State input)
    (left right : Fin m) :
    (state.swapRows left right).operations.total =
      state.operations.total + 2 := by
  simp [Internal.State.swapRows, Internal.OperationCount.addSwap,
    Internal.OperationCount.total]
  omega

private theorem TraceState.swapStep_operations_total_le {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int} (state : TraceState input) (k : Nat) :
    (state.swapStep k).transformState.operations.total <=
      state.transformState.operations.total + 2 := by
  unfold TraceState.swapStep
  dsimp only
  split
  · split
    · simp
    · simp
  · simp

/-- Fuel-bounded traced loop with control flow definitionally matching Hex. -/
private def tracedLoop {m n : Nat} {input : Matrix (Fin m) (Fin n) Int}
    (state : TraceState input) (k : Nat) (parameter : Rat)
    (parameterLower : 1 / 4 < parameter) (parameterUpper : parameter ≤ 1)
    (indexPositive : 1 ≤ k) (indexBounded : k ≤ m) : Nat → TraceState input
  | 0 => state
  | fuel + 1 =>
      if done : k = m then
        state
      else
        have below : k < m := Nat.lt_of_le_of_ne indexBounded done
        have previousBelow : k - 1 < m :=
          Nat.lt_of_le_of_lt (Nat.sub_le k 1) below
        let reduced := state.sizeReduce k
        let row : Fin m := ⟨k, below⟩
        let previous : Fin m := ⟨k - 1, previousBelow⟩
        let previousDeterminant := reduced.core.d.get
          ⟨k - 1, Nat.lt_trans previousBelow (Nat.lt_succ_self m)⟩
        let determinant := reduced.core.d.get ⟨k, Nat.lt_succ_of_lt below⟩
        let nextDeterminant := reduced.core.d.get ⟨k + 1, Nat.succ_lt_succ below⟩
        let coefficient := (reduced.core.ν.getRow row).get previous
        let lhs : Int := Int.ofNat parameter.den *
          (Int.ofNat nextDeterminant * Int.ofNat previousDeterminant + coefficient ^ 2)
        let rhs : Int := parameter.num * (Int.ofNat determinant ^ 2)
        if _lovasz : lhs ≥ rhs then
          tracedLoop reduced (k + 1) parameter parameterLower parameterUpper
            (Nat.succ_pos k) (Nat.succ_le_of_lt below) fuel
        else
          let swapped := reduced.swapStep k
          let nextIndex := max (k - 1) 1
          tracedLoop swapped nextIndex parameter parameterLower parameterUpper
            (Nat.le_max_right (k - 1) 1)
            ((Nat.max_le).2
              ⟨Nat.le_trans (Nat.sub_le k 1) indexBounded,
                Nat.le_trans indexPositive indexBounded⟩)
            fuel

/-- Every traced outer transition has a dimension-only event charge. -/
private theorem tracedLoop_operations_total_le {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int}
    (state : TraceState input) (k : Nat) (parameter : Rat)
    (parameterLower : 1 / 4 < parameter) (parameterUpper : parameter <= 1)
    (indexPositive : 1 <= k) (indexBounded : k <= m) (fuel : Nat) :
    (tracedLoop state k parameter parameterLower parameterUpper
      indexPositive indexBounded fuel).transformState.operations.total <=
      state.transformState.operations.total + lllTrackedEventBound m fuel := by
  induction fuel generalizing state k with
  | zero =>
      simp [tracedLoop, lllTrackedEventBound]
  | succ fuel inductionHypothesis =>
      unfold tracedLoop
      by_cases done : k = m
      · rw [dif_pos done]
        unfold lllTrackedEventBound
        exact Nat.le_add_right _ _
      · rw [dif_neg done]
        have below : k < m := Nat.lt_of_le_of_ne indexBounded done
        let reduced := state.sizeReduce k
        have reducedBound :
            reduced.transformState.operations.total <=
              state.transformState.operations.total + 2 * m :=
          state.sizeReduce_operations_total_le k
        dsimp only
        split
        · have tailBound := inductionHypothesis (state := reduced) (k := k + 1)
            (Nat.succ_pos k) (Nat.succ_le_of_lt below)
          calc
            _ <= reduced.transformState.operations.total +
                lllTrackedEventBound m fuel := tailBound
            _ <= state.transformState.operations.total + 2 * m +
                lllTrackedEventBound m fuel :=
              Nat.add_le_add_right reducedBound _
            _ <= state.transformState.operations.total +
                lllTrackedEventBound m (fuel + 1) := by
              unfold lllTrackedEventBound
              ring_nf
              omega
        · let swapped := reduced.swapStep k
          let nextIndex := max (k - 1) 1
          have swappedBound :
              swapped.transformState.operations.total <=
                reduced.transformState.operations.total + 2 :=
            reduced.swapStep_operations_total_le k
          have tailBound := inductionHypothesis (state := swapped)
            (k := nextIndex) (Nat.le_max_right (k - 1) 1)
            ((Nat.max_le).2
              ⟨Nat.le_trans (Nat.sub_le k 1) indexBounded,
                Nat.le_trans indexPositive indexBounded⟩)
          calc
            _ <= swapped.transformState.operations.total +
                lllTrackedEventBound m fuel := tailBound
            _ <= (reduced.transformState.operations.total + 2) +
                lllTrackedEventBound m fuel :=
              Nat.add_le_add_right swappedBound _
            _ <= ((state.transformState.operations.total + 2 * m) + 2) +
                lllTrackedEventBound m fuel := by
              gcongr
            _ <= state.transformState.operations.total +
                lllTrackedEventBound m (fuel + 1) := by
              unfold lllTrackedEventBound
              ring_nf
              omega

/-- Erasing transform evidence from the trace recovers Hex's loop output. -/
private theorem tracedLoop_core_basis {m n : Nat}
    {input : Matrix (Fin m) (Fin n) Int}
    (state : TraceState input) (k : Nat) (parameter : Rat)
    (parameterLower : 1 / 4 < parameter) (parameterUpper : parameter ≤ 1)
    (indexPositive : 1 ≤ k) (indexBounded : k ≤ m) (fuel : Nat) :
    (tracedLoop state k parameter parameterLower parameterUpper
      indexPositive indexBounded fuel).core.b =
      Hex.Internal.lllLoop state.core k parameter parameterLower parameterUpper
        indexPositive indexBounded fuel := by
  induction fuel generalizing state k with
  | zero =>
      rfl
  | succ fuel inductionHypothesis =>
      unfold tracedLoop Hex.Internal.lllLoop
      by_cases done : k = m
      · rw [dif_pos done, dif_pos done]
      · rw [dif_neg done, dif_neg done]
        have below : k < m := Nat.lt_of_le_of_ne indexBounded done
        let reduced := state.sizeReduce k
        have reducedCore : reduced.core = state.core.sizeReduce k :=
          state.sizeReduce_core k
        simp only [TraceState.sizeReduce_core]
        split
        · simpa only [reducedCore] using
            inductionHypothesis (state := reduced) (k := k + 1)
              (Nat.succ_pos k) (Nat.succ_le_of_lt below)
        · simpa only [TraceState.swapStep_core, reducedCore] using
            inductionHypothesis (state := reduced.swapStep k)
              (k := max (k - 1) 1) (Nat.le_max_right (k - 1) 1)
              ((Nat.max_le).2
                ⟨Nat.le_trans (Nat.sub_le k 1) indexBounded,
                  Nat.le_trans indexPositive indexBounded⟩)

end NormalForms.Research.LLL.Internal.HexTrace

namespace NormalForms.Research.LLL

open Internal.HexTrace

private def fullRankLLLProfileImpl {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (rowsPositive : 1 ≤ m)
    (fullRank : FullRowRankWitness basis) : FullRankLLLProfile basis := by
  have independent : (toDense basis).independent := fullRank.independent
  let initial := TraceState.initial basis
  let parameter : Rat := 3 / 4
  have parameterLower : 1 / 4 < parameter := by
    norm_num [parameter]
  have parameterUpper : parameter ≤ 1 := by
    norm_num [parameter]
  let fuel := fullRankLLLFuel basis
  let final := tracedLoop initial 1 parameter parameterLower parameterUpper
    (Nat.le_refl 1) rowsPositive fuel
  have finalCore : final.core.b =
      Hex.lllNative (toDense basis) parameter parameterLower parameterUpper rowsPositive := by
    simpa [final, fuel, fullRankLLLFuel, initial, TraceState.initial,
      Hex.lllNative, Hex.Internal.lllAux] using
      tracedLoop_core_basis initial 1 parameter parameterLower parameterUpper
        (Nat.le_refl 1) rowsPositive fuel
  have candidateDense : toDense final.transformState.basis = final.core.b := by
    rw [final.aligned, toDense_ofDense]
  have outputIndependent : final.core.b.independent := by
    rw [finalCore]
    exact Hex.lllNative_independent (toDense basis) parameter parameterLower
      parameterUpper rowsPositive independent
  have outputReduced : Hex.isLLLReduced final.core.b delta eta := by
    rw [finalCore]
    simpa [delta, eta, parameter] using
      Hex.lllNative_isLLLReduced (toDense basis) parameter parameterLower
        parameterUpper rowsPositive independent
  have candidateReduced :
      Hex.isLLLReduced (toDense final.transformState.basis) delta eta := by
    rw [candidateDense]
    exact outputReduced
  let result : FullRankLLLResult basis :=
    { U := final.transformState.transform
      U_cert := final.transformState.transformCert
      reducedBasis := final.transformState.basis
      equation := final.transformState.equation
      reduced :=
        { positive := by
            change (toDense final.transformState.basis).independent
            rw [candidateDense]
            exact outputIndependent
          sizeReduced := by
            simpa [IsSizeReduced, Hex.isLLLReduced] using candidateReduced.1
          lovasz := by
            simpa [SatisfiesLovasz, Hex.isLLLReduced] using candidateReduced.2 } }
  let operations : LLLOperationCount :=
    { sizeReductions := final.transformState.operations.sizeReductions
      swaps := final.transformState.operations.swaps
      gramSchmidtRefreshes :=
        final.transformState.operations.gramSchmidtRefreshes }
  have traceBound := tracedLoop_operations_total_le initial 1 parameter
    parameterLower parameterUpper (Nat.le_refl 1) rowsPositive fuel
  have operationBound : operations.total <= lllTrackedEventBound m fuel := by
    simpa [operations, LLLOperationCount.total, final, initial, TraceState.initial,
      Internal.State.initial, Internal.OperationCount.total] using traceBound
  exact
    { result
      fuel
      fuel_eq := rfl
      operations
      operation_bound := operationBound
      intermediateCoefficientHeight := final.intermediateCoefficientHeight
      result_height_le := by
        change basisHeight final.transformState.basis <=
          final.intermediateCoefficientHeight
        exact final.basis_height_le }

/--
Profiled total strong LLL implementation for a nonempty independent row basis.
It returns the semantic result together with the verified event budget and the
observed intermediate basis-height envelope.
-/
public opaque fullRankLLLProfilePositive {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (rowsPositive : 1 ≤ m)
    (fullRank : FullRowRankWitness basis) : FullRankLLLProfile basis :=
  fullRankLLLProfileImpl basis rowsPositive fullRank

/-- Total strong LLL implementation for a nonempty independent row basis.

The opaque boundary keeps trace internals out of downstream native call graphs;
the returned value still contains the computed transform, its explicit inverse,
the transformation equation, and the exact reducedness proof.
-/
public opaque fullRankLLLPositive {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (rowsPositive : 1 ≤ m)
    (fullRank : FullRowRankWitness basis) : FullRankLLLResult basis :=
  (fullRankLLLProfileImpl basis rowsPositive fullRank).result

end NormalForms.Research.LLL
