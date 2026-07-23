/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Pass
public import NormalForms.Research.KannanBachem.Smith.Search

/-! # Costed Smith Searches -/

public section

namespace NormalForms.Research.KannanBachem

open NormalForms
open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Smith

/-- One divisibility decision and its non-overlapping primitive leaves. -/
public structure DvdExecution (divisor dividend : SignMagnitude) where
  value : Bool
  charges : List KannanBachemArithmeticCharge
  trace_wellFormed : ArithmeticChargeListWellFormed charges
  value_eq : value = (dvdWithCost divisor dividend).value

/--
Execute divisibility.  The nonzero branch owns one search division; the zero
branch owns only its two zero tests.
-/
@[expose] public def dvdExecution
    (location : ArithmeticChargeLocation)
    (divisor dividend : SignMagnitude) : DvdExecution divisor dividend :=
  let ownedLocation := ArithmeticChargeLocation.ofIndices .smithSearch
    location.dimension location.indices location.indices_valid
  let divisorZero := isZeroWithCost divisor
  let divisorCharge := KannanBachemArithmeticCharge.zeroTestOfRun
    ownedLocation divisor divisorZero rfl
  if _hzero : divisorZero.value then
    let dividendZero := isZeroWithCost dividend
    let dividendCharge := KannanBachemArithmeticCharge.zeroTestOfRun
      ownedLocation dividend dividendZero rfl
    { value := dividendZero.value
      charges := [divisorCharge, dividendCharge]
      trace_wellFormed := by
        simp only [ArithmeticChargeListWellFormed, List.forall_cons]
        exact
          ⟨KannanBachemArithmeticCharge.zeroTestOfRun_wellFormed
              ownedLocation divisor divisorZero rfl,
            KannanBachemArithmeticCharge.zeroTestOfRun_wellFormed
              ownedLocation dividend dividendZero rfl,
            by simp⟩
      value_eq := by
        rw [dvdWithCost, if_pos _hzero] }
  else
    let division := divModWithCost dividend divisor
    let divisionCharge := KannanBachemArithmeticCharge.divModOfRun
      ownedLocation .smithSearch dividend divisor division rfl (by trivial)
    let remainderZero := isZeroWithCost division.value.remainder
    let remainderCharge := KannanBachemArithmeticCharge.zeroTestOfRun
      ownedLocation division.value.remainder remainderZero rfl
    { value := remainderZero.value
      charges := [divisorCharge, divisionCharge, remainderCharge]
      trace_wellFormed := by
        simp only [ArithmeticChargeListWellFormed, List.forall_cons]
        exact
          ⟨KannanBachemArithmeticCharge.zeroTestOfRun_wellFormed
              ownedLocation divisor divisorZero rfl,
            KannanBachemArithmeticCharge.divModOfRun_wellFormed
              ownedLocation .smithSearch dividend divisor division rfl (by
                trivial),
            KannanBachemArithmeticCharge.zeroTestOfRun_wellFormed
              ownedLocation division.value.remainder remainderZero rfl,
            by simp⟩
      value_eq := by
        rw [dvdWithCost, if_neg _hzero] }

public theorem dvdExecution_value
    (location : ArithmeticChargeLocation)
    (divisor dividend : SignMagnitude) :
    (dvdExecution location divisor dividend).value =
      decide (divisor.value ∣ dividend.value) := by
  rw [(dvdExecution location divisor dividend).value_eq,
    dvdWithCost_value]

public theorem dvdExecution_traceBitCost
    (location : ArithmeticChargeLocation)
    (divisor dividend : SignMagnitude) :
    traceBitCost (dvdExecution location divisor dividend).charges =
      (dvdWithCost divisor dividend).cost := by
  rw [dvdExecution]
  split
  next hzero =>
    have valueZero : divisor.value = 0 := by
      simpa using hzero
    simp [traceBitCost, dvdWithCost, valueZero]
  next hnonzero =>
    have valueNonzero : divisor.value ≠ 0 := by
      intro valueZero
      apply hnonzero
      simp [valueZero]
    simp [traceBitCost, dvdWithCost, valueNonzero, Nat.add_assoc]

/-- A value-producing optional search with a flat arithmetic trace. -/
public structure SearchExecution (α : Type) where
  value : Option α
  charges : List KannanBachemArithmeticCharge
  trace_wellFormed : ArithmeticChargeListWellFormed charges

/-- Search a vector for its first entry not divisible by `pivot`. -/
@[expose] public def firstUndivisibleIndexExecution : {n : Nat} →
    (pivot : Int) → (entries : Fin n → Int) →
      (locations : Fin n → ArithmeticChargeLocation) → SearchExecution (Fin n)
  | 0, _, _, _ =>
      { value := none, charges := []
        trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }
  | _n + 1, pivot, entries, locations =>
      let current := dvdExecution (locations 0)
        (SignMagnitude.ofInt pivot) (SignMagnitude.ofInt (entries 0))
      if current.value then
        let tail := firstUndivisibleIndexExecution pivot
          (fun index ↦ entries index.succ)
          (fun index ↦ locations index.succ)
        { value := Option.map Fin.succ tail.value
          charges := current.charges ++ tail.charges
          trace_wellFormed :=
            current.trace_wellFormed.append tail.trace_wellFormed }
      else
        { value := some 0
          charges := current.charges
          trace_wellFormed := current.trace_wellFormed }

public theorem firstUndivisibleIndexExecution_value :
    {n : Nat} → (pivot : Int) → (entries : Fin n → Int) →
      (locations : Fin n → ArithmeticChargeLocation) →
        (firstUndivisibleIndexExecution pivot entries locations).value =
          firstUndivisibleIndex? pivot entries
  | 0, _, _, _ => rfl
  | _n + 1, pivot, entries, locations => by
      by_cases hdiv : pivot ∣ entries 0
      · have executionTrue :
            (dvdExecution (locations 0)
              (SignMagnitude.ofInt pivot)
              (SignMagnitude.ofInt (entries 0))).value = true := by
          simpa [hdiv] using dvdExecution_value (locations 0)
            (SignMagnitude.ofInt pivot)
            (SignMagnitude.ofInt (entries 0))
        have pureTrue :
            ComputableEuclideanOps.dvdB pivot (entries 0) = true :=
          (ComputableEuclideanOps.dvdB_eq_true_iff _ _).2 hdiv
        simp only [firstUndivisibleIndexExecution, executionTrue, if_true,
          firstUndivisibleIndex?, pureTrue]
        rw [firstUndivisibleIndexExecution_value]
      · have executionFalse :
            (dvdExecution (locations 0)
              (SignMagnitude.ofInt pivot)
              (SignMagnitude.ofInt (entries 0))).value = false := by
          simpa [hdiv] using dvdExecution_value (locations 0)
            (SignMagnitude.ofInt pivot)
            (SignMagnitude.ofInt (entries 0))
        have pureFalse :
            ComputableEuclideanOps.dvdB pivot (entries 0) ≠ true := by
          simpa [ComputableEuclideanOps.dvdB_eq_true_iff] using hdiv
        simp [firstUndivisibleIndexExecution, executionFalse,
          firstUndivisibleIndex?, pureFalse]

/-- Cost of inspecting every entry of a vector. -/
@[expose] public def firstUndivisibleIndexCostBound : {n : Nat} →
    Int → (Fin n → Int) → Nat
  | 0, _, _ => 0
  | _n + 1, pivot, entries =>
      (dvdWithCost (SignMagnitude.ofInt pivot)
          (SignMagnitude.ofInt (entries 0))).cost +
        firstUndivisibleIndexCostBound pivot
          (fun index ↦ entries index.succ)

public theorem firstUndivisibleIndexExecution_cost_le :
    {n : Nat} → (pivot : Int) → (entries : Fin n → Int) →
      (locations : Fin n → ArithmeticChargeLocation) →
        traceBitCost
            (firstUndivisibleIndexExecution pivot entries locations).charges ≤
          firstUndivisibleIndexCostBound pivot entries
  | 0, _, _, _ => by simp [firstUndivisibleIndexExecution,
      firstUndivisibleIndexCostBound, traceBitCost]
  | _n + 1, pivot, entries, locations => by
      rw [firstUndivisibleIndexExecution]
      let current := dvdExecution (locations 0)
        (SignMagnitude.ofInt pivot) (SignMagnitude.ofInt (entries 0))
      by_cases hcurrent : current.value = true
      · rw [if_pos hcurrent, traceBitCost_append,
          dvdExecution_traceBitCost]
        exact Nat.add_le_add_left
          (firstUndivisibleIndexExecution_cost_le pivot
            (fun index ↦ entries index.succ)
            (fun index ↦ locations index.succ)) _
      · rw [if_neg hcurrent, dvdExecution_traceBitCost,
          firstUndivisibleIndexCostBound]
        exact Nat.le_add_right _ _

/-- Checked search location below the pivot. -/
@[expose] public def belowSearchLocation {n : Nat}
    (row : Fin n) : ArithmeticChargeLocation :=
  ArithmeticChargeLocation.ofIndices .smithSearch (n + 1)
    [0, row.succ.val] (by
      intro index member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · omega
      · exact row.succ.isLt)

/-- Costed first below-pivot divisibility witness. -/
@[expose] public def firstUndivisibleBelowWithCost {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    SearchExecution (Fin n) :=
  firstUndivisibleIndexExecution (A 0 0)
    (fun row ↦ A row.succ 0) belowSearchLocation

public theorem firstUndivisibleBelowWithCost_value {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (firstUndivisibleBelowWithCost A).value =
      firstUndivisibleBelow? A :=
  firstUndivisibleIndexExecution_value (A 0 0)
    (fun row ↦ A row.succ 0) belowSearchLocation

/-- A closed bound: searching never exceeds charging every below-pivot entry. -/
@[expose] public def firstUndivisibleBelowCostBound {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Nat :=
  firstUndivisibleIndexCostBound (A 0 0)
    (fun row ↦ A row.succ 0)

public theorem firstUndivisibleBelowWithCost_cost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    traceBitCost (firstUndivisibleBelowWithCost A).charges ≤
      firstUndivisibleBelowCostBound A := by
  exact firstUndivisibleIndexExecution_cost_le (A 0 0)
    (fun row ↦ A row.succ 0) belowSearchLocation

/-- Checked row-major location in the strict lower-right block. -/
@[expose] public def lowerSearchLocation {n : Nat}
    (row column : Fin n) : ArithmeticChargeLocation :=
  ArithmeticChargeLocation.ofIndices .smithSearch (n + 1)
    [0, row.succ.val, column.succ.val] (by
      intro index member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · omega
      · exact row.succ.isLt
      · exact column.succ.isLt)

/-- Row-major costed search of a rectangular block. -/
@[expose] public def firstUndivisibleMatrixExecution : {m n : Nat} →
    (pivot : Int) → (entries : Fin m → Fin n → Int) →
      (locations : Fin m → Fin n → ArithmeticChargeLocation) →
        SearchExecution (Fin m × Fin n)
  | 0, _, _, _, _ =>
      { value := none, charges := []
        trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }
  | _m + 1, n, pivot, entries, locations =>
      let row := firstUndivisibleIndexExecution pivot (entries 0) (locations 0)
      match row.value with
      | some column =>
          { value := some (0, column)
            charges := row.charges
            trace_wellFormed := row.trace_wellFormed }
      | none =>
          let tail := firstUndivisibleMatrixExecution pivot
            (fun row column ↦ entries row.succ column)
            (fun row column ↦ locations row.succ column)
          { value := Option.map
              (fun position ↦ (position.1.succ, position.2)) tail.value
            charges := row.charges ++ tail.charges
            trace_wellFormed :=
              row.trace_wellFormed.append tail.trace_wellFormed }

public theorem firstUndivisibleMatrixExecution_value :
    {m n : Nat} → (pivot : Int) → (entries : Fin m → Fin n → Int) →
      (locations : Fin m → Fin n → ArithmeticChargeLocation) →
        (firstUndivisibleMatrixExecution pivot entries locations).value =
          firstUndivisibleMatrix? pivot entries
  | 0, _, _, _, _ => rfl
  | _m + 1, n, pivot, entries, locations => by
      rw [firstUndivisibleMatrixExecution]
      have rowValue := firstUndivisibleIndexExecution_value pivot
        (entries 0) (locations 0)
      cases rowResult : firstUndivisibleIndex? pivot (entries 0) with
      | some column =>
          have executionResult :
              (firstUndivisibleIndexExecution pivot
                (entries 0) (locations 0)).value = some column :=
            rowValue.trans rowResult
          simp [executionResult, firstUndivisibleMatrix?, rowResult]
      | none =>
          have executionResult :
              (firstUndivisibleIndexExecution pivot
                (entries 0) (locations 0)).value = none :=
            rowValue.trans rowResult
          simp only [executionResult, firstUndivisibleMatrix?, rowResult]
          rw [firstUndivisibleMatrixExecution_value]

/-- Cost of inspecting every entry of a rectangular block. -/
@[expose] public def firstUndivisibleMatrixCostBound : {m n : Nat} →
    Int → (Fin m → Fin n → Int) → Nat
  | 0, _, _, _ => 0
  | _m + 1, _n, pivot, entries =>
      firstUndivisibleIndexCostBound pivot (entries 0) +
        firstUndivisibleMatrixCostBound pivot
          (fun row column ↦ entries row.succ column)

public theorem firstUndivisibleMatrixExecution_cost_le :
    {m n : Nat} → (pivot : Int) → (entries : Fin m → Fin n → Int) →
      (locations : Fin m → Fin n → ArithmeticChargeLocation) →
        traceBitCost
            (firstUndivisibleMatrixExecution pivot entries locations).charges ≤
          firstUndivisibleMatrixCostBound pivot entries
  | 0, _, _, _, _ => by simp [firstUndivisibleMatrixExecution,
      firstUndivisibleMatrixCostBound, traceBitCost]
  | _m + 1, n, pivot, entries, locations => by
      rw [firstUndivisibleMatrixExecution]
      let row := firstUndivisibleIndexExecution pivot (entries 0) (locations 0)
      cases hrow : row.value with
      | some column =>
          rw [firstUndivisibleMatrixCostBound]
          exact (firstUndivisibleIndexExecution_cost_le pivot
            (entries 0) (locations 0)).trans (Nat.le_add_right _ _)
      | none =>
          rw [traceBitCost_append, firstUndivisibleMatrixCostBound]
          exact Nat.add_le_add
            (firstUndivisibleIndexExecution_cost_le pivot
              (entries 0) (locations 0))
            (firstUndivisibleMatrixExecution_cost_le pivot
              (fun row column ↦ entries row.succ column)
              (fun row column ↦ locations row.succ column))

/-- Costed first lower-right divisibility witness. -/
@[expose] public def firstUndivisibleLowerWithCost {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    SearchExecution (Fin n × Fin n) :=
  firstUndivisibleMatrixExecution (A 0 0)
    (fun row column ↦ A row.succ column.succ) lowerSearchLocation

public theorem firstUndivisibleLowerWithCost_value {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (firstUndivisibleLowerWithCost A).value =
      firstUndivisibleLower? A :=
  firstUndivisibleMatrixExecution_value (A 0 0)
    (fun row column ↦ A row.succ column.succ) lowerSearchLocation

@[expose] public def firstUndivisibleLowerCostBound {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Nat :=
  firstUndivisibleMatrixCostBound (A 0 0)
    (fun row column ↦ A row.succ column.succ)

public theorem firstUndivisibleLowerWithCost_cost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    traceBitCost (firstUndivisibleLowerWithCost A).charges ≤
      firstUndivisibleLowerCostBound A := by
  exact firstUndivisibleMatrixExecution_cost_le (A 0 0)
    (fun row column ↦ A row.succ column.succ) lowerSearchLocation

/-- One divisibility decision at a uniform coefficient width. -/
@[expose] public def smithSearchDecisionBitOperationBound
    (operandBits : Nat) : Nat :=
  2 + divisionCostForBitLengths operandBits operandBits

private theorem dvdWithCost_cost_le_uniform
    (divisor dividend : SignMagnitude) (operandBits : Nat)
    (divisorWidth : divisor.bitLength ≤ operandBits)
    (dividendWidth : dividend.bitLength ≤ operandBits) :
    (dvdWithCost divisor dividend).cost ≤
      smithSearchDecisionBitOperationBound operandBits := by
  rw [dvdWithCost]
  split
  · simp [smithSearchDecisionBitOperationBound]
  · have divisionCost :=
      (divModWithCost_cost_le dividend divisor).trans <|
        Internal.divModBitOperationBound_le_lengths dividend divisor
          operandBits operandBits dividendWidth divisorWidth
    simp only [isZeroWithCost_cost]
    unfold smithSearchDecisionBitOperationBound
    omega

private theorem firstUndivisibleIndexCostBound_le :
    {n : Nat} → (pivot : Int) → (entries : Fin n → Int) →
      (operandBits : Nat) →
      Nat.size pivot.natAbs ≤ operandBits →
      (∀ index, Nat.size (entries index).natAbs ≤ operandBits) →
      firstUndivisibleIndexCostBound pivot entries ≤
        n * smithSearchDecisionBitOperationBound operandBits
  | 0, _, _, _, _, _ => by simp [firstUndivisibleIndexCostBound]
  | n + 1, pivot, entries, operandBits, pivotWidth, entryWidths => by
      have headCost := dvdWithCost_cost_le_uniform
        (SignMagnitude.ofInt pivot) (SignMagnitude.ofInt (entries 0))
        operandBits (by
          simpa only [SignMagnitude.bitLength_eq_natSize_natAbs,
            SignMagnitude.value_ofInt] using pivotWidth)
        (by
          simpa only [SignMagnitude.bitLength_eq_natSize_natAbs,
            SignMagnitude.value_ofInt] using entryWidths 0)
      have tailCost := firstUndivisibleIndexCostBound_le pivot
        (fun index ↦ entries index.succ) operandBits pivotWidth
        (fun index ↦ entryWidths index.succ)
      rw [firstUndivisibleIndexCostBound, Nat.add_mul, one_mul]
      omega

private theorem firstUndivisibleMatrixCostBound_le :
    {m n : Nat} → (pivot : Int) → (entries : Fin m → Fin n → Int) →
      (operandBits : Nat) →
      Nat.size pivot.natAbs ≤ operandBits →
      (∀ row column, Nat.size (entries row column).natAbs ≤ operandBits) →
      firstUndivisibleMatrixCostBound pivot entries ≤
        m * n * smithSearchDecisionBitOperationBound operandBits
  | 0, _, _, _, _, _, _ => by simp [firstUndivisibleMatrixCostBound]
  | m + 1, n, pivot, entries, operandBits, pivotWidth, entryWidths => by
      have rowCost := firstUndivisibleIndexCostBound_le pivot
        (entries 0) operandBits pivotWidth (entryWidths 0)
      have tailCost := firstUndivisibleMatrixCostBound_le pivot
        (fun row column ↦ entries row.succ column)
        operandBits pivotWidth
        (fun row column ↦ entryWidths row.succ column)
      rw [firstUndivisibleMatrixCostBound, Nat.add_mul, one_mul]
      nlinarith

public theorem firstUndivisibleBelowWithCost_cost_le_uniform {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (operandBits : Nat) (matrixBound : Hermite.matrixBitLength A ≤ operandBits) :
    traceBitCost (firstUndivisibleBelowWithCost A).charges ≤
      n * smithSearchDecisionBitOperationBound operandBits := by
  apply (firstUndivisibleBelowWithCost_cost_le A).trans
  apply firstUndivisibleIndexCostBound_le
  · exact (Hermite.entry_bitLength_le_matrixBitLength A 0 0).trans matrixBound
  · intro row
    exact (Hermite.entry_bitLength_le_matrixBitLength A row.succ 0).trans
      matrixBound

public theorem firstUndivisibleLowerWithCost_cost_le_uniform {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (operandBits : Nat) (matrixBound : Hermite.matrixBitLength A ≤ operandBits) :
    traceBitCost (firstUndivisibleLowerWithCost A).charges ≤
      n * n * smithSearchDecisionBitOperationBound operandBits := by
  apply (firstUndivisibleLowerWithCost_cost_le A).trans
  apply firstUndivisibleMatrixCostBound_le
  · exact (Hermite.entry_bitLength_le_matrixBitLength A 0 0).trans matrixBound
  · intro row column
    exact
      (Hermite.entry_bitLength_le_matrixBitLength
        A row.succ column.succ).trans matrixBound

end NormalForms.Research.KannanBachem
