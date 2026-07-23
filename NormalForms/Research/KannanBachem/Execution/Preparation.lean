/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Determinant
public import NormalForms.Research.KannanBachem.Hermite.PrincipalPreparation

/-! # Value-Producing Principal Preparation -/

public section

namespace NormalForms.Research.KannanBachem

open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminant

/-- A first-nonzero determinant scan and its primitive leaf trace. -/
public structure DeterminantScanExecution (ι : Type*) where
  value : Option ι
  charges : List KannanBachemArithmeticCharge
  trace_wellFormed : ArithmeticChargeListWellFormed charges

/-- Scan left-to-right, branching on the zero-test from the recorded run. -/
@[expose] public def determinantScanExecution {ι : Type*} {n : Nat}
    (matrixAt : ι → Matrix (Fin n) (Fin n) Int) :
    List ι → DeterminantScanExecution ι
  | [] =>
      { value := none
        charges := []
        trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }
  | index :: rest =>
      let determinant := determinantExecution (matrixAt index)
      let zeroRun := isZeroWithCost determinant.value
      let zeroCharge := KannanBachemArithmeticCharge.zeroTestOfRun
        .scalar determinant.value zeroRun rfl
      have zeroWellFormed :
          ArithmeticChargeListWellFormed [zeroCharge] := by
        simp only [ArithmeticChargeListWellFormed, List.forall_cons]
        exact
          ⟨KannanBachemArithmeticCharge.zeroTestOfRun_wellFormed
              .scalar determinant.value zeroRun rfl,
            by simp⟩
      if zeroRun.value then
        let following := determinantScanExecution matrixAt rest
        { value := following.value
          charges := determinant.charges ++
            ([zeroCharge] ++ following.charges)
          trace_wellFormed := determinant.trace_wellFormed.append <|
            zeroWellFormed.append following.trace_wellFormed }
      else
        { value := some index
          charges := determinant.charges ++ [zeroCharge]
          trace_wellFormed :=
            determinant.trace_wellFormed.append zeroWellFormed }

public theorem determinantScanExecution_value {ι : Type*} {n : Nat}
    (matrixAt : ι → Matrix (Fin n) (Fin n) Int) (indices : List ι) :
    (determinantScanExecution matrixAt indices).value =
      (scanFirstNonzeroWithCost matrixAt indices).value := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [determinantScanExecution, scanFirstNonzeroWithCost]
      dsimp only
      by_cases hzero : (evaluateWithCost (matrixAt index)).value = 0
      · have executionZero :
            (determinantExecution (matrixAt index)).value = 0 := by
          rw [determinantExecution_value_eq_evaluateWithCost, hzero]
        have zeroRun :
            (isZeroWithCost
              (determinantExecution (matrixAt index)).value).value := by
          simp [executionZero]
        rw [if_pos zeroRun, if_pos hzero]
        exact ih
      · have executionNonzero :
            (determinantExecution (matrixAt index)).value ≠ 0 := by
          rw [determinantExecution_value_eq_evaluateWithCost]
          exact hzero
        have zeroRun :
            ¬(isZeroWithCost
              (determinantExecution (matrixAt index)).value).value := by
          have decodedNonzero :
              (determinantExecution
                (matrixAt index)).value.value ≠ 0 := by
            intro valueZero
            apply executionNonzero
            apply signMagnitude_value_injective
            simpa using valueZero
          simpa using decodedNonzero
        rw [if_neg zeroRun, if_neg hzero]

public theorem determinantScanExecution_cost_le {ι : Type*} {n : Nat}
    (matrixAt : ι → Matrix (Fin n) (Fin n) Int) (indices : List ι)
    (inputBits : Nat)
    (width : ∀ index ∈ indices,
      matrixBitLength (matrixAt index) ≤ inputBits) :
    traceBitCost (determinantScanExecution matrixAt indices).charges ≤
      indices.length *
        (determinantExecutionBitOperationBound n inputBits + 1) := by
  induction indices with
  | nil => simp [determinantScanExecution, traceBitCost]
  | cons index rest ih =>
      have headWidth := width index (by simp)
      have tailWidth : ∀ next ∈ rest,
          matrixBitLength (matrixAt next) ≤ inputBits := by
        intro next member
        exact width next (by simp [member])
      have determinantCost :
          traceBitCost (determinantExecution (matrixAt index)).charges ≤
            determinantExecutionBitOperationBound n inputBits :=
        (determinantExecution_cost_le (matrixAt index)).trans
          (determinantExecutionBitOperationBound_mono_right n headWidth)
      have tailCost := ih tailWidth
      rw [determinantScanExecution]
      dsimp only
      split
      · rw [traceBitCost_append, traceBitCost_append,
          traceBitCost_singleton_zeroTestOfRun, isZeroWithCost_cost]
        simp only [List.length_cons, Nat.succ_mul]
        omega
      · rw [traceBitCost_append]
        rw [traceBitCost_singleton_zeroTestOfRun, isZeroWithCost_cost]
        simp only [List.length_cons, Nat.succ_mul]
        omega

/-- Leaf-traced scan of all complementary last-column minors. -/
@[expose] public def lastColumnScanExecution {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    DeterminantScanExecution (Fin (n + 1)) :=
  determinantScanExecution (Hermite.Principal.lastColumnMinor A)
    (List.finRange (n + 1))

public theorem lastColumnScanExecution_value {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (lastColumnScanExecution A).value =
      (Hermite.Principal.lastColumnScan A).value := by
  exact determinantScanExecution_value _ _

public theorem lastColumnScanExecution_cost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    traceBitCost (lastColumnScanExecution A).charges ≤
      (n + 1) *
        (determinantExecutionBitOperationBound n
          (matrixBitLength A) + 1) := by
  simpa only [lastColumnScanExecution, List.length_finRange] using
    determinantScanExecution_cost_le
      (Hermite.Principal.lastColumnMinor A)
      (List.finRange (n + 1)) (matrixBitLength A) (by
        intro pivot _member
        exact submatrix_bitLength_le A pivot.succAbove
          (Fin.last n).succAbove)

/-- Recursive row-permutation execution used by principal preparation. -/
public structure ReadyRowPermutationExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) where
  value : Equiv.Perm (Fin n)
  charges : List KannanBachemArithmeticCharge
  value_eq : value = Hermite.Principal.readyRowPermutation A hdet
  trace_wellFormed : ArithmeticChargeListWellFormed charges

@[expose] public def readyRowPermutationExecution : {n : Nat} →
    (A : Matrix (Fin n) (Fin n) Int) → (hdet : A.det ≠ 0) →
      ReadyRowPermutationExecution A hdet
  | 0, _A, _hdet =>
      { value := 1
        charges := []
        value_eq := rfl
        trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }
  | n + 1, A, hdet => by
      let scan := lastColumnScanExecution A
      have scanValue :
          scan.value =
            some (Hermite.Principal.lastColumnPivot A hdet) := by
        rw [lastColumnScanExecution_value]
        exact (Option.some_get _).symm
      exact match scanResult : scan.value with
      | none => by
          rw [scanValue] at scanResult
          contradiction
      | some pivot => by
          have pivotEq :
              pivot = Hermite.Principal.lastColumnPivot A hdet := by
            rw [scanValue] at scanResult
            exact Option.some.inj scanResult.symm
          let minor := Hermite.Principal.lastColumnMinor A pivot
          have minorNonzero : minor.det ≠ 0 := by
            change (Hermite.Principal.lastColumnMinor A pivot).det ≠ 0
            rw [pivotEq]
            exact Hermite.Principal.lastColumnPivot_spec A hdet
          let tail := readyRowPermutationExecution minor minorNonzero
          exact
            { value := Hermite.Principal.appendRowPermutation pivot tail.value
              charges := scan.charges ++ tail.charges
              value_eq := by
                simp only [Hermite.Principal.readyRowPermutation]
                rw [pivotEq]
                congr 1
                simpa only [minor, pivotEq] using tail.value_eq
              trace_wellFormed :=
                scan.trace_wellFormed.append tail.trace_wellFormed }

/-- Closed cost recurrence for all determinant scans in preparation. -/
@[expose] public def preparationExecutionBitOperationBound :
    Nat → Nat → Nat
  | 0, _inputBits => 0
  | n + 1, inputBits =>
      (n + 1) *
          (determinantExecutionBitOperationBound n inputBits + 1) +
        preparationExecutionBitOperationBound n inputBits

public theorem preparationExecutionBitOperationBound_mono_right :
    ∀ dimension {smaller larger : Nat}, smaller ≤ larger →
      preparationExecutionBitOperationBound dimension smaller ≤
        preparationExecutionBitOperationBound dimension larger
  | 0, _, _, _ => by simp [preparationExecutionBitOperationBound]
  | n + 1, smaller, larger, hle => by
      simp only [preparationExecutionBitOperationBound]
      exact Nat.add_le_add
        (Nat.mul_le_mul_left (n + 1)
          (Nat.add_le_add_right
            (determinantExecutionBitOperationBound_mono_right n hle) 1))
        (preparationExecutionBitOperationBound_mono_right n hle)

public theorem readyRowPermutationExecution_cost_le :
    {n : Nat} → (A : Matrix (Fin n) (Fin n) Int) →
      (hdet : A.det ≠ 0) →
      traceBitCost (readyRowPermutationExecution A hdet).charges ≤
        preparationExecutionBitOperationBound n (matrixBitLength A)
  | 0, _A, _hdet => by
      simp [readyRowPermutationExecution,
        preparationExecutionBitOperationBound, traceBitCost]
  | n + 1, A, hdet => by
      let scan := lastColumnScanExecution A
      have scanValue :
          scan.value =
            some (Hermite.Principal.lastColumnPivot A hdet) := by
        rw [lastColumnScanExecution_value]
        exact (Option.some_get _).symm
      rw [readyRowPermutationExecution]
      split
      · rename_i scanResult
        rw [scanValue] at scanResult
        contradiction
      · rename_i pivot scanResult
        have pivotEq :
            pivot = Hermite.Principal.lastColumnPivot A hdet := by
          rw [scanValue] at scanResult
          exact Option.some.inj scanResult.symm
        let minor := Hermite.Principal.lastColumnMinor A pivot
        have minorNonzero : minor.det ≠ 0 := by
          change (Hermite.Principal.lastColumnMinor A pivot).det ≠ 0
          rw [pivotEq]
          exact Hermite.Principal.lastColumnPivot_spec A hdet
        let tail := readyRowPermutationExecution minor minorNonzero
        have scanCost := lastColumnScanExecution_cost_le A
        have tailCost :=
          readyRowPermutationExecution_cost_le minor minorNonzero
        have minorWidth :
            matrixBitLength minor ≤ matrixBitLength A := by
          exact submatrix_bitLength_le A pivot.succAbove
            (Fin.last n).succAbove
        have tailCost' :
            traceBitCost tail.charges ≤
              preparationExecutionBitOperationBound n
                (matrixBitLength A) :=
          tailCost.trans
            (preparationExecutionBitOperationBound_mono_right n minorWidth)
        rw [traceBitCost_append]
        change traceBitCost scan.charges + traceBitCost tail.charges ≤ _
        simp only [preparationExecutionBitOperationBound]
        exact Nat.add_le_add scanCost tailCost'

/-- Value-producing principal preparation and its determinant trace. -/
public structure PreparationExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) where
  value : Hermite.Principal.Preparation A
  charges : List KannanBachemArithmeticCharge
  value_eq : value = Hermite.Principal.prepare A hdet
  trace_wellFormed : ArithmeticChargeListWellFormed charges

private theorem preparation_ext {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (left right : Hermite.Principal.Preparation A)
    (rowPermutation_eq :
      left.rowPermutation = right.rowPermutation) :
    left = right := by
  cases left
  cases right
  simp_all

@[expose] public def preparationExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    PreparationExecution A hdet := by
  let permutation := readyRowPermutationExecution A hdet
  let value : Hermite.Principal.Preparation A :=
    { rowPermutation := permutation.value
      ready := by
        rw [permutation.value_eq]
        exact Hermite.Principal.readyRowPermutation_ready A hdet }
  exact
    { value
      charges := permutation.charges
      value_eq := by
        apply preparation_ext
        exact permutation.value_eq
      trace_wellFormed := permutation.trace_wellFormed }

public theorem preparationExecution_value {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (preparationExecution A hdet).value =
      Hermite.Principal.prepare A hdet :=
  (preparationExecution A hdet).value_eq

public theorem preparationExecution_cost_le {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    traceBitCost (preparationExecution A hdet).charges ≤
      preparationExecutionBitOperationBound n (matrixBitLength A) := by
  exact readyRowPermutationExecution_cost_le A hdet

end NormalForms.Research.KannanBachem
