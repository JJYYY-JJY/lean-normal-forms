/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Search
public import NormalForms.Research.KannanBachem.Smith.Clear

/-! # Instrumented Smith Clear and Injection -/

public section

namespace NormalForms.Research.KannanBachem

open scoped Matrix
open NormalForms
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

/-- One contracted exact quotient used by the simultaneous clearing shear. -/
public structure ClearQuotientExecution
    (numerator divisor : SignMagnitude) where
  value : SignMagnitude
  charge : KannanBachemArithmeticCharge
  charge_wellFormed : charge.WellFormed
  value_eq : value.value = numerator.value / divisor.value

/-- Checked location for one first-column exact division. -/
@[expose] public def clearLocation {n : Nat}
    (row : Fin n) : ArithmeticChargeLocation :=
  ArithmeticChargeLocation.ofIndices .smithClear (n + 1)
    [0, row.succ.val] (by
      intro index member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · omega
      · exact row.succ.isLt)

/-- Execute one exact clearing quotient from one shared long division. -/
@[expose] public def clearQuotientExecution
    (location : ArithmeticChargeLocation)
    (numerator divisor : SignMagnitude)
    (_divisor_ne_zero : divisor.value ≠ 0)
    (_divides : divisor.value ∣ numerator.value) :
    ClearQuotientExecution numerator divisor :=
  let ownedLocation := ArithmeticChargeLocation.ofIndices .smithClear
    location.dimension location.indices location.indices_valid
  let division := divModWithCost numerator divisor
  let charge := KannanBachemArithmeticCharge.divModOfRun
    ownedLocation .smithClear numerator divisor division rfl (by trivial)
  { value := division.value.quotient
    charge
    charge_wellFormed :=
      KannanBachemArithmeticCharge.divModOfRun_wellFormed
        ownedLocation .smithClear numerator divisor division rfl (by trivial)
    value_eq := divModWithCost_quotient_value numerator divisor }

/-- Exact quotient executions for every below-pivot row. -/
@[expose] public def clearQuotients {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hpivot : A 0 0 ≠ 0)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0)
    (row : Fin n) :
    ClearQuotientExecution
      (SignMagnitude.ofInt (A row.succ 0))
      (SignMagnitude.ofInt (A 0 0)) :=
  clearQuotientExecution (clearLocation row)
    (SignMagnitude.ofInt (A row.succ 0))
    (SignMagnitude.ofInt (A 0 0))
    (by simpa only [SignMagnitude.value_ofInt] using hpivot)
    (by simpa only [SignMagnitude.value_ofInt] using hdiv row)

/-- Clearing coefficients produced by those same quotient executions. -/
@[expose] public def clearExecutionCoefficients {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hpivot : A 0 0 ≠ 0)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0) :
    Fin n → Int :=
  fun row ↦ -(clearQuotients A hpivot hdiv row).value.value

public theorem clearExecutionCoefficients_eq {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hpivot : A 0 0 ≠ 0)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0) :
    clearExecutionCoefficients A hpivot hdiv =
      firstColumnClearCoefficient A := by
  funext row
  rw [clearExecutionCoefficients, firstColumnClearCoefficient,
    (clearQuotients A hpivot hdiv row).value_eq,
    ComputableEuclideanOps.quot_eq]
  simp only [SignMagnitude.value_ofInt]

/-- Exact-division leaves in row order. -/
@[expose] public def clearDivisionCharges {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hpivot : A 0 0 ≠ 0)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0) :
    List KannanBachemArithmeticCharge :=
  (List.finRange n).map fun row ↦
    (clearQuotients A hpivot hdiv row).charge

public theorem clearDivisionCharges_wellFormed {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hpivot : A 0 0 ≠ 0)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0) :
    ArithmeticChargeListWellFormed
      (clearDivisionCharges A hpivot hdiv) := by
  rw [ArithmeticChargeListWellFormed, List.forall_iff_forall_mem]
  intro charge member
  rw [clearDivisionCharges, List.mem_map] at member
  obtain ⟨row, _rowMember, rfl⟩ := member
  exact (clearQuotients A hpivot hdiv row).charge_wellFormed

/-- Clear a divisible first column using exact quotients and one actual product. -/
@[expose] public def clearExecution {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hpivot : A 0 0 ≠ 0)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0) :
    CertificateExecution A := by
  let coefficients := clearExecutionCoefficients A hpivot hdiv
  let forward := firstColumnShear coefficients
  let product := matrixProductExecution forward A
  have productValue : product.value = forward * A :=
    matrixProductExecution_value _ _
  let value : TwoSidedCertificate A :=
    { U := forward
      U_cert := firstColumnShearCertificate coefficients
      result := product.value
      V := 1
      V_cert := MatrixInverseCertificate.one
      equation := by
        rw [Matrix.mul_one, productValue] }
  let charges := clearDivisionCharges A hpivot hdiv ++ product.charges
  have chargesWellFormed : ArithmeticChargeListWellFormed charges :=
    (clearDivisionCharges_wellFormed A hpivot hdiv).append
      product.trace_wellFormed
  exact
    { value
      charges
      trace_wellFormed := chargesWellFormed
      chargeOwnership := List.forall_iff_forall_mem.mp chargesWellFormed }

public theorem clearExecution_value {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hpivot : A 0 0 ≠ 0)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0) :
    (clearExecution A hpivot hdiv).value =
      clearDivisibleFirstColumn A := by
  apply twoSidedCertificate_ext_data
  · exact congrArg firstColumnShear
      (clearExecutionCoefficients_eq A hpivot hdiv)
  · exact congrArg (fun coefficients ↦
      (firstColumnShearCertificate coefficients).inverse)
      (clearExecutionCoefficients_eq A hpivot hdiv)
  · change
      (matrixProductExecution
        (firstColumnShear (clearExecutionCoefficients A hpivot hdiv))
        A).value =
          firstColumnShear (firstColumnClearCoefficient A) * A
    rw [matrixProductExecution_value,
      clearExecutionCoefficients_eq]
  · rfl
  · rfl

/-- Step-7 injection with its result constructed by one actual dense product. -/
@[expose] public def injectExecution {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (column : Fin n) : CertificateExecution A := by
  let forward := columnOperationMatrix
    (ColumnOperation.add column.succ 0 (1 : Int))
  let product := matrixProductExecution A forward
  have productValue : product.value = A * forward :=
    matrixProductExecution_value _ _
  let value : TwoSidedCertificate A :=
    { U := 1
      U_cert := MatrixInverseCertificate.one
      result := product.value
      V := forward
      V_cert := columnAddCertificate column.succ 0 1 (by simp)
      equation := by rw [Matrix.one_mul, productValue] }
  exact
    { value
      charges := product.charges
      trace_wellFormed := product.trace_wellFormed
      chargeOwnership := List.forall_iff_forall_mem.mp
        product.trace_wellFormed }

public theorem injectExecution_value {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (column : Fin n) :
    (injectExecution A column).value = injectLowerWitness A column := by
  apply twoSidedCertificate_ext_data
  · rfl
  · rfl
  · change
      (matrixProductExecution A
        (columnOperationMatrix
          (ColumnOperation.add column.succ 0 (1 : Int)))).value =
        applyColumnOperation A (.add column.succ 0 1)
    rw [matrixProductExecution_value, mul_columnOperationMatrix]
  · rfl
  · rfl

/-- Uniform cost of the exact-division leaves and one clearing product. -/
@[expose] public def clearExecutionBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  (dimension - 1) *
      Principal.integerDivModBitOperationBound inputBits +
    matrixMultiplicationBitOperationBound dimension (inputBits + 1) inputBits

private theorem clearDivisionCharges_cost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hpivot : A 0 0 ≠ 0)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0) :
    traceBitCost (clearDivisionCharges A hpivot hdiv) ≤
      n * Principal.integerDivModBitOperationBound (matrixBitLength A) := by
  unfold clearDivisionCharges traceBitCost
  simp only [List.map_map]
  have bound := List.sum_le_card_nsmul
    (List.map
      (KannanBachemArithmeticCharge.bitCost ∘
        fun row ↦ (clearQuotients A hpivot hdiv row).charge)
      (List.finRange n))
    (Principal.integerDivModBitOperationBound (matrixBitLength A)) (by
      intro cost member
      rw [List.mem_map] at member
      obtain ⟨row, _rowMember, rfl⟩ := member
      change
        (divModWithCost
          (SignMagnitude.ofInt (A row.succ 0))
          (SignMagnitude.ofInt (A 0 0))).cost ≤
            Principal.integerDivModBitOperationBound (matrixBitLength A)
      exact (divModWithCost_cost_le _ _).trans <|
        Internal.divModBitOperationBound_le_lengths _ _
          (matrixBitLength A) (matrixBitLength A)
          (by
            have width :=
              entry_bitLength_le_matrixBitLength A row.succ 0
            change Nat.size (A row.succ 0).natAbs ≤ matrixBitLength A at width
            simpa only [SignMagnitude.bitLength_eq_natSize_natAbs,
              SignMagnitude.value_ofInt] using width)
          (by
            have width := entry_bitLength_le_matrixBitLength A 0 0
            change Nat.size (A 0 0).natAbs ≤ matrixBitLength A at width
            simpa only [SignMagnitude.bitLength_eq_natSize_natAbs,
              SignMagnitude.value_ofInt] using width))
  simpa using bound

public theorem clearExecution_cost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hpivot : A 0 0 ≠ 0)
    (hdiv : ∀ row : Fin n, A 0 0 ∣ A row.succ 0) :
    traceBitCost (clearExecution A hpivot hdiv).charges ≤
      clearExecutionBitOperationBound (n + 1) (matrixBitLength A) := by
  let coefficients := clearExecutionCoefficients A hpivot hdiv
  let forward := firstColumnShear coefficients
  have forwardBound : matrixBitLength forward ≤ matrixBitLength A + 1 := by
    have transformBound := clear_transformBitLength_le A
    have component :
        matrixBitLength (clearDivisibleFirstColumn A).U ≤
          matrixBitLength A + 1 :=
      (le_max_left _ _).trans transformBound
    simpa [forward, coefficients, clearDivisibleFirstColumn,
      clearExecutionCoefficients_eq A hpivot hdiv] using component
  have productCost :
      traceBitCost (matrixProductExecution forward A).charges ≤
        matrixMultiplicationBitOperationBound (n + 1)
          (matrixBitLength A + 1) (matrixBitLength A) := by
    rw [matrixProductExecution_cost_eq]
    exact matrixMultiplicationBitOperationCost_le
      forward A forwardBound le_rfl
  change
    traceBitCost
        (clearDivisionCharges A hpivot hdiv ++
          (matrixProductExecution forward A).charges) ≤ _
  rw [traceBitCost_append]
  unfold clearExecutionBitOperationBound
  simp only [Nat.add_sub_cancel]
  exact Nat.add_le_add
    (clearDivisionCharges_cost_le A hpivot hdiv) productCost

public theorem clearExecutionBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    clearExecutionBitOperationBound dimension smaller ≤
      clearExecutionBitOperationBound dimension larger := by
  unfold clearExecutionBitOperationBound
  exact Nat.add_le_add
    (Nat.mul_le_mul_left (dimension - 1) <|
      (by
        unfold Principal.integerDivModBitOperationBound
          divisionCostForBitLengths
        gcongr))
    (matrixMultiplicationBitOperationBound_mono dimension
      (Nat.add_le_add_right hle 1) hle)

/-- Uniform cost of the single dense Step-7 product. -/
@[expose] public def injectExecutionBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  matrixMultiplicationBitOperationBound dimension inputBits 1

public theorem injectExecution_cost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (column : Fin n) :
    traceBitCost (injectExecution A column).charges ≤
      injectExecutionBitOperationBound (n + 1) (matrixBitLength A) := by
  change
    traceBitCost
      (matrixProductExecution A
        (columnOperationMatrix
          (ColumnOperation.add column.succ 0 (1 : Int)))).charges ≤ _
  rw [matrixProductExecution_cost_eq]
  unfold injectExecutionBitOperationBound
  have transformBound := injection_transformBitLength_le A column
  have forwardBound :
      matrixBitLength
          (columnOperationMatrix
            (ColumnOperation.add column.succ 0 (1 : Int))) ≤ 1 := by
    have component :
        matrixBitLength (injectLowerWitness A column).V ≤ 1 :=
      ((le_max_left _ _).trans <| (le_max_right _ _).trans
        (le_max_right _ _)).trans transformBound
    simpa [injectLowerWitness] using component
  exact matrixMultiplicationBitOperationCost_le A _
    le_rfl forwardBound

public theorem injectExecutionBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    injectExecutionBitOperationBound dimension smaller ≤
      injectExecutionBitOperationBound dimension larger := by
  unfold injectExecutionBitOperationBound
  exact matrixMultiplicationBitOperationBound_mono dimension hle le_rfl

end NormalForms.Research.KannanBachem
