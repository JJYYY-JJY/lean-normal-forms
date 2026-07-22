/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.StandardXGCD
public import NormalForms.Research.ModularHNF.OperationBound

/-!
# Bit-operation bound for the modular HNF value kernel

The DKT kernel records exact counts for six scalar-operation classes.  This
module prices those counters in the verified sign-magnitude schoolbook model.
The scalar charge is deliberately conservative: its working width admits a
product followed by an addition or modular reduction, while XGCD is charged by
the exact mirror of Lean's standard integer implementation.

The result concerns the modular value kernel.  Construction of the strong
transform and its inverse is supplied by the core canonical HNF bridge and is
not included in this research-kernel cost theorem.
-/

public section

namespace NormalForms.Research.ModularHNF

open NormalForms.Research.BitCost

/-- Width budget for a product and subsequent linear-combination temporary. -/
@[expose] public def modularWorkingBitWidth (height : Nat) : Nat :=
  2 * Nat.size height + 2

/-- Reference cost of comparing two sign-magnitude words of this width. -/
@[expose] public def modularComparisonCostForBitLength (bits : Nat) : Nat :=
  bits + 1

/-- One conservative scalar-operation charge at a stored coefficient height. -/
@[expose] public def modularScalarBitOperationCharge (height : Nat) : Nat :=
  let bits := modularWorkingBitWidth height
  additionCostForBitLengths bits bits +
    multiplicationCostForBitLengths bits bits +
    StandardXGCD.standardIntXGCDUniformBitOperationBound height +
    divisionCostForBitLengths bits bits +
    divisionCostForBitLengths bits bits +
    modularComparisonCostForBitLength bits

namespace ModularOperationCount

/-- Exact telemetry priced by the verified primitive upper charges. -/
@[expose] public def bitOperationCost
    (count : ModularOperationCount) (height : Nat) : Nat :=
  let bits := modularWorkingBitWidth height
  count.additions * additionCostForBitLengths bits bits +
    count.multiplications * multiplicationCostForBitLengths bits bits +
    count.xgcdCalls *
      StandardXGCD.standardIntXGCDUniformBitOperationBound height +
    count.exactDivisions * divisionCostForBitLengths bits bits +
    count.modularReductions * divisionCostForBitLengths bits bits +
    count.comparisons * modularComparisonCostForBitLength bits

/-- Pricing every class by the common scalar charge bounds the weighted sum. -/
public theorem bitOperationCost_le_total_mul_charge
    (count : ModularOperationCount) (height : Nat) :
    count.bitOperationCost height ≤
      count.total * modularScalarBitOperationCharge height := by
  let bits := modularWorkingBitWidth height
  let addition := additionCostForBitLengths bits bits
  let multiplication := multiplicationCostForBitLengths bits bits
  let xgcd := StandardXGCD.standardIntXGCDUniformBitOperationBound height
  let division := divisionCostForBitLengths bits bits
  let comparison := modularComparisonCostForBitLength bits
  let charge := addition + multiplication + xgcd + division + division + comparison
  have additionLe : addition ≤ charge := by
    simp only [charge]
    omega
  have multiplicationLe : multiplication ≤ charge := by
    simp only [charge]
    omega
  have xgcdLe : xgcd ≤ charge := by
    simp only [charge]
    omega
  have divisionLe : division ≤ charge := by
    simp only [charge]
    omega
  have comparisonLe : comparison ≤ charge := by
    simp only [charge]
    omega
  change count.additions * addition + count.multiplications * multiplication +
      count.xgcdCalls * xgcd + count.exactDivisions * division +
      count.modularReductions * division + count.comparisons * comparison ≤
    count.total * charge
  calc
    _ ≤ count.additions * charge + count.multiplications * charge +
        count.xgcdCalls * charge + count.exactDivisions * charge +
        count.modularReductions * charge + count.comparisons * charge := by
      gcongr
    _ = count.total * charge := by
      unfold total
      ring

end ModularOperationCount

namespace Internal

public theorem addition_call_cost_le_charge (left right : SignMagnitude)
    (height : Nat)
    (leftWidth : left.bitLength ≤ modularWorkingBitWidth height)
    (rightWidth : right.bitLength ≤ modularWorkingBitWidth height) :
    (addWithCost left right).cost ≤ modularScalarBitOperationCharge height := by
  have primitive := (addWithCost_cost_le left right).trans
    (NormalForms.Research.BitCost.Internal.addBitOperationBound_le_lengths
      left right _ _ leftWidth rightWidth)
  calc
    _ ≤ additionCostForBitLengths (modularWorkingBitWidth height)
        (modularWorkingBitWidth height) := primitive
    _ ≤ modularScalarBitOperationCharge height := by
      simp [modularScalarBitOperationCharge]
      omega

public theorem multiplication_call_cost_le_charge (left right : SignMagnitude)
    (height : Nat)
    (leftWidth : left.bitLength ≤ modularWorkingBitWidth height)
    (rightWidth : right.bitLength ≤ modularWorkingBitWidth height) :
    (mulWithCost left right).cost ≤ modularScalarBitOperationCharge height := by
  have primitive := (mulWithCost_cost_le left right).trans
    (NormalForms.Research.BitCost.Internal.mulBitOperationBound_le_lengths
      left right _ _ leftWidth rightWidth)
  calc
    _ ≤ multiplicationCostForBitLengths (modularWorkingBitWidth height)
        (modularWorkingBitWidth height) := primitive
    _ ≤ modularScalarBitOperationCharge height := by
      simp [modularScalarBitOperationCharge]
      omega

public theorem division_call_cost_le_charge (left right : SignMagnitude)
    (height : Nat)
    (leftWidth : left.bitLength ≤ modularWorkingBitWidth height)
    (rightWidth : right.bitLength ≤ modularWorkingBitWidth height) :
    (divModWithCost left right).cost ≤ modularScalarBitOperationCharge height := by
  have primitive := (divModWithCost_cost_le left right).trans
    (NormalForms.Research.BitCost.Internal.divModBitOperationBound_le_lengths
      left right _ _ leftWidth rightWidth)
  calc
    _ ≤ divisionCostForBitLengths (modularWorkingBitWidth height)
        (modularWorkingBitWidth height) := primitive
    _ ≤ modularScalarBitOperationCharge height := by
      simp [modularScalarBitOperationCharge]
      omega

public theorem standard_xgcd_call_cost_le_charge (left right : Int)
    (height : Nat) (leftLe : left.natAbs ≤ height)
    (rightLe : right.natAbs ≤ height) :
    (StandardXGCD.standardIntXGCDWithCost left right).cost ≤
      modularScalarBitOperationCharge height := by
  have primitive := StandardXGCD.standardIntXGCDWithCost_cost_le_uniform
    left right height leftLe rightLe
  calc
    _ ≤ StandardXGCD.standardIntXGCDUniformBitOperationBound height := primitive
    _ ≤ modularScalarBitOperationCharge height := by
      simp [modularScalarBitOperationCharge]
      omega

end Internal

/-- Height envelope used to price every stored state of a full raw run. -/
@[expose] public def modularKernelHeightBound {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (modulus : Int) : Nat :=
  modularIntermediateHeightBound m n n (matrixHeight A) modulus.natAbs

/-- Closed bit-operation budget for the full modular value kernel. -/
@[expose] public def modularKernelBitOperationBound {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (modulus : Int) : Nat :=
  modularOperationBound m n *
    modularScalarBitOperationCharge (modularKernelHeightBound A modulus)

/-- The priced exact telemetry of every raw run satisfies the closed budget. -/
public theorem runRaw_bitOperationCost_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int) :
    (runRaw A columns_le_rows modulus).operations.bitOperationCost
        (modularKernelHeightBound A modulus) ≤
      modularKernelBitOperationBound A modulus := by
  exact (ModularOperationCount.bitOperationCost_le_total_mul_charge _ _).trans
    (Nat.mul_le_mul_right _
      (runRaw_operations_total_le A columns_le_rows modulus))

/-- The legal determinant-modulus entry inherits the same bit-operation bound. -/
public theorem runWithDeterminantWitness_bitOperationCost_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (modulus : DeterminantModulusWitness A fullRank) :
    (runWithDeterminantWitness A fullRank modulus).operations.bitOperationCost
        (modularKernelHeightBound A modulus.modulus) ≤
      modularKernelBitOperationBound A modulus.modulus := by
  exact runRaw_bitOperationCost_le A fullRank.columns_le_rows modulus.modulus

end NormalForms.Research.ModularHNF
