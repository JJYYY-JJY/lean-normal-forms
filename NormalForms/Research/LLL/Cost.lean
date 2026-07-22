/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.Result
public import NormalForms.Research.LLL.HexBackend
public import NormalForms.Research.BitCost

/-!
# Cost vocabulary for the exact integer LLL trace

The verified backend has two deliberately separate cost views.  The transition
counter records successful size reductions, adjacent swaps, and the associated
integer Gram--Schmidt state refreshes.  The bit model then prices those tracked
events at an observed intermediate coefficient height using the project's
explicit sign-magnitude schoolbook primitives.

This is an a-posteriori bound for the traced full-row-rank kernel.  It is not an
input-only polynomial bound, and it does not price the HNF rank decomposition
used by the total rank-deficient wrapper.
-/

@[expose] public section

namespace NormalForms.Research.LLL

open NormalForms.Research.BitCost

/-- Largest absolute entry of a finite integer row basis. -/
public def basisHeight {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) : Nat :=
  Finset.univ.sup fun row =>
    Finset.univ.sup fun column => (basis row column).natAbs

/-- Binary length of the largest absolute basis entry. -/
public def basisBitLength {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) : Nat :=
  Nat.size (basisHeight basis)

public theorem entry_natAbs_le_basisHeight {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (row : Fin m) (column : Fin n) :
    (basis row column).natAbs <= basisHeight basis := by
  exact (Finset.le_sup
    (f := fun column => (basis row column).natAbs)
    (Finset.mem_univ column)).trans
      (Finset.le_sup
        (f := fun row => Finset.univ.sup fun column =>
          (basis row column).natAbs)
        (Finset.mem_univ row))

/-- The termination fuel used by the pinned verified dense backend. -/
public def fullRankLLLFuel {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) : Nat :=
  Hex.Internal.lllFuel (Hex.Internal.LLLState.ofBasis (toDense basis))

/--
Every outer transition visits at most `rows` reduction positions and performs
at most one adjacent swap.  Each successful row operation also records one
integer Gram--Schmidt refresh, hence the factor two.
-/
public def lllTrackedEventBound (rows fuel : Nat) : Nat :=
  fuel * (2 * rows + 2)

/-- Working width for one product followed by an addition or division. -/
public def lllWorkingBitWidth (height : Nat) : Nat :=
  2 * Nat.size height + 3

/--
One conservative schoolbook charge for a tracked scalar arithmetic position.
The two division charges cover quotient/remainder-style updates in the dense
integer state; comparisons are charged linearly in the common width.
-/
public def lllScalarBitOperationCharge (height : Nat) : Nat :=
  let bits := lllWorkingBitWidth height
  additionCostForBitLengths bits bits +
    multiplicationCostForBitLengths bits bits +
    divisionCostForBitLengths bits bits +
    divisionCostForBitLengths bits bits +
    bits + 1

/-- Number of scalar positions conservatively charged for one tracked event. -/
public def lllScalarPositionsPerEvent (rows columns : Nat) : Nat :=
  4 * rows + 2 * columns + 12

namespace PrimitiveCost

/-- One explicit sign-magnitude addition fits the common scalar charge. -/
public theorem addition_call_cost_le_charge
    (left right : SignMagnitude) (height : Nat)
    (leftWidth : left.bitLength <= lllWorkingBitWidth height)
    (rightWidth : right.bitLength <= lllWorkingBitWidth height) :
    (addWithCost left right).cost <= lllScalarBitOperationCharge height := by
  have primitive := (addWithCost_cost_le left right).trans
    (NormalForms.Research.BitCost.Internal.addBitOperationBound_le_lengths
      left right _ _ leftWidth rightWidth)
  calc
    _ <= additionCostForBitLengths (lllWorkingBitWidth height)
        (lllWorkingBitWidth height) := primitive
    _ <= lllScalarBitOperationCharge height := by
      simp [lllScalarBitOperationCharge]
      omega

/-- One explicit sign-magnitude multiplication fits the common scalar charge. -/
public theorem multiplication_call_cost_le_charge
    (left right : SignMagnitude) (height : Nat)
    (leftWidth : left.bitLength <= lllWorkingBitWidth height)
    (rightWidth : right.bitLength <= lllWorkingBitWidth height) :
    (mulWithCost left right).cost <= lllScalarBitOperationCharge height := by
  have primitive := (mulWithCost_cost_le left right).trans
    (NormalForms.Research.BitCost.Internal.mulBitOperationBound_le_lengths
      left right _ _ leftWidth rightWidth)
  calc
    _ <= multiplicationCostForBitLengths (lllWorkingBitWidth height)
        (lllWorkingBitWidth height) := primitive
    _ <= lllScalarBitOperationCharge height := by
      simp [lllScalarBitOperationCharge]
      omega

/-- One explicit sign-magnitude division fits the common scalar charge. -/
public theorem division_call_cost_le_charge
    (left right : SignMagnitude) (height : Nat)
    (leftWidth : left.bitLength <= lllWorkingBitWidth height)
    (rightWidth : right.bitLength <= lllWorkingBitWidth height) :
    (divModWithCost left right).cost <= lllScalarBitOperationCharge height := by
  have primitive := (divModWithCost_cost_le left right).trans
    (NormalForms.Research.BitCost.Internal.divModBitOperationBound_le_lengths
      left right _ _ leftWidth rightWidth)
  calc
    _ <= divisionCostForBitLengths (lllWorkingBitWidth height)
        (lllWorkingBitWidth height) := primitive
    _ <= lllScalarBitOperationCharge height := by
      simp [lllScalarBitOperationCharge]
      omega

end PrimitiveCost

namespace LLLOperationCount

/-- Abstract row operations represented by the telemetry. -/
public def rowOperations (count : LLLOperationCount) : Nat :=
  count.sizeReductions + count.swaps

/--
A specified schoolbook reference price for the tracked dense-kernel events at
a common observed coefficient height.
-/
public def bitOperationCost (count : LLLOperationCount)
    (rows columns height : Nat) : Nat :=
  count.total * lllScalarPositionsPerEvent rows columns *
    lllScalarBitOperationCharge height

end LLLOperationCount

/-- Closed profile-dependent bit-operation budget for the traced kernel. -/
public def lllKernelBitOperationBound
    (rows columns fuel height : Nat) : Nat :=
  lllTrackedEventBound rows fuel *
    lllScalarPositionsPerEvent rows columns *
    lllScalarBitOperationCharge height

/-- Four-tier evidence returned by the profiled full-row-rank entry. -/
public structure FullRankLLLProfile {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) where
  result : FullRankLLLResult basis
  fuel : Nat
  fuel_eq : fuel = fullRankLLLFuel basis
  operations : LLLOperationCount
  operation_bound : operations.total <= lllTrackedEventBound m fuel
  intermediateCoefficientHeight : Nat
  result_height_le :
    basisHeight result.reducedBasis <= intermediateCoefficientHeight

namespace FullRankLLLProfile

/-- Observed maximum bit length along the profiled basis trace. -/
public def intermediateCoefficientBitLength {m n : Nat}
    {basis : Matrix (Fin m) (Fin n) Int}
    (profile : FullRankLLLProfile basis) : Nat :=
  Nat.size profile.intermediateCoefficientHeight

/-- The returned basis is covered by the recorded intermediate bit width. -/
public theorem result_bitLength_le {m n : Nat}
    {basis : Matrix (Fin m) (Fin n) Int}
    (profile : FullRankLLLProfile basis) :
    basisBitLength profile.result.reducedBasis <=
      profile.intermediateCoefficientBitLength := by
  exact Nat.size_le_size profile.result_height_le

/-- Actual tracked-event reference cost of this profiled execution. -/
public def bitOperationCost {m n : Nat}
    {basis : Matrix (Fin m) (Fin n) Int}
    (profile : FullRankLLLProfile basis) : Nat :=
  profile.operations.bitOperationCost m n profile.intermediateCoefficientHeight

/-- The profiled reference cost satisfies its closed fuel-and-height budget. -/
public theorem bitOperationCost_le {m n : Nat}
    {basis : Matrix (Fin m) (Fin n) Int}
    (profile : FullRankLLLProfile basis) :
    profile.bitOperationCost <=
      lllKernelBitOperationBound m n profile.fuel
        profile.intermediateCoefficientHeight := by
  unfold bitOperationCost LLLOperationCount.bitOperationCost
    lllKernelBitOperationBound
  exact Nat.mul_le_mul_right _ <|
    Nat.mul_le_mul_right _ profile.operation_bound

end FullRankLLLProfile

end NormalForms.Research.LLL
