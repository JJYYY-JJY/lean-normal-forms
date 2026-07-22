/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Research.LLL
meta import all NormalForms.Research.LLL

/-!
# Native LLL research benchmark

The fixed corpus separates the profiled independent-row kernel from the total
rank-decomposition wrapper and the transpose-only column adapter. Native time
is regression evidence; the imported Lean theorems establish the strong result
and profile bounds.
-/

namespace NormalForms.Benchmarks.LLL

open scoped Matrix
open NormalForms.Research.LLL

private def matrixEqb {m n : Nat}
    (left right : Matrix (Fin m) (Fin n) Int) : Bool :=
  (List.finRange m).all fun row =>
    (List.finRange n).all fun column => left row column == right row column

private def zeroTailEqb {m n : Nat} (rank : Nat)
    (basis : Matrix (Fin m) (Fin n) Int) : Bool :=
  (List.finRange m).all fun row =>
    if rank <= row.val then
      (List.finRange n).all fun column => basis row column == 0
    else
      true

private def runProfileCase {m n : Nat} (caseName : String)
    (input : Matrix (Fin m) (Fin n) Int) (rowsPositive : 1 <= m)
    (fullRank : FullRowRankWitness input) : IO Bool := do
  let profile := fullRankLLLProfilePositive input rowsPositive fullRank
  let result := profile.result
  let operationBound := lllTrackedEventBound m profile.fuel
  let bitBound := lllKernelBitOperationBound m n profile.fuel
    profile.intermediateCoefficientHeight
  let strong :=
    matrixEqb (result.U * input) result.reducedBasis &&
      matrixEqb (result.U_cert.inverse * result.U) 1 &&
      matrixEqb (result.U * result.U_cert.inverse) 1 &&
      isLLLReducedB result.reducedBasis
  let valid :=
    strong && profile.operations.total <= operationBound &&
      basisBitLength result.reducedBasis <=
        profile.intermediateCoefficientBitLength &&
      profile.bitOperationCost <= bitBound
  IO.println s!"case={caseName}"
  IO.println "kind=profiled-full-rank"
  IO.println s!"rows={m}"
  IO.println s!"columns={n}"
  IO.println s!"rank={m}"
  IO.println s!"input_bits={basisBitLength input}"
  IO.println s!"result_bits={basisBitLength result.reducedBasis}"
  IO.println s!"fuel={profile.fuel}"
  IO.println s!"size_reductions={profile.operations.sizeReductions}"
  IO.println s!"swaps={profile.operations.swaps}"
  IO.println s!"refreshes={profile.operations.gramSchmidtRefreshes}"
  IO.println s!"operation_total={profile.operations.total}"
  IO.println s!"operation_bound={operationBound}"
  IO.println s!"intermediate_coefficient_bits={profile.intermediateCoefficientBitLength}"
  IO.println s!"modeled_bit_cost={profile.bitOperationCost}"
  IO.println s!"modeled_bit_bound={bitBound}"
  IO.println s!"strong_result={strong}"
  IO.println s!"valid={valid}"
  return valid

private def runTotalRowCase {m n : Nat} (caseName : String) (rank : Nat)
    (input : Matrix (Fin m) (Fin n) Int) : IO Bool := do
  let result := integerLLL input
  let strong :=
    result.rank == rank &&
      matrixEqb (result.U * input) result.reducedBasis &&
      matrixEqb (result.U_cert.inverse * result.U) 1 &&
      matrixEqb (result.U * result.U_cert.inverse) 1 &&
      isLLLReducedB (rowPrefix result.rank_le_rows result.reducedBasis) &&
      zeroTailEqb result.rank result.reducedBasis
  IO.println s!"case={caseName}"
  IO.println "kind=total-row"
  IO.println s!"rows={m}"
  IO.println s!"columns={n}"
  IO.println s!"rank={result.rank}"
  IO.println s!"input_bits={basisBitLength input}"
  IO.println s!"result_bits={basisBitLength result.reducedBasis}"
  IO.println s!"strong_result={strong}"
  IO.println s!"valid={strong}"
  return strong

private def runColumnCase {m n : Nat} (caseName : String) (rank : Nat)
    (input : Matrix (Fin m) (Fin n) Int) : IO Bool := do
  let result := integerColumnLLL input
  let strong :=
    result.rank == rank &&
      matrixEqb (input * result.V) result.reducedBasis &&
      matrixEqb (result.V_cert.inverse * result.V) 1 &&
      matrixEqb (result.V * result.V_cert.inverse) 1 &&
      isLLLReducedB
        (rowPrefix result.rank_le_columns result.reducedBasis.transpose) &&
      zeroTailEqb result.rank result.reducedBasis.transpose
  IO.println s!"case={caseName}"
  IO.println "kind=transpose-column"
  IO.println s!"rows={m}"
  IO.println s!"columns={n}"
  IO.println s!"rank={result.rank}"
  IO.println s!"input_bits={basisBitLength input}"
  IO.println s!"result_bits={basisBitLength result.reducedBasis}"
  IO.println s!"strong_result={strong}"
  IO.println s!"valid={strong}"
  return strong

private def gaussInput : Matrix (Fin 2) (Fin 2) Int :=
  !![1, 1; 1, 0]

set_option linter.style.nativeDecide false in
private theorem gaussFullRank : FullRowRankWitness gaussInput :=
  { independent := by native_decide }

private def denseInput : Matrix (Fin 3) (Fin 3) Int :=
  !![4, 1, 3; 2, 1, 1; 1, 0, 2]

set_option linter.style.nativeDecide false in
private theorem denseFullRank : FullRowRankWitness denseInput :=
  { independent := by native_decide }

private def dependentInput : Matrix (Fin 3) (Fin 3) Int :=
  !![1, 1, 0; 2, 2, 0; 0, 0, 0]

private def runGauss : IO Bool :=
  runProfileCase "gauss-2x2" gaussInput (by decide) gaussFullRank

private def runDense : IO Bool :=
  runProfileCase "dense-3x3" denseInput (by decide) denseFullRank

private def runDependent : IO Bool :=
  runTotalRowCase "dependent-3x3" 1 dependentInput

private def runColumn : IO Bool :=
  runColumnCase "column-3x3" 1 dependentInput.transpose

private def runAll : IO Bool := do
  let gauss <- runGauss
  let dense <- runDense
  let dependent <- runDependent
  let column <- runColumn
  let valid := gauss && dense && dependent && column
  IO.println "cases=4"
  IO.println s!"all_valid={valid}"
  return valid

private def finish (action : IO Bool) : IO UInt32 := do
  let valid <- action
  if valid then return 0
  IO.eprintln "LLL benchmark check failed"
  return 2

public def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | ["gauss"] => finish runGauss
  | ["dense"] => finish runDense
  | ["dependent"] => finish runDependent
  | ["column"] => finish runColumn
  | ["all"] => finish runAll
  | _ => do
      IO.eprintln
        "usage: normalforms-lll-smoke gauss | dense | dependent | column | all"
      return 64

end NormalForms.Benchmarks.LLL

public def main (arguments : List String) : IO UInt32 :=
  NormalForms.Benchmarks.LLL.main arguments
