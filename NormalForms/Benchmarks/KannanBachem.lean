/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Research.KannanBachem

/-!
# Native Kannan--Bachem Research Benchmark

This executable measures three fixed nonsingular square integer cases.  It
reports the formal ring-operation telemetry, coefficient widths, and modeled
schoolbook bit cost next to native timing metadata.  Runtime success remains
regression evidence; correctness and complexity come from the imported Lean
theorems.
-/

namespace NormalForms.Benchmarks.KannanBachem

open scoped Matrix
open NormalForms.Matrix.Hermite
open NormalForms.Research.KannanBachem
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

private def hnfInput : Matrix (Fin 3) (Fin 3) Int :=
  !![2, 3, 5;
     4, 7, 11;
     6, 13, 17]

private def hnfExpected : Matrix (Fin 3) (Fin 3) Int :=
  !![2, 0, 0;
     0, 1, 1;
     0, 0, 2]

private theorem hnfInput_det_ne_zero : hnfInput.det ≠ 0 := by decide

private def smithRepeatInput : Matrix (Fin 2) (Fin 2) Int :=
  !![2, 1;
     0, 2]

private def smithRepeatExpected : Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 4]

private theorem smithRepeatInput_det_ne_zero :
    smithRepeatInput.det ≠ 0 := by decide

private def smithInjectionInput : Matrix (Fin 2) (Fin 2) Int :=
  !![2, 0;
     0, 3]

private def smithInjectionExpected : Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 6]

private theorem smithInjectionInput_det_ne_zero :
    smithInjectionInput.det ≠ 0 := by decide

private def printCommon
    (caseName : String) (dimension inputBits determinantBits
      inputEncodingBits : Nat) : IO Unit := do
  IO.println s!"case={caseName}"
  IO.println s!"dimension={dimension}"
  IO.println s!"input_bits={inputBits}"
  IO.println s!"determinant_bits={determinantBits}"
  IO.println s!"input_encoding_bits={inputEncodingBits}"

private def runHNF : IO Bool := do
  let run := preparedPrincipalExecution hnfInput hnfInput_det_ne_zero
  let result := run.value
  let operations := traceOperationCount run.charges
  let cost := traceBitCost run.charges
  let bound := preparedPrincipalExecutionBitOperationBound 3
    (matrixBitLength hnfInput)
  let valid :=
    result.H == hnfExpected &&
      result.U * hnfInput == result.H &&
      result.U_cert.inverse * result.H == hnfInput &&
      cost ≤ bound
  printCommon "hnf-prepared-3x3" 3 (matrixBitLength hnfInput)
    (Hermite.integerBitLength hnfInput.det)
    (matrixEncodingLength ⟨3, hnfInput⟩)
  IO.println s!"additions={operations.additions}"
  IO.println s!"multiplications={operations.multiplications}"
  IO.println s!"xgcd_calls={operations.xgcdCalls}"
  IO.println s!"normalizations={operations.normalizations}"
  IO.println s!"standalone_divmod_calls={operations.standaloneDivModCalls}"
  IO.println s!"arithmetic_operation_total={operations.total}"
  IO.println s!"result_bits={matrixBitLength result.H}"
  IO.println s!"left_bits={matrixBitLength result.U}"
  IO.println s!"left_inverse_bits={matrixBitLength result.U_cert.inverse}"
  IO.println "right_bits=0"
  IO.println "right_inverse_bits=0"
  IO.println s!"passes=0"
  IO.println s!"injections=0"
  IO.println s!"bit_cost={cost}"
  IO.println s!"bit_bound={bound}"
  IO.println s!"diagonal=2,1,2"
  IO.println s!"valid={valid}"
  return valid

private def runSmith
    (caseName : String)
    (diagonal : String)
    (input expected : Matrix (Fin 2) (Fin 2) Int)
    (hdet : input.det ≠ 0) : IO Bool := do
  let run := smithExecution input hdet
  let result := run.value
  let operations := traceOperationCount run.charges
  let profile := smithCoefficientProfile result
  let cost := traceBitCost run.charges
  let bound := smithExecutionPolynomialBitOperationBound 2
    (matrixBitLength input)
  let outputEncodingBits := smithOutputEncodingLength result
  let valid :=
    result.S == expected &&
      result.U * input * result.V == result.S &&
      result.U_cert.inverse * result.S * result.V_cert.inverse == input &&
      cost ≤ bound
  printCommon caseName 2 (matrixBitLength input)
    (Hermite.integerBitLength input.det)
    (matrixEncodingLength ⟨2, input⟩)
  IO.println s!"additions={operations.additions}"
  IO.println s!"multiplications={operations.multiplications}"
  IO.println s!"xgcd_calls={operations.xgcdCalls}"
  IO.println s!"normalizations={operations.normalizations}"
  IO.println s!"standalone_divmod_calls={operations.standaloneDivModCalls}"
  IO.println s!"arithmetic_operation_total={operations.total}"
  IO.println s!"result_bits={profile.resultBitLength}"
  IO.println s!"left_bits={profile.leftBitLength}"
  IO.println s!"left_inverse_bits={profile.leftInverseBitLength}"
  IO.println s!"right_bits={profile.rightBitLength}"
  IO.println s!"right_inverse_bits={profile.rightInverseBitLength}"
  IO.println s!"passes={run.controlTrace.passes}"
  IO.println s!"injections={run.controlTrace.injections}"
  IO.println s!"bit_cost={cost}"
  IO.println s!"bit_bound={bound}"
  IO.println s!"output_encoding_bits={outputEncodingBits}"
  IO.println s!"diagonal={diagonal}"
  IO.println s!"valid={valid}"
  return valid

private def runRepeat : IO Bool :=
  runSmith "smith-repeat-2x2" "1,4" smithRepeatInput smithRepeatExpected
    smithRepeatInput_det_ne_zero

private def runInjection : IO Bool :=
  runSmith "smith-injection-2x2" "1,6" smithInjectionInput
    smithInjectionExpected
    smithInjectionInput_det_ne_zero

private def runAll : IO Bool := do
  let hnfValid ← runHNF
  let repeatValid ← runRepeat
  let injectionValid ← runInjection
  IO.println "cases=3"
  IO.println s!"all_valid={hnfValid && repeatValid && injectionValid}"
  return hnfValid && repeatValid && injectionValid

private def finish (action : IO Bool) : IO UInt32 := do
  let valid ← action
  if valid then return 0
  IO.eprintln "Kannan--Bachem benchmark check failed"
  return 2

public def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | ["hnf"] => finish runHNF
  | ["smith-repeat"] => finish runRepeat
  | ["smith-injection"] => finish runInjection
  | ["all"] => finish runAll
  | _ => do
      IO.eprintln
        "usage: normalforms-kannan-bachem-benchmark \
          hnf | smith-repeat | smith-injection | all"
      return 64

end NormalForms.Benchmarks.KannanBachem

public def main (arguments : List String) : IO UInt32 :=
  NormalForms.Benchmarks.KannanBachem.main arguments
