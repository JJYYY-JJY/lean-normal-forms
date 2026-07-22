/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Research.ModularHNF

/-!
# Native modular-HNF research benchmark

The executable measures fixed full-column-rank determinant-modulus cases.  It
reports exact value-kernel telemetry, coefficient widths, modeled schoolbook
bit-cost widths, and native timing inputs.  Runtime agreement is regression
evidence; the imported Lean theorems establish correctness and bounds.
-/

namespace NormalForms.Benchmarks.ModularHNF

open scoped Matrix
open NormalForms.Research.ModularHNF

private def runCase {m n : Nat}
    (caseName : String)
    (input : Matrix (Fin m) (Fin n) Int)
    (expected : Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness input)
    (modulus : DeterminantModulusWitness input fullRank) : IO Bool := do
  let run := runWithDeterminantWitness input fullRank modulus
  let heightBound := modularKernelHeightBound input modulus.modulus
  let bitCost := run.operations.bitOperationCost heightBound
  let bitBound := modularKernelBitOperationBound input modulus.modulus
  let valid :=
    run.candidate == expected &&
      bitCost ≤ bitBound &&
      matrixHeight run.candidate ≤ modulus.modulus.natAbs
  IO.println s!"case={caseName}"
  IO.println s!"rows={m}"
  IO.println s!"columns={n}"
  IO.println s!"input_bits={matrixBitLength input}"
  IO.println s!"modulus_bits={integerBitLength modulus.modulus}"
  IO.println s!"stages={run.stages.length}"
  IO.println s!"additions={run.operations.additions}"
  IO.println s!"multiplications={run.operations.multiplications}"
  IO.println s!"xgcd_calls={run.operations.xgcdCalls}"
  IO.println s!"exact_divisions={run.operations.exactDivisions}"
  IO.println s!"modular_reductions={run.operations.modularReductions}"
  IO.println s!"comparisons={run.operations.comparisons}"
  IO.println s!"operation_total={run.operations.total}"
  IO.println s!"operation_bound={modularOperationBound m n}"
  IO.println s!"intermediate_height_bits={Nat.size heightBound}"
  IO.println s!"result_bits={matrixBitLength run.candidate}"
  IO.println s!"modeled_bit_cost_bits={Nat.size bitCost}"
  IO.println s!"modeled_bit_bound_bits={Nat.size bitBound}"
  IO.println s!"valid={valid}"
  return valid

private def scalarInput : Matrix (Fin 1) (Fin 1) Int := !![6]

private def scalarFullRank : FullColumnRankWitness scalarInput :=
  { rows := Function.Embedding.refl _
    det_ne_zero := by decide }

private def scalarModulus :
    DeterminantModulusWitness scalarInput scalarFullRank :=
  { modulus := 6
    positive := by decide
    selectedMinor_dvd := by decide }

private def tallInput : Matrix (Fin 2) (Fin 1) Int := !![6; 10]

private def tallFullRank : FullColumnRankWitness tallInput :=
  { rows := Fin.castLEEmb (by omega)
    det_ne_zero := by decide }

private def tallModulus :
    DeterminantModulusWitness tallInput tallFullRank :=
  { modulus := 6
    positive := by decide
    selectedMinor_dvd := by decide }

private def squareInput : Matrix (Fin 2) (Fin 2) Int :=
  !![2, 4;
     6, 8]

private def squareFullRank : FullColumnRankWitness squareInput :=
  { rows := Function.Embedding.refl _
    det_ne_zero := by decide }

private def squareModulus :
    DeterminantModulusWitness squareInput squareFullRank :=
  { modulus := 8
    positive := by decide
    selectedMinor_dvd := by decide }

private def runScalar : IO Bool :=
  runCase "scalar-1x1" scalarInput !![6] scalarFullRank scalarModulus

private def runTall : IO Bool :=
  runCase "tall-2x1" tallInput !![2; 0] tallFullRank tallModulus

private def runSquare : IO Bool :=
  runCase "square-2x2" squareInput !![2, 0; 0, 4]
    squareFullRank squareModulus

private def runAll : IO Bool := do
  let scalarValid ← runScalar
  let tallValid ← runTall
  let squareValid ← runSquare
  let valid := scalarValid && tallValid && squareValid
  IO.println "cases=3"
  IO.println s!"all_valid={valid}"
  return valid

private def finish (action : IO Bool) : IO UInt32 := do
  let valid ← action
  if valid then return 0
  IO.eprintln "modular-HNF benchmark check failed"
  return 2

public def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | ["scalar"] => finish runScalar
  | ["tall"] => finish runTall
  | ["square"] => finish runSquare
  | ["all"] => finish runAll
  | _ => do
      IO.eprintln
        "usage: normalforms-modular-hnf-benchmark scalar | tall | square | all"
      return 64

end NormalForms.Benchmarks.ModularHNF

public def main (arguments : List String) : IO UInt32 :=
  NormalForms.Benchmarks.ModularHNF.main arguments
