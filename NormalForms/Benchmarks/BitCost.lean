/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Research.BitCost
meta import all NormalForms.Research.BitCost.Representation
meta import all NormalForms.Research.BitCost.Addition
meta import all NormalForms.Research.BitCost.Multiplication
meta import all NormalForms.Research.BitCost.Division
meta import all NormalForms.Research.BitCost.XGCD

/-!
# Native Bit-Cost Reference Benchmark

This executable reports modeled bit operations and proved budgets for fixed
binary inputs. Native wall time is experimental metadata only; the formal
cost claims are the `cost_le` theorems in the research facade.
-/

namespace NormalForms.Benchmarks.BitCost

open NormalForms.Research.BitCost

private def z (value : Int) : SignMagnitude :=
  SignMagnitude.ofInt value

private def runAdd (left right : Int) : IO Bool := do
  let result := addWithCost (z left) (z right)
  let bound := addBitOperationBound (z left) (z right)
  let valid := result.value.value == left + right && result.cost ≤ bound
  IO.println s!"operation=add left={left} right={right} \
    value={result.value.value} cost={result.cost} bound={bound} valid={valid}"
  return valid

private def runMul (left right : Int) : IO Bool := do
  let result := mulWithCost (z left) (z right)
  let bound := mulBitOperationBound (z left) (z right)
  let valid := result.value.value == left * right && result.cost ≤ bound
  IO.println s!"operation=mul left={left} right={right} \
    value={result.value.value} cost={result.cost} bound={bound} valid={valid}"
  return valid

private def runDivMod (numerator divisor : Int) : IO Bool := do
  let result := divModWithCost (z numerator) (z divisor)
  let bound := divModBitOperationBound (z numerator) (z divisor)
  let valid :=
    result.value.quotient.value == numerator / divisor &&
      result.value.remainder.value == numerator % divisor &&
      result.cost ≤ bound
  IO.println s!"operation=divmod left={numerator} right={divisor} \
    quotient={result.value.quotient.value} \
    remainder={result.value.remainder.value} cost={result.cost} \
    bound={bound} valid={valid}"
  return valid

private def runXGCD (left right : Int) : IO Bool := do
  let result := xgcdWithCost (z left) (z right)
  let bound := xgcdBitOperationBound (z left) (z right)
  let coefficientBound := xgcdCoefficientBitBound (z left) (z right)
  let valid :=
    result.value.gcd.value == (left.gcd right : Nat) &&
      result.value.leftCoeff.value * left +
          result.value.rightCoeff.value * right == result.value.gcd.value &&
      result.value.leftCoeff.bitLength ≤ coefficientBound &&
      result.value.rightCoeff.bitLength ≤ coefficientBound &&
      result.cost ≤ bound
  IO.println s!"operation=xgcd left={left} right={right} \
    gcd={result.value.gcd.value} left_coeff={result.value.leftCoeff.value} \
    right_coeff={result.value.rightCoeff.value} cost={result.cost} \
    coefficient_bound={coefficientBound} bound={bound} valid={valid}"
  return valid

private def runCases : IO Bool := do
  let a0 ← runAdd (-37) 19
  let a1 ← runAdd 65535 1
  let a2 ← runAdd (-1048576) 1048575
  let m0 ← runMul (-13) 11
  let m1 ← runMul 255 257
  let m2 ← runMul 0 1048576
  let d0 ← runDivMod (-37) 5
  let d1 ← runDivMod 37 (-5)
  let d2 ← runDivMod 17 0
  let x0 ← runXGCD 240 46
  let x1 ← runXGCD (-240) 46
  let x2 ← runXGCD 17 (-5)
  let x3 ← runXGCD 0 0
  return a0 && a1 && a2 && m0 && m1 && m2 &&
    d0 && d1 && d2 && x0 && x1 && x2 && x3

public def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | [] => do
      let start ← IO.monoNanosNow
      let valid ← runCases
      let stop ← IO.monoNanosNow
      IO.println "cases=13"
      IO.println s!"total_nanoseconds={stop - start}"
      IO.println s!"valid={valid}"
      if valid then return 0 else return 2
  | _ => do
      IO.eprintln "usage: normalforms-bit-cost-benchmark"
      return 64

end NormalForms.Benchmarks.BitCost

public def main (arguments : List String) : IO UInt32 :=
  NormalForms.Benchmarks.BitCost.main arguments
