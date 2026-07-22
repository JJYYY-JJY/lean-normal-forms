/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Applications.RationalCanonical

/-!
# Native Rational Canonical Benchmark

This executable measures the independent rational-canonical application.  It
uses a fixed rational size-two Jordan block at `1 / 2`.  The executable
reports deterministic degree and coefficient-growth metrics and exposes
separate invariant-generation, companion-verification, and end-to-end stages.

All successes are runtime regression reports.  The theorems imported from the
application facade, rather than this executable, establish correctness.
-/

namespace NormalForms.Benchmarks.RationalCanonical

open NormalForms.RationalCanonical
open Polynomial
open scoped Matrix

private def benchmarkInput : Matrix (Fin 2) (Fin 2) Rat :=
  !![(1 : Rat) / 2, 1;
     0, (1 : Rat) / 2]

private def bitLength (value : Nat) : Nat :=
  if value = 0 then 0 else value.log2 + 1

private def rationalBitLength (value : Rat) : Nat :=
  max (bitLength value.num.natAbs) (bitLength value.den)

private def matrixCoefficientBitLength : Nat :=
  (List.finRange 2).foldl
    (fun current i =>
      (List.finRange 2).foldl
        (fun rowCurrent j =>
          max rowCurrent (rationalBitLength (benchmarkInput i j)))
        current)
    0

private def polynomialCoefficientBitLength (factor : Rat[X]) : Nat :=
  (List.range (factor.natDegree + 1)).foldl
    (fun current degree =>
      max current (rationalBitLength (factor.coeff degree)))
    0

private def factorCoefficientBitLength (factors : List Rat[X]) : Nat :=
  factors.foldl
    (fun current factor =>
      max current (polynomialCoefficientBitLength factor))
    0

private def factorDegrees (factors : List Rat[X]) : List Nat :=
  factors.map Polynomial.natDegree

private def unitFactorCheck (factor : Rat[X]) : Bool :=
  factor.natDegree == 0 &&
    factor.coeff 0 == 1

private def invariantCheck (factors : List Rat[X]) : Bool :=
  match factors with
  | [first, quadratic] =>
      unitFactorCheck first &&
        quadratic.natDegree == 2 &&
        quadratic.coeff 0 == (1 : Rat) / 4 &&
        quadratic.coeff 1 == -1 &&
        quadratic.coeff 2 == 1
  | _ => false

private def companionShapeCheck (factor : Rat[X]) : Bool :=
  let degree := factor.natDegree
  let block := companionMatrix factor
  (List.finRange degree).all fun i =>
    (List.finRange degree).all fun j =>
      if j.1 + 1 < degree then
        if i.1 = j.1 + 1 then
          block i j == 1
        else
          block i j == 0
      else
        block i j == -factor.coeff i.1

private def companionCheck (factors : List Rat[X]) : Bool :=
  factors.all companionShapeCheck

private def repeatCompanionCheck
    (factors : List Rat[X]) : Nat → Bool
  | 0 => true
  | repetitions + 1 =>
      companionCheck factors &&
        repeatCompanionCheck factors repetitions

private def companionRepetitions : Nat := 1000

private def renderDegrees (degrees : List Nat) : String :=
  String.intercalate "," (degrees.map toString)

private def printMetrics
    (factors : List Rat[X])
    (valid : Bool) : IO Unit := do
  IO.println s!"valid={valid}"
  IO.println s!"factor_degrees={renderDegrees (factorDegrees factors)}"
  IO.println s!"maximum_input_coefficient_bits={matrixCoefficientBitLength}"
  IO.println s!"maximum_factor_coefficient_bits={
    factorCoefficientBitLength factors}"
  IO.println s!"companion_repetitions={companionRepetitions}"

private def finish
    (factors : List Rat[X])
    (valid : Bool) : IO UInt32 := do
  printMetrics factors valid
  if valid then
    return 0
  IO.eprintln "rational canonical benchmark check failed"
  return 2

private def runInvariants : IO UInt32 :=
  let factors := endomorphismInvariantFactors benchmarkInput
  finish factors (invariantCheck factors)

private def runCompanion : IO UInt32 := do
  let factors := endomorphismInvariantFactors benchmarkInput
  if invariantCheck factors then
    let start ← IO.monoNanosNow
    if repeatCompanionCheck factors companionRepetitions then
      let stop ← IO.monoNanosNow
      IO.println s!"companion_nanoseconds={stop - start}"
      finish factors true
    else
      finish factors false
  else
    finish factors false

private def runTotal : IO UInt32 :=
  let factors := endomorphismInvariantFactors benchmarkInput
  finish factors
    (invariantCheck factors && companionCheck factors)

public def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | ["invariants"] => runInvariants
  | ["companion"] => runCompanion
  | ["total"] => runTotal
  | _ => do
      IO.eprintln
        "usage: normalforms-rational-canonical-benchmark \
          invariants | companion | total"
      return 64

end NormalForms.Benchmarks.RationalCanonical

public def main (arguments : List String) : IO UInt32 :=
  NormalForms.Benchmarks.RationalCanonical.main arguments
