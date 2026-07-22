/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Examples.Homology.Basic
import all NormalForms.Examples.Homology.Simplicial

/-!
# Native Finite-Free Homology Smoke Test

This executable runs both strong Smith calculations for four fixed finite
free integer chain complexes. It checks the complete runtime summary in every
degree represented by the examples and reports per-case wall time.

Success is an execution regression report. Correctness comes from the
kernel-checked homology theorems, not from this executable.
-/

namespace NormalForms.Benchmarks.Homology

open NormalForms.Applications.Homology
open NormalForms.Examples.Homology
open IntChainComplex

private def expected
    (degree chainRank outgoingRank kernelRank : Nat)
    (invariantFactors torsionFactors : List Nat)
    (bettiNumber : Nat) :
    RuntimeHomologySummary :=
  { degree
    chainRank
    outgoingRank
    kernelRank
    invariantFactors
    torsionFactors
    bettiNumber }

private def cases :
    List (String × IntChainComplex × Nat × RuntimeHomologySummary) :=
  [ ("circle-h0", circle, 0, expected 0 1 0 1 [] [] 1)
  , ("circle-h1", circle, 1, expected 1 1 0 1 [] [] 1)
  , ("circle-h2", circle, 2, expected 2 0 0 0 [] [] 0)
  , ("torus-h0", torus, 0, expected 0 1 0 1 [] [] 1)
  , ("torus-h1", torus, 1, expected 1 2 0 2 [] [] 2)
  , ("torus-h2", torus, 2, expected 2 1 0 1 [] [] 1)
  , ("rp2-h0", realProjectivePlane, 0, expected 0 1 0 1 [] [] 1)
  , ("rp2-h1", realProjectivePlane, 1, expected 1 1 0 1 [2] [2] 0)
  , ("rp2-h2", realProjectivePlane, 2, expected 2 1 1 0 [] [] 0)
  , ("finite-h0", circleWithSixCell, 0, expected 0 1 0 1 [] [] 1)
  , ("finite-h1", circleWithSixCell, 1, expected 1 2 0 2 [6] [6] 1)
  , ("finite-h2", circleWithSixCell, 2, expected 2 1 1 0 [] [] 0)
  , ("simplicial-circle-h0", simplicialCircle.toIntChainComplex, 0,
      expected 0 1 0 1 [] [] 1)
  , ("simplicial-circle-h1", simplicialCircle.toIntChainComplex, 1,
      expected 1 1 0 1 [] [] 1)
  , ("collapsed-sphere-h0", collapsedBoundarySphere.toIntChainComplex, 0,
      expected 0 1 0 1 [] [] 1)
  , ("collapsed-sphere-h1", collapsedBoundarySphere.toIntChainComplex, 1,
      expected 1 0 0 0 [] [] 0)
  , ("collapsed-sphere-h2", collapsedBoundarySphere.toIntChainComplex, 2,
      expected 2 1 0 1 [] [] 1)
  , ("filled-triangle-h0", filledTriangle.toIntChainComplex, 0,
      expected 0 3 0 3 [1, 1] [] 1)
  , ("filled-triangle-h1", filledTriangle.toIntChainComplex, 1,
      expected 1 3 2 1 [1] [] 0)
  , ("filled-triangle-h2", filledTriangle.toIntChainComplex, 2,
      expected 2 1 1 0 [] [] 0)
  ]

private def runCase
    (testCase :
      String × IntChainComplex × Nat × RuntimeHomologySummary) :
    IO Bool := do
  let (name, complex, degree, expectedSummary) := testCase
  let start ← IO.monoNanosNow
  let observed := complex.runtimeHomologySummary degree
  if observed == expectedSummary then
    let stop ← IO.monoNanosNow
    IO.println s!"case={name} valid=true nanoseconds={stop - start} \
      summary={repr observed}"
    return true
  else
    let stop ← IO.monoNanosNow
    IO.println s!"case={name} valid=false nanoseconds={stop - start} \
      summary={repr observed}"
    return false

private def runCases : List
    (String × IntChainComplex × Nat × RuntimeHomologySummary) →
    IO Bool
  | [] => return true
  | testCase :: remaining => do
      let current ← runCase testCase
      let rest ← runCases remaining
      return current && rest

public def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | [] => do
      let start ← IO.monoNanosNow
      let valid ← runCases cases
      let stop ← IO.monoNanosNow
      IO.println s!"cases={cases.length}"
      IO.println s!"total_nanoseconds={stop - start}"
      IO.println s!"valid={valid}"
      if valid then
        return 0
      IO.eprintln "finite-free homology smoke test failed"
      return 2
  | _ => do
      IO.eprintln "usage: normalforms-homology-smoke"
      return 64

end NormalForms.Benchmarks.Homology

public def main (arguments : List String) : IO UInt32 :=
  NormalForms.Benchmarks.Homology.main arguments
