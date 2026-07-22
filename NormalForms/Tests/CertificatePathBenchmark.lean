/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Certificate
import NormalForms.Tests.External.ExpectedMatrices
import all NormalForms.Matrix.Smith.Algorithm

/-!
# Native benchmark stages for the certificate path

This executable is observational instrumentation only. `internal` evaluates
the complete internal Smith certificate on the fixed C1 matrix. `check` parses
and runs the pure checker natively; success is a run report, not a theorem.
-/

open NormalForms.Certificate
open NormalForms.Matrix.Smith
open NormalForms.Tests.External
open scoped Matrix

private def matrixEqb {m n : Nat}
    (left right : Matrix (Fin m) (Fin n) Int) : Bool :=
  (List.finRange m).all fun i =>
    (List.finRange n).all fun j => decide (left i j = right i j)

private def normalizedInvariantFactors {m n : Nat}
    (matrix : Matrix (Fin m) (Fin n) Int) : List Nat :=
  (List.finRange (min m n)).filterMap fun i =>
    let row : Fin m := Fin.castLE (Nat.min_le_left m n) i
    let column : Fin n := Fin.castLE (Nat.min_le_right m n) i
    let value := matrix row column
    if value = 0 then none else some value.natAbs

private def runInternal : IO UInt32 := do
  let result := smithNormalFormFin benchmarkSmall
  let valid :=
    matrixEqb (result.U * benchmarkSmall * result.V) result.S &&
      matrixEqb (result.U_cert.inverse * result.U) 1 &&
      matrixEqb (result.U * result.U_cert.inverse) 1 &&
      matrixEqb (result.V_cert.inverse * result.V) 1 &&
      matrixEqb (result.V * result.V_cert.inverse) 1
  if valid then
    IO.println s!"internal factors: {normalizedInvariantFactors result.S}"
    return 0
  IO.eprintln "internal certificate identities failed"
  return 2

private def runNativeCheck (path : String) : IO UInt32 := do
  let source ← IO.FS.readFile path
  match parseCertificate source with
  | .error error =>
      IO.eprintln s!"certificate parse failed: {repr error}"
      return 2
  | .ok (.hnf _) =>
      IO.eprintln "expected an SNF certificate"
      return 2
  | .ok (.snf raw) =>
      match checkSNF benchmarkSmall raw with
      | .error error =>
          IO.eprintln s!"native certificate check failed: {repr error}"
          return 2
      | .ok checked =>
          IO.println s!"native checker factors: {
            normalizedInvariantFactors checked.S}"
          return 0

public def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | ["internal"] => runInternal
  | ["check", path] => runNativeCheck path
  | _ => do
      IO.eprintln
        "usage: normalforms-certificate-benchmark internal | check CERTIFICATE"
      return 64
