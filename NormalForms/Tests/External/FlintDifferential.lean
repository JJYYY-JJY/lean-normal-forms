/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.External.Flint.FFI
import all NormalForms.Matrix.Smith.Algorithm

/-!
# Fixed-seed internal/FLINT differential regression

This optional native executable compares normalized invariant factors only.
Transformation matrices are intentionally ignored because they are not unique.
The FFI result first passes through the public pure certificate checker.
Differential agreement is a regression signal, not a trust argument.
-/

open NormalForms.Certificate
open NormalForms.External.Flint
open NormalForms.Matrix.Smith

private structure Case where
  name : String
  rows : Nat
  cols : Nat
  matrix : Matrix (Fin rows) (Fin cols) Int

private def lcgStep (state : Nat) : Nat :=
  (1_664_525 * state + 1_013_904_223) % 4_294_967_296

private def lcgAt (seed : Nat) : Nat → Nat
  | 0 => lcgStep seed
  | index + 1 => lcgStep (lcgAt seed index)

private def denseValue (seed cols row column : Nat) : Int :=
  ((lcgAt seed (row * cols + column) % 9 : Nat) : Int) - 4

private def denseCase (name : String) (seed rows cols : Nat) : Case :=
  { name, rows, cols
    matrix := fun i j => denseValue seed cols i.val j.val }

private def sparseCase (name : String) (seed rows cols : Nat) : Case :=
  { name, rows, cols
    matrix := fun i j =>
      let sample := lcgAt seed (i.val * cols + j.val)
      if sample % 3 = 0 then ((sample % 9 : Nat) : Int) - 4 else 0 }

private def rankDeficientCase : Case :=
  let base (row column : Nat) : Int :=
    denseValue 0x5eed1234 3 row column
  { name := "rank-deficient"
    rows := 3
    cols := 3
    matrix := fun i j =>
      match i.val with
      | 0 => base 0 j.val
      | 1 => base 1 j.val
      | _ => 2 * base 0 j.val }

private def cases : List Case :=
  [denseCase "dense-wide" 0x00c0ffee 2 3,
    denseCase "dense-tall" 0x12345678 3 2,
    sparseCase "sparse-rectangular" 0x0badf00d 3 4,
    rankDeficientCase]

private def normalizedInvariantFactors {m n : Nat}
    (matrix : Matrix (Fin m) (Fin n) Int) : List Nat :=
  (List.finRange (min m n)).filterMap fun i =>
    let row : Fin m := Fin.castLE (Nat.min_le_left m n) i
    let column : Fin n := Fin.castLE (Nat.min_le_right m n) i
    let value := matrix row column
    if value = 0 then none else some value.natAbs

private def runCase (test : Case) : IO (Except String Unit) := do
  let internal := smithNormalFormFin test.matrix
  let internalFactors := normalizedInvariantFactors internal.S
  match ← generateAndCheckSNF test.matrix with
  | .error error =>
      return Except.error s!"{test.name}: FFI/checker failure: {repr error}"
  | .ok checked =>
      let ffiFactors := normalizedInvariantFactors checked.S
      if internalFactors != ffiFactors then
        return Except.error <|
          s!"{test.name}: invariant factors differ: " ++
          s!"internal={internalFactors}, ffi={ffiFactors}"
      IO.println s!"{test.name}: {ffiFactors}"
      return Except.ok ()

private def mutationRegression : IO (Except String Unit) := do
  let test := denseCase "mutation" 0xdecafbad 3 4
  match ← generateSNF (.ofMatrix test.matrix) with
  | .error error =>
      return Except.error s!"mutation setup failed: {repr error}"
  | .ok raw =>
      let some first := raw.UInverse.entries[0]?
        | return Except.error "mutation setup produced an empty U inverse"
      let entries := raw.UInverse.entries.set! 0 (first + 1)
      let damaged :=
        { raw with
          UInverse := { raw.UInverse with entries } }
      match checkSNF test.matrix damaged with
      | .error _ =>
          IO.println "damaged certificate: rejected"
          return Except.ok ()
      | .ok _ =>
          return Except.error "damaged certificate was accepted"

private def hnfRegression : IO (Except String Unit) := do
  let test := denseCase "hnf" 0x13579bdf 2 3
  match ← generateAndCheckHNF test.matrix with
  | .error error =>
      return Except.error s!"HNF FFI/checker failure: {repr error}"
  | .ok _ =>
      IO.println "HNF certificate: accepted by pure checker"
      return Except.ok ()

private def malformedProtocolRegression : IO (Except String Unit) := do
  let malformed :=
    "normalforms.decimal/v1\nkind snf\nrows 1\ncols 1\nentries 1\n00\nend\n"
  match ← runRawProtocol malformed with
  | .error _ =>
      IO.println "malformed FFI protocol: rejected"
      return Except.ok ()
  | .ok _ =>
      return Except.error "malformed FFI protocol was accepted"

private def runRegression
    (name : String) (regression : IO (Except String Unit)) :
    IO (Except String Unit) := do
  match ← regression with
  | .ok () => return Except.ok ()
  | .error error => return Except.error s!"{name}: {error}"

public def main : IO UInt32 := do
  for test in cases do
    match ← runCase test with
    | .ok () => pure ()
    | .error error =>
        IO.eprintln s!"normalforms-flint-differential: {error}"
        return 1
  match ← runRegression "HNF" hnfRegression with
  | .error error =>
      IO.eprintln s!"normalforms-flint-differential: {error}"
      return 1
  | .ok () => pure ()
  match ← runRegression "malformed protocol" malformedProtocolRegression with
  | .error error =>
      IO.eprintln s!"normalforms-flint-differential: {error}"
      return 1
  | .ok () => pure ()
  match ← runRegression "mutation" mutationRegression with
  | .ok () =>
      IO.println "FLINT FFI differential regression passed"
      return 0
  | .error error =>
      IO.eprintln s!"normalforms-flint-differential: {error}"
      return 1
