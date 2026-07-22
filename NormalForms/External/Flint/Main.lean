/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.External.Flint.FFI

/-!
# Raw FLINT FFI worker executable

This optional executable has the same stdin/stdout decimal protocol as the C
worker, but crosses the Lean native FFI boundary. It emits no proof or checked
result.
-/

open NormalForms.External.Flint

public def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match ← runRawProtocol input with
  | .ok output =>
      IO.print output
      return 0
  | .error error =>
      IO.eprint error
      return 2
