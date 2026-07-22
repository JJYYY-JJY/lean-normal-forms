/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Bridge.MathlibPID.Basic
public import NormalForms.Bridge.MathlibPID.Signature
public import NormalForms.Bridge.MathlibPID.Quotient

/-!
# PID Bridge

Top-level entrypoint for the Phase 4 PID bridge layer.

- `NormalForms.Bridge.MathlibPID.Basic` exposes raw span/readout helpers and
  normalized `Int` coefficient-list readouts on both the executable and
  mathlib sides
- `NormalForms.Bridge.MathlibPID.Signature` exposes the intrinsic three-level
  bridge through canonical mathlib diagonal bases
- `NormalForms.Bridge.MathlibPID.Quotient` exposes the semantic
  quotient/decomposition bridge together with the current full-rank executable
  versus mathlib compatibility equivalences

The raw mathlib witness remains available, but coefficient comparison requires
`CanonicalPIDSmithBasis` because mathlib's structure does not itself store a
normalization or divisibility-chain field.
-/

public section
