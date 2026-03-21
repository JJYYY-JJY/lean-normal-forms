import NormalForms.Bridge.MathlibPID.Basic
import NormalForms.Bridge.MathlibPID.Quotient

/-!
# PID Bridge

Top-level entrypoint for the Phase 4 PID bridge layer.

- `NormalForms.Bridge.MathlibPID.Basic` exposes raw span/readout helpers and
  normalized `Int` coefficient-list readouts on both the executable and
  mathlib sides
- `NormalForms.Bridge.MathlibPID.Quotient` exposes the semantic
  quotient/decomposition bridge together with the current full-rank executable
  versus mathlib compatibility equivalences

The current coefficient-facing closure is example-level rather than abstract:
the literal full-rank `Int` list-equality proofs live in
`NormalForms.Examples.AbelianGroups.Basic`. A generic theorem comparing
mathlib's chosen `smithNormalFormCoeffs` witness list against the executable
list remains blocked on missing witness-canonicality results upstream.
-/
