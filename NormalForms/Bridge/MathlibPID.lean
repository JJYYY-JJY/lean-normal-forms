import NormalForms.Bridge.MathlibPID.Basic
import NormalForms.Bridge.MathlibPID.Quotient

/-!
# PID Bridge

Top-level entrypoint for the Phase 4 bridge layer.

- `NormalForms.Bridge.MathlibPID.Basic` exposes raw span/readout helpers and
  normalized `Int` coefficient-list readouts on both the executable and
  mathlib sides
- `NormalForms.Bridge.MathlibPID.Quotient` exposes the semantic
  quotient/decomposition bridge together with the current full-rank executable
  versus mathlib compatibility equivalences
-/
