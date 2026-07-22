/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Applications.Homology

set_option linter.privateModule false

/-!
# Chain-complex orientation regressions
-/

namespace NormalForms.Tests.Homology

open NormalForms.Applications.Homology

private def intervalComplex : IntChainComplex where
  topDegree := 1
  rank
    | 0 => 2
    | 1 => 1
    | _ => 0
  finiteSupport := by
    intro n hn
    rcases n with _ | n
    · omega
    rcases n with _ | n
    · omega
    rfl
  boundary
    | 0 => fun
        | ⟨0, _⟩, _ => (-1 : Int)
        | ⟨1, _⟩, _ => 1
    | _ + 1 => 0
  boundary_squared := by
    intro n
    cases n <;> simp

example :
    intervalComplex.outgoingBoundary 1 =
      intervalComplex.boundary 0 :=
  rfl

example :
    intervalComplex.outgoingBoundary 0 =
      (0 : Matrix (Fin 0) (Fin 2) Int) :=
  rfl

example :
    intervalComplex.outgoingBoundary 1 *
        intervalComplex.incomingBoundary 1 =
      0 :=
  intervalComplex.outgoing_mul_incoming 1

example (vector : Fin 1 → Int) :
    (intervalComplex.boundaryCycleMap 0 vector).1 =
      (intervalComplex.boundary 0).mulVec vector := by
  rfl

end NormalForms.Tests.Homology
