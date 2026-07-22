/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib

/-!
# NormalForms.Basic

Shared imports and project-wide conventions for the `NormalForms` library.
-/

public section

namespace NormalForms

/--
A direct finite enumeration of `Fin` whose construction does not pass through
mathlib's choice-bearing general `Fintype` machinery.
-/
public theorem finRange_nodup_constructive :
    ∀ n : Nat, (List.finRange n).Nodup
  | 0 => by
      rw [List.finRange_zero]
      exact .nil
  | n + 1 => by
      rw [List.finRange_succ]
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨i, _, equality⟩ := List.mem_map.mp member
        exact Fin.succ_ne_zero i equality
      · exact (finRange_nodup_constructive n).map (Fin.succ_injective n)

@[expose, reducible] public def constructiveFinFintype (n : Nat) :
    Fintype (Fin n) where
  elems := ⟨List.finRange n, finRange_nodup_constructive n⟩
  complete := List.mem_finRange

/-
Prefer the direct constructive enumeration over downstream definitionally
equal `Fintype` instances. This keeps canonical `Fin` matrix products out of
`Classical.choice` in strict certificate proofs.
-/
attribute [instance 10000] constructiveFinFintype

end NormalForms
