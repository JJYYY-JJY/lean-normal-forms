/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.Data.Rat.Floor

/-!
# Fixed LLL parameters and exact rounding

The research profile fixes the classical exact parameters
`delta = 3/4` and `eta = 1/2`.  Rounding is performed in `Rat`, with the
tie convention inherited from `Int.round`.
-/

@[expose] public section

namespace NormalForms.Research.LLL

/-- The fixed Lovasz parameter used by the profile. -/
public def delta : Rat := 3 / 4

/-- The fixed size-reduction parameter used by the profile. -/
public def eta : Rat := 1 / 2

/-- Exact nearest-integer rounding for rational Gram--Schmidt coefficients. -/
public def nearestInteger (value : Rat) : Int :=
  round value

@[simp] public theorem delta_eq : delta = (3 : Rat) / 4 := rfl

@[simp] public theorem eta_eq : eta = (1 : Rat) / 2 := rfl

public theorem delta_gt_quarter : (1 : Rat) / 4 < delta := by
  norm_num [delta]

public theorem delta_lt_one : delta < 1 := by
  norm_num [delta]

public theorem eta_nonnegative : 0 <= eta := by
  norm_num [eta]

public theorem eta_lt_one : eta < 1 := by
  norm_num [eta]

/-- Rounding leaves a residual of absolute value at most `eta`. -/
public theorem abs_sub_nearestInteger_le (value : Rat) :
    |value - nearestInteger value| <= eta := by
  simpa [nearestInteger, eta] using abs_sub_round value

end NormalForms.Research.LLL
