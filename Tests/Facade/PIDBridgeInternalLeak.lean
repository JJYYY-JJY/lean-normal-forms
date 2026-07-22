/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms

/-!
This file must not compile: projective splitting used by the mathlib PID bridge
is an implementation detail rather than part of the `NormalForms` facade.
-/

#check NormalForms.Bridge.MathlibPID.Internal.pidSmithRangeSplitting
