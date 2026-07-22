/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.Internal.Algorithm

/-!
# Fuelled LLL diagnostics

This implementation-facing module exposes bounded transition telemetry without
placing recursive state or pivot helpers in the stable research facade.
-/

@[expose] public section

namespace NormalForms.Research.LLL

/-- Execute at most `fuel` outer LLL transitions and check the final candidate. -/
public def fullRankLLLWithFuel {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (fuel : Nat) : FuelledLLLRun basis :=
  Internal.publicFuelledRun basis fuel

/-- Return a strong result exactly when the bounded run finishes and checks. -/
public def fullRankLLLWithFuel? {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (fuel : Nat) :
    Option (FullRankLLLResult basis) :=
  (fullRankLLLWithFuel basis fuel).certified

end NormalForms.Research.LLL
