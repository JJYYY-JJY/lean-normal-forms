/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Basic

/-!
# Caller-owned matrices for optional external adapters

This module contains no adapter code and links no external library. Dedicated
external-adapter tests bind generated certificates to these exact Lean values.
-/

public section

namespace NormalForms.Tests.External

public def nontrivial : Matrix (Fin 3) (Fin 4) Int :=
  !![6, 9, 3, 0;
     4, 6, 2, 8;
     2, 5, 7, 4]

public def rankDeficient : Matrix (Fin 3) (Fin 4) Int :=
  !![2, 3, 1, 4;
     4, 6, 2, 8;
     6, 9, 3, 12]

public def benchmarkSmall : Matrix (Fin 2) (Fin 3) Int :=
  !![2, 4, 0;
     6, 8, 0]

public def zeroRows : Matrix (Fin 0) (Fin 3) Int :=
  0

public def zeroColumns : Matrix (Fin 3) (Fin 0) Int :=
  0

end NormalForms.Tests.External
