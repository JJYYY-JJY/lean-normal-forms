/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Basic

/-!
# Expected matrices for generated certificate imports

This module deliberately contains only caller-owned matrices. Generated
certificate modules must import it and bind their payload to these names.
-/

public section

namespace NormalForms.Tests.Generated

public def mediumInput : Matrix (Fin 4) (Fin 5) Int :=
  !![2, 0, 0, 0, 0;
     0, 6, 0, 0, 0;
     0, 0, 30, 0, 0;
     0, 0, 0, 0, 0]

public def otherInput : Matrix (Fin 4) (Fin 5) Int :=
  !![7, 0, 0, 0, 0;
     0, 6, 0, 0, 0;
     0, 0, 30, 0, 0;
     0, 0, 0, 0, 0]

end NormalForms.Tests.Generated
