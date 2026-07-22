/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Euclidean.Int
import all NormalForms.Matrix.Hermite.Algorithm
import all NormalForms.Matrix.Smith.Algorithm
meta import all NormalForms.Euclidean.Int
meta import all NormalForms.Matrix.Hermite.Algorithm
meta import all NormalForms.Matrix.Smith.Algorithm

set_option linter.hashCommand false
set_option linter.privateModule false

open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith
open scoped Matrix

private def input : Matrix (Fin 2) (Fin 3) Int :=
  !![6, 15, 9;
     4, 10, 6]

-- Prints `H` and `S`; the expected deterministic pair is
-- `(!![2, 5, 3; 0, 0, 0], !![1, 0, 0; 0, 0, 0])`.
#eval ((hermiteNormalFormFin input).H, (smithNormalFormFin input).S)
