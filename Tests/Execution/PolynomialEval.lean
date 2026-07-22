/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Euclidean.PolynomialRat
import all NormalForms.Matrix.PolynomialRat
meta import all NormalForms.Euclidean.PolynomialRat
meta import all NormalForms.Matrix.PolynomialRat

set_option linter.hashCommand false
set_option linter.privateModule false

open NormalForms.PolynomialRatRuntime
open scoped Matrix

private def input : Matrix (Fin 1) (Fin 1) RuntimePolynomial :=
  !![mul (C (-2)) (add X one)]

private def expected : Matrix (Fin 1) (Fin 1) RuntimePolynomial :=
  !![add X one]

-- The standalone harness must print exactly `true`.
#eval certificateChecksFin input expected expected
