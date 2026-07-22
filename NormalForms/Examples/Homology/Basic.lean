/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.Homology

/-!
# Finite Cellular Chain-Complex Examples

Small integral cellular chain complexes used by the executable homology
regressions. They remain outside the homology facade.
-/

public section

namespace NormalForms.Examples.Homology

open NormalForms.Applications.Homology

/-- Cellular chain complex of the circle. -/
@[expose] public def circle : IntChainComplex :=
  IntChainComplex.ofLengthTwo
    1 1 0
    (0 : Matrix (Fin 1) (Fin 1) Int)
    (0 : Matrix (Fin 1) (Fin 0) Int)
    (by simp)

/-- Standard one-cell-per-dimension cellular chain complex of the torus. -/
@[expose] public def torus : IntChainComplex :=
  IntChainComplex.ofLengthTwo
    1 2 1
    (0 : Matrix (Fin 1) (Fin 2) Int)
    (0 : Matrix (Fin 2) (Fin 1) Int)
    (by simp)

/-- Cellular chain complex of the real projective plane, with `d₂ = 2`. -/
@[expose] public def realProjectivePlane : IntChainComplex :=
  IntChainComplex.ofLengthTwo
    1 1 1
    (0 : Matrix (Fin 1) (Fin 1) Int)
    !![2]
    (by simp)

/--
A finite cellular example with `H₁ ≅ ℤ × ℤ/6`: one free circle and one
degree-two cell attached by degree six.
-/
@[expose] public def circleWithSixCell : IntChainComplex :=
  IntChainComplex.ofLengthTwo
    1 2 1
    (0 : Matrix (Fin 1) (Fin 2) Int)
    !![0;
       6]
    (by simp)

end NormalForms.Examples.Homology
