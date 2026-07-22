/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Applications.RationalCanonical
meta import NormalForms.Applications.RationalCanonical

set_option linter.privateModule false
set_option linter.hashCommand false

/-!
# Rational Canonical Module-Decomposition Tests

Regression coverage for the strong polynomial Smith result, the
presentation-to-`Module.AEval'` equivalence, executable diagonal factors, and
the complete cyclic decomposition.
-/

namespace NormalForms.Tests.RationalCanonical.ModuleDecomposition

open Polynomial
open NormalForms
open NormalForms.RationalCanonical

private def scalarTwo : Matrix (Fin 1) (Fin 1) Rat :=
  !![2]

private def diagonalOneTwo : Matrix (Fin 2) (Fin 2) Rat :=
  !![1, 0;
     0, 2]

private def emptyMatrix : Matrix (Fin 0) (Fin 0) Rat :=
  0

example :
    (endomorphismPresentation diagonalOneTwo).relationMatrix =
      endomorphismPresentationMatrix diagonalOneTwo :=
  rfl

example :
    (endomorphismSmithResult diagonalOneTwo).U *
          endomorphismPresentationMatrix diagonalOneTwo *
          (endomorphismSmithResult diagonalOneTwo).V =
        (endomorphismSmithResult diagonalOneTwo).S :=
  (endomorphismSmithResult diagonalOneTwo).equation

example (x : EndomorphismModule scalarTwo) :
    endomorphismPresentationEquivAEval scalarTwo
        ((endomorphismPresentationEquivAEval scalarTwo).symm x) =
      x :=
  (endomorphismPresentationEquivAEval scalarTwo).apply_symm_apply x

example
    (x : (endomorphismPresentation scalarTwo).presentedModule) :
    (endomorphismPresentationEquivAEval scalarTwo).symm
        (endomorphismPresentationEquivAEval scalarTwo x) =
      x :=
  (endomorphismPresentationEquivAEval scalarTwo).symm_apply_apply x

example (x : EndomorphismModule diagonalOneTwo) :
    (endomorphismCyclicDecomposition diagonalOneTwo).symm
        (endomorphismCyclicDecomposition diagonalOneTwo x) =
      x :=
  (endomorphismCyclicDecomposition diagonalOneTwo).symm_apply_apply x

example :
    endomorphismInvariantFactors diagonalOneTwo =
      (List.finRange 2).map
        (endomorphismInvariantFactor diagonalOneTwo) :=
  endomorphismInvariantFactors_eq_diagonal diagonalOneTwo

private def diagonalFactorChecks : Bool :=
  let first := endomorphismInvariantFactor diagonalOneTwo 0
  let second := endomorphismInvariantFactor diagonalOneTwo 1
  first.coeff 0 == 1 &&
    first.natDegree == 0 &&
    second.coeff 0 == 2 &&
    second.coeff 1 == -3 &&
    second.coeff 2 == 1 &&
    second.natDegree == 2

#guard diagonalFactorChecks

example (factor : Rat[X]) (hunit : IsUnit factor) :
    factor ∉
      endomorphismDisplayInvariantFactors diagonalOneTwo := by
  intro hmem
  exact
    (mem_endomorphismDisplayInvariantFactors
      diagonalOneTwo factor).mp hmem |>.2 hunit

noncomputable example :
    EndomorphismModule emptyMatrix ≃ₗ[Rat[X]]
      ((i : Fin 0) →
        Rat[X] ⧸
          Ideal.span
            ({endomorphismInvariantFactor emptyMatrix i} :
              Set Rat[X])) :=
  endomorphismCyclicDecomposition emptyMatrix

end NormalForms.Tests.RationalCanonical.ModuleDecomposition
