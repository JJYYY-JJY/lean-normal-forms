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
# Companion-Matrix Tests

The tests execute the subdiagonal/last-column convention and verify the
power-basis and characteristic-polynomial specifications.
-/

namespace NormalForms.Tests.RationalCanonical.Companion

open Polynomial
open NormalForms.RationalCanonical

private noncomputable def quadratic : Rat[X] :=
  X ^ 2 - C 3 * X + C 2

private def diagonalOneTwo : Matrix (Fin 2) (Fin 2) Rat :=
  !![1, 0;
     0, 2]

private def scalarTwo : Matrix (Fin 1) (Fin 1) Rat :=
  !![2]

private def companionEntries (p : Rat[X]) : List (List Rat) :=
  (List.finRange p.natDegree).map fun i =>
    (List.finRange p.natDegree).map fun j =>
      companionMatrix p i j

private def executableQuadratic : Rat[X] :=
  endomorphismInvariantFactor diagonalOneTwo 1

private def executableLinear : Rat[X] :=
  endomorphismInvariantFactor scalarTwo 0

#guard
  companionEntries executableQuadratic ==
    [[0, -2], [1, 3]]
#guard
  companionEntries executableLinear == [[2]]

example : quadratic.Monic := by
  rw [quadratic, sub_eq_add_neg, add_assoc]
  apply monic_X_pow_add
  rw [degree_add_eq_left_of_degree_lt]
  · norm_num
  · norm_num

example :
    (companionMatrix quadratic).charpoly = quadratic :=
  companionMatrix_charpoly quadratic (by
    rw [quadratic, sub_eq_add_neg, add_assoc]
    apply monic_X_pow_add
    rw [degree_add_eq_left_of_degree_lt]
    · norm_num
    · norm_num)

example :
    companionMatrix quadratic =
      LinearMap.toMatrix
        (AdjoinRoot.powerBasis' (by
          rw [quadratic, sub_eq_add_neg, add_assoc]
          apply monic_X_pow_add
          rw [degree_add_eq_left_of_degree_lt]
          · norm_num
          · norm_num)).basis
        (AdjoinRoot.powerBasis' (by
          rw [quadratic, sub_eq_add_neg, add_assoc]
          apply monic_X_pow_add
          rw [degree_add_eq_left_of_degree_lt]
          · norm_num
          · norm_num)).basis
        ((Algebra.lmul Rat (AdjoinRoot quadratic))
          (AdjoinRoot.root quadratic)) :=
  companionMatrix_eq_toMatrix quadratic (by
    rw [quadratic, sub_eq_add_neg, add_assoc]
    apply monic_X_pow_add
    rw [degree_add_eq_left_of_degree_lt]
    · norm_num
    · norm_num)

example :
    (companionMatrix (1 : Rat[X])).charpoly = 1 :=
  companionMatrix_charpoly 1 monic_one

end NormalForms.Tests.RationalCanonical.Companion
