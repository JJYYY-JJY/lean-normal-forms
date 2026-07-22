/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.Homology.Decomposition
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Comparison with mathlib Homological Complexes

This module realizes an `IntChainComplex` as a mathlib chain complex of
`ModuleCat Int` objects. It also compares the project's explicit quotient
`ker dₙ / im dₙ₊₁` with mathlib's categorical homology.

There is one deliberate edge case: mathlib's canonical degree-zero short
complex uses the zero endomorphism `C₀ ⟶ C₀`, while this project uses the
unique map `C₀ ⟶ 0`. The comparison map below handles that case explicitly.
-/

public section

open CategoryTheory

namespace NormalForms.Applications.Homology

open scoped Matrix

namespace IntChainComplex

/--
The finite-free integer chain complex as mathlib's
`ChainComplex (ModuleCat Int) Nat`.
-/
@[expose] public noncomputable def toMathlibChainComplex
    (complex : IntChainComplex) :
    ChainComplex (ModuleCat Int) Nat :=
  ChainComplex.of
    (fun n => ModuleCat.of Int (Fin (complex.rank n) → Int))
    (fun n => ModuleCat.ofHom (complex.boundary n).mulVecLin)
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro vector
      funext row
      change (complex.boundary n).mulVec
          ((complex.boundary (n + 1)).mulVec vector) row = 0
      rw [Matrix.mulVec_mulVec, complex.boundary_squared]
      exact congrFun (Matrix.zero_mulVec vector) row)

@[simp] public theorem toMathlibChainComplex_X
    (complex : IntChainComplex) (n : Nat) :
    (complex.toMathlibChainComplex).X n =
      ModuleCat.of Int (Fin (complex.rank n) → Int) :=
  rfl

@[simp] public theorem toMathlibChainComplex_d
    (complex : IntChainComplex) (n : Nat) :
    (complex.toMathlibChainComplex).d (n + 1) n =
      ModuleCat.ofHom (complex.boundary n).mulVecLin := by
  change
    ChainComplex.of.d
        (fun k => ModuleCat.of Int (Fin (complex.rank k) → Int))
        (fun k => ModuleCat.ofHom (complex.boundary k).mulVecLin)
        (n + 1) n =
      ModuleCat.ofHom (complex.boundary n).mulVecLin
  apply ChainComplex.of_d

/--
The degree-`n` short complex using the project's explicit zero target in
degree zero.
-/
@[expose] public noncomputable def mathlibDegreeShortComplex
    (complex : IntChainComplex) (n : Nat) :
    ShortComplex (ModuleCat Int) :=
  ShortComplex.moduleCatMk
    (complex.incomingBoundary n).mulVecLin
    (complex.outgoingBoundary n).mulVecLin
    (by
      apply LinearMap.ext
      intro vector
      funext row
      change (complex.outgoingBoundary n).mulVec
          ((complex.incomingBoundary n).mulVec vector) row = 0
      rw [Matrix.mulVec_mulVec, complex.outgoing_mul_incoming]
      exact congrFun (Matrix.zero_mulVec vector) row)

/--
The concrete quotient underlying the degree short complex is definitionally
the project's intrinsic homology quotient.
-/
@[expose] public noncomputable def homologyToDegreeQuotient
    (complex : IntChainComplex) (n : Nat) :
    complex.homology n ≃ₗ[Int]
      (complex.mathlibDegreeShortComplex n).moduleCatLeftHomologyData.H :=
  LinearEquiv.refl Int _

/--
Comparison from the explicit degree short complex to the canonical short
complex extracted by mathlib. Its third component is the zero map
`0 ⟶ C₀` in degree zero and the identity in positive degrees.
-/
@[expose] public noncomputable def degreeShortComplexToSc
    (complex : IntChainComplex) :
    (n : Nat) →
      complex.mathlibDegreeShortComplex n ⟶
        complex.toMathlibChainComplex.sc n
  | 0 =>
      { τ₁ := (complex.toMathlibChainComplex.XIsoOfEq
          (ChainComplex.prev Nat 0)).inv
        τ₂ := 𝟙 _
        τ₃ := 0
        comm₁₂ := by
          change
            (complex.toMathlibChainComplex.XIsoOfEq
                (ChainComplex.prev Nat 0)).inv ≫
                complex.toMathlibChainComplex.d
                  ((ComplexShape.down Nat).prev 0) 0 =
              ModuleCat.ofHom (complex.boundary 0).mulVecLin
          rw [HomologicalComplex.XIsoOfEq_inv_comp_d]
          exact complex.toMathlibChainComplex_d 0
        comm₂₃ := by
          change
            complex.toMathlibChainComplex.d
                0 ((ComplexShape.down Nat).next 0) =
              0
          exact
            complex.toMathlibChainComplex.shape
              0 ((ComplexShape.down Nat).next 0) (by simp) }
  | n + 1 =>
      { τ₁ := (complex.toMathlibChainComplex.XIsoOfEq
          (ChainComplex.prev Nat (n + 1))).inv
        τ₂ := 𝟙 _
        τ₃ := (complex.toMathlibChainComplex.XIsoOfEq
          (ChainComplex.next_nat_succ n)).inv
        comm₁₂ := by
          change
            (complex.toMathlibChainComplex.XIsoOfEq
                (ChainComplex.prev Nat (n + 1))).inv ≫
                complex.toMathlibChainComplex.d
                  ((ComplexShape.down Nat).prev (n + 1)) (n + 1) =
              ModuleCat.ofHom (complex.boundary (n + 1)).mulVecLin
          rw [HomologicalComplex.XIsoOfEq_inv_comp_d]
          exact complex.toMathlibChainComplex_d (n + 1)
        comm₂₃ := by
          change
            complex.toMathlibChainComplex.d
                (n + 1) ((ComplexShape.down Nat).next (n + 1)) =
              ModuleCat.ofHom (complex.boundary n).mulVecLin ≫
                (complex.toMathlibChainComplex.XIsoOfEq
                  (ChainComplex.next_nat_succ n)).inv
          rw [← complex.toMathlibChainComplex_d n]
          exact
            (complex.toMathlibChainComplex.d_comp_XIsoOfEq_inv
              (ChainComplex.next_nat_succ n) (n + 1)).symm }

/--
The categorical homology of the explicit degree short complex agrees with
mathlib's homology of `toMathlibChainComplex`.
-/
@[expose] public noncomputable def degreeHomologyIso
    (complex : IntChainComplex) (n : Nat) :
    (complex.mathlibDegreeShortComplex n).homology ≅
      complex.toMathlibChainComplex.homology n := by
  let comparison := complex.degreeShortComplexToSc n
  haveI : Epi comparison.τ₁ := by
    cases n <;>
      dsimp [comparison, degreeShortComplexToSc] <;>
      infer_instance
  haveI : IsIso comparison.τ₂ := by
    cases n <;>
      dsimp [comparison, degreeShortComplexToSc] <;>
      exact IsIso.id _
  haveI : Mono comparison.τ₃ := by
    cases n with
    | zero =>
        rw [ModuleCat.mono_iff_injective]
        intro left right _
        funext i
        exact Fin.elim0 i
    | succ n =>
        dsimp [comparison, degreeShortComplexToSc]
        infer_instance
  let homologyComparison := ShortComplex.homologyMap comparison
  let homologyComparisonIsIso : IsIso homologyComparison := by
    dsimp [homologyComparison]
    exact
      ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono comparison
  exact @asIso _ _ _ _ homologyComparison homologyComparisonIsIso

/--
Linear equivalence between the project's intrinsic homology quotient and
mathlib's categorical homology object.
-/
@[expose] public noncomputable def mathlibHomologyEquiv
    (complex : IntChainComplex) (n : Nat) :
    complex.homology n ≃ₗ[Int]
      complex.toMathlibChainComplex.homology n :=
  (complex.homologyToDegreeQuotient n).trans
    ((complex.mathlibDegreeShortComplex n).moduleCatHomologyIso.symm.toLinearEquiv.trans
      (complex.degreeHomologyIso n).toLinearEquiv)

/--
The certified cyclic-plus-free decomposition transported to mathlib's
categorical homology object.
-/
@[expose] public noncomputable def mathlibHomologyDecomposition
    (complex : IntChainComplex) (n : Nat) :
    complex.toMathlibChainComplex.homology n ≃+
      ((i : Fin (complex.homologyInvariantFactorCount n)) →
          ZMod (complex.homologyInvariantFactor n i)) ×
        (Fin (complex.bettiNumber n) → Int) :=
  (complex.mathlibHomologyEquiv n).symm.toAddEquiv.trans
    (complex.homologyDecomposition n)

end IntChainComplex

end NormalForms.Applications.Homology
