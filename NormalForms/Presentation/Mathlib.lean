/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Presentation.Basic
public import Mathlib.Algebra.Module.Presentation.Basic

/-!
# Mathlib Presentation Bridge

This module converts a column-oriented `FiniteFreePresentation` to mathlib's
finitely supported `Module.Relations` representation.  It proves that the
mathlib quotient is linearly equivalent to the cokernel used by the project,
then packages that equivalence as a `Module.Presentation`.
-/

@[expose] public noncomputable section

namespace NormalForms

namespace FiniteFreePresentation

/--
The mathlib relations encoded by the columns of a finite-free presentation.
-/
public def mathlibRelations
    {R : Type _} [CommRing R]
    (presentation : FiniteFreePresentation R) :
    Module.Relations R where
  G := Fin presentation.numGenerators
  R := Fin presentation.numRelations
  relation j :=
    (Finsupp.linearEquivFunOnFinite
      R R (Fin presentation.numGenerators)).symm
      (presentation.relationMatrix.col j)

@[simp] public theorem mathlibRelations_relation_apply
    {R : Type _} [CommRing R]
    (presentation : FiniteFreePresentation R)
    (j : Fin presentation.numRelations)
    (i : Fin presentation.numGenerators) :
    presentation.mathlibRelations.relation j i =
      presentation.relationMatrix i j :=
  rfl

/--
The quotient of mathlib's finitely supported relations is the same cokernel as
`presentedModule`.
-/
public def mathlibQuotientEquivPresentedModule
    {R : Type _} [CommRing R]
    (presentation : FiniteFreePresentation R) :
    presentation.mathlibRelations.Quotient ≃ₗ[R]
      presentation.presentedModule := by
  let generatorEquiv :
      (Fin presentation.numGenerators →₀ R) ≃ₗ[R]
        presentation.generatorModule :=
    Finsupp.linearEquivFunOnFinite
      R R (Fin presentation.numGenerators)
  have hmap :
      Submodule.map generatorEquiv.toLinearMap
          (Submodule.span R
            (Set.range presentation.mathlibRelations.relation)) =
        presentation.relationSubmodule := by
    rw [Submodule.map_span, relationSubmodule, relationMap,
      _root_.Matrix.range_mulVecLin]
    apply congrArg (Submodule.span R)
    ext x
    constructor
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, by
        ext i
        rfl⟩
    · rintro ⟨j, rfl⟩
      refine
        ⟨presentation.mathlibRelations.relation j, ⟨j, rfl⟩, ?_⟩
      ext i
      rfl
  let quotientInstanceEquiv :
      presentation.mathlibRelations.Quotient ≃ₗ[R]
        ((presentation.mathlibRelations.G →₀ R) ⧸
          Submodule.span R
            (Set.range presentation.mathlibRelations.relation)) :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let quotientEquiv :=
    Submodule.Quotient.equiv
      (Submodule.span R
        (Set.range presentation.mathlibRelations.relation))
      presentation.relationSubmodule
      generatorEquiv
      hmap
  exact quotientInstanceEquiv.trans quotientEquiv

/--
A mathlib `Module.Presentation` of the project's presented cokernel.
-/
public def mathlibPresentation
    {R : Type _} [CommRing R]
    (presentation : FiniteFreePresentation R) :
    Module.Presentation R presentation.presentedModule := by
  let quotientPresentation :
      Module.Presentation R
        presentation.mathlibRelations.Quotient :=
    Module.Presentation.ofIsPresentation
      (Module.Relations.Solution.ofQuotient_isPresentation
        presentation.mathlibRelations)
  exact
    Module.Presentation.ofLinearEquiv quotientPresentation
      presentation.mathlibQuotientEquivPresentedModule

end FiniteFreePresentation

end NormalForms
