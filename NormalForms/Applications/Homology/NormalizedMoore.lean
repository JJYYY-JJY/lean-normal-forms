/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.Homology.Mathlib
public import NormalForms.Applications.Homology.Simplicial
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
public import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
# Comparison with mathlib's Normalized Moore Complex

`NormalizedMooreComparison data` records that finite normalized face data is
an enumerated realization of a genuine mathlib simplicial set. The comparison
includes the enumeration of nondegenerate simplices, the interpretation of
degenerate faces, the basis isomorphisms, and their differential compatibility.

From this data we construct:

* an isomorphism with mathlib's normalized nondegenerate chain complex;
* an isomorphism in the Karoubi envelope with mathlib's normalized Moore
  complex;
* the certified cyclic-plus-free decomposition of the simplicial set's
  categorical homology.
-/

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology AlgebraicTopology.DoldKan
open Simplicial

namespace NormalForms.Applications.Homology

/-- The integer coefficient object used by the mathlib simplicial bridge. -/
public abbrev intCoefficientModule : ModuleCat Int :=
  ModuleCat.of Int Int

/--
Certified identification of finite normalized simplex data with a mathlib
simplicial set.

The `face_some` and `face_none` fields pin the finite face table to mathlib's
face maps. `basis` pins each enumerated simplex to the canonical coproduct
generator. `differential` is the resulting chain-level compatibility, retained
as an explicit proof obligation so consumers never rely on an unverified
choice of bases.
-/
public structure NormalizedMooreComparison
    (data : FiniteNormalizedSimplicialData) where
  simplicialSet : SSet
  simplexEquiv :
    ∀ n, Fin (data.simplexCount n) ≃ simplicialSet.nonDegenerate n
  degreeEquiv :
    ∀ n,
      (Fin (data.simplexCount n) → Int) ≃ₗ[Int]
        (simplicialSet.normalizedChainComplex intCoefficientModule).X n
  face_some :
    ∀ n i column target,
      data.face n i column = some target →
        (simplicialSet.δ i) (simplexEquiv (n + 1) column).1 =
          (simplexEquiv n target).1
  face_none :
    ∀ n i column,
      data.face n i column = none →
        (simplicialSet.δ i) (simplexEquiv (n + 1) column).1 ∈
          simplicialSet.degenerate n
  basis :
    ∀ n column,
      degreeEquiv n (Pi.single column 1) =
        simplicialSet.ιNormalizedChainComplex
          (R := intCoefficientModule) (simplexEquiv n column).1 1
  differential :
    ∀ n,
      ModuleCat.ofHom (degreeEquiv (n + 1)).toLinearMap ≫
          (simplicialSet.normalizedChainComplex intCoefficientModule).d
            (n + 1) n =
        ModuleCat.ofHom (data.boundary n).mulVecLin ≫
          ModuleCat.ofHom (degreeEquiv n).toLinearMap

namespace NormalizedMooreComparison

/--
Chain isomorphism from the explicit normalized boundary matrices to mathlib's
normalized chain complex on nondegenerate simplices.
-/
@[expose] public noncomputable def chainIso
    {data : FiniteNormalizedSimplicialData}
    (comparison : NormalizedMooreComparison data) :
    data.toIntChainComplex.toMathlibChainComplex ≅
      comparison.simplicialSet.normalizedChainComplex
        intCoefficientModule :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (comparison.degreeEquiv n).toModuleIso)
    (by
      rintro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      rw [IntChainComplex.toMathlibChainComplex_d]
      exact comparison.differential j)

/--
The splitting of the free integer-module simplicial object used internally by
mathlib's normalized chain complex.
-/
@[expose] public noncomputable def mathlibSplitting
    {data : FiniteNormalizedSimplicialData}
    (comparison : NormalizedMooreComparison data) :
    SimplicialObject.Splitting
      (comparison.simplicialSet ⋙
        Limits.sigmaConst.obj intCoefficientModule) :=
  comparison.simplicialSet.splitting.map
    (Limits.sigmaConst.obj intCoefficientModule)

/--
The explicit matrix complex and mathlib's normalized Moore complex are
isomorphic in the Karoubi envelope.

The middle object is mathlib's nondegenerate-simplex chain complex. The first
isomorphism is supplied by `chainIso`; the remaining two are mathlib's proved
comparison between a split simplicial object, `N₁`, and the normalized Moore
complex.
-/
@[expose] public noncomputable def karoubiNormalizedMooreIso
    {data : FiniteNormalizedSimplicialData}
    (comparison : NormalizedMooreComparison data) :
    (CategoryTheory.Idempotents.toKaroubi
        (ChainComplex (ModuleCat Int) Nat)).obj
          data.toIntChainComplex.toMathlibChainComplex ≅
      (CategoryTheory.Idempotents.toKaroubi
        (ChainComplex (ModuleCat Int) Nat)).obj
          ((AlgebraicTopology.normalizedMooreComplex
              (ModuleCat Int)).obj
            (comparison.simplicialSet ⋙
              Limits.sigmaConst.obj intCoefficientModule)) :=
  ((CategoryTheory.Idempotents.toKaroubi
      (ChainComplex (ModuleCat Int) Nat)).mapIso comparison.chainIso).trans
    (comparison.mathlibSplitting.toKaroubiNondegComplexIsoN₁.trans
      ((N₁_iso_normalizedMooreComplex_comp_toKaroubi
        (ModuleCat Int)).app
          (comparison.simplicialSet ⋙
            Limits.sigmaConst.obj intCoefficientModule)))

/--
Actual chain-complex isomorphism with the normalized Moore complex.

Both sides of `karoubiNormalizedMooreIso` lie in the image of the fully
faithful embedding into the Karoubi envelope, so the isomorphism has a unique
preimage in `ChainComplex (ModuleCat Int) Nat`.
-/
@[expose] public noncomputable def normalizedMooreChainIso
    {data : FiniteNormalizedSimplicialData}
    (comparison : NormalizedMooreComparison data) :
    data.toIntChainComplex.toMathlibChainComplex ≅
      (AlgebraicTopology.normalizedMooreComplex
        (ModuleCat Int)).obj
          (comparison.simplicialSet ⋙
            Limits.sigmaConst.obj intCoefficientModule) :=
  (CategoryTheory.Idempotents.fullyFaithfulToKaroubi
    (ChainComplex (ModuleCat Int) Nat)).preimageIso
      comparison.karoubiNormalizedMooreIso

/--
The explicit computation transported to mathlib's nondegenerate-simplex
normalized chain complex.
-/
@[expose] public noncomputable def normalizedChainHomologyDecomposition
    {data : FiniteNormalizedSimplicialData}
    (comparison : NormalizedMooreComparison data) (n : Nat) :
    (comparison.simplicialSet.normalizedChainComplex
        intCoefficientModule).homology n ≃+
      ((i : Fin
          (data.toIntChainComplex.homologyInvariantFactorCount n)) →
          ZMod (data.toIntChainComplex.homologyInvariantFactor n i)) ×
        (Fin (data.toIntChainComplex.bettiNumber n) → Int) :=
  (HomologicalComplex.homologyMapIso comparison.chainIso n).symm
    |>.toLinearEquiv.toAddEquiv.trans
      (data.toIntChainComplex.mathlibHomologyDecomposition n)

/--
The certified cyclic-plus-free decomposition transported all the way to
mathlib's normalized Moore complex.
-/
@[expose] public noncomputable def normalizedMooreHomologyDecomposition
    {data : FiniteNormalizedSimplicialData}
    (comparison : NormalizedMooreComparison data) (n : Nat) :
    ((AlgebraicTopology.normalizedMooreComplex
        (ModuleCat Int)).obj
          (comparison.simplicialSet ⋙
            Limits.sigmaConst.obj intCoefficientModule)).homology n ≃+
      ((i : Fin
          (data.toIntChainComplex.homologyInvariantFactorCount n)) →
          ZMod (data.toIntChainComplex.homologyInvariantFactor n i)) ×
        (Fin (data.toIntChainComplex.bettiNumber n) → Int) :=
  (HomologicalComplex.homologyMapIso
      comparison.normalizedMooreChainIso n).symm
    |>.toLinearEquiv.toAddEquiv.trans
      (data.toIntChainComplex.mathlibHomologyDecomposition n)

end NormalizedMooreComparison

end NormalForms.Applications.Homology
