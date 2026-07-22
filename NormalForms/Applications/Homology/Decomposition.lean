/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.Homology.Basis

/-!
# Certified Homology Decomposition

The explicit kernel basis transports degree-`n` boundaries to
`kernelCoordinateMatrix`. Therefore ordinary homology is linearly equivalent
to the cokernel of that finite-free presentation. A second strong Smith
calculation supplies the torsion and free invariants.
-/

public section

namespace NormalForms.Applications.Homology

open NormalForms.Bridge.MathlibPID
open NormalForms.Matrix.Smith

namespace IntChainComplex

theorem kernelBasisEquiv_maps_boundaries
    (complex : IntChainComplex) (n : Nat) :
    Submodule.map
        (complex.kernelBasisEquiv n).symm.toLinearMap
        (complex.boundaries n) =
      (complex.homologyPresentation n).relationSubmodule := by
  change
    Submodule.map
        (complex.kernelBasisEquiv n).symm.toLinearMap
        (LinearMap.range (complex.boundaryCycleMap n)) =
      LinearMap.range (complex.kernelCoordinateMatrix n).mulVecLin
  calc
    Submodule.map
        (complex.kernelBasisEquiv n).symm.toLinearMap
        (LinearMap.range (complex.boundaryCycleMap n)) =
      LinearMap.range
        ((complex.kernelBasisEquiv n).symm.toLinearMap.comp
          (complex.boundaryCycleMap n)) := by
            rw [LinearMap.range_comp]
    _ = LinearMap.range (complex.kernelCoordinateMatrix n).mulVecLin := by
      congr 1
      apply LinearMap.ext
      intro vector
      exact complex.kernelBasisEquiv_symm_boundary n vector

/--
Ordinary homology is the cokernel of `kernelCoordinateMatrix` in the explicit
Smith kernel basis.
-/
@[expose] public noncomputable def homologyPresentationEquiv
    (complex : IntChainComplex) (n : Nat) :
    complex.homology n ≃ₗ[Int]
      (complex.homologyPresentation n).presentedModule := by
  exact
    Submodule.Quotient.equiv
      (complex.boundaries n)
      (complex.homologyPresentation n).relationSubmodule
      (complex.kernelBasisEquiv n).symm
      (kernelBasisEquiv_maps_boundaries complex n)

/-- Strong Smith result for the boundary matrix restricted to `ker d_n`. -/
@[expose] public noncomputable def homologySmithResult
    (complex : IntChainComplex) (n : Nat) :
    SNFResultFin (complex.kernelCoordinateMatrix n) :=
  smithNormalFormFin (complex.kernelCoordinateMatrix n)

/-- Intrinsic Smith data of the restricted boundary matrix. -/
@[expose] public noncomputable def homologySmithData
    (complex : IntChainComplex) (n : Nat) :
    SmithData
      (complex.kernelRank n)
      (complex.rank (n + 1)) Int :=
  (complex.homologySmithResult n).smithData

/-- Number of nonzero homology presentation factors, including units. -/
@[expose] public noncomputable def homologyInvariantFactorCount
    (complex : IntChainComplex) (n : Nat) : Nat :=
  pidExecutableInvariantFactorCount (complex.kernelCoordinateMatrix n)

/-- The `i`th normalized homology presentation factor as a natural number. -/
@[expose] public noncomputable def homologyInvariantFactor
    (complex : IntChainComplex) (n : Nat)
    (i : Fin (complex.homologyInvariantFactorCount n)) : Nat :=
  (pidExecutableInvariantFactorFn
    (complex.kernelCoordinateMatrix n) i).natAbs

/--
All normalized nonzero factors of the homology presentation, including unit
factors whose cyclic quotient is zero.
-/
@[expose] public noncomputable def homologyInvariantFactors
    (complex : IntChainComplex) (n : Nat) : List Nat :=
  pidExecutableSmithCoeffNatAbsList (complex.kernelCoordinateMatrix n)

/-- Rank of the free abelian summand of degree-`n` homology. -/
@[expose] public noncomputable def bettiNumber
    (complex : IntChainComplex) (n : Nat) : Nat :=
  complex.kernelRank n - complex.homologyInvariantFactorCount n

/-- Human-facing torsion factors; unit factors are omitted. -/
@[expose] public noncomputable def homologyTorsionFactors
    (complex : IntChainComplex) (n : Nat) : List Nat :=
  (complex.homologyInvariantFactors n).filter (fun factor => 1 < factor)

@[simp] public theorem homologyInvariantFactors_length
    (complex : IntChainComplex) (n : Nat) :
    (complex.homologyInvariantFactors n).length =
      complex.homologyInvariantFactorCount n := by
  exact pidExecutableSmithCoeffNatAbsList_length_eq_count _

@[simp] public theorem homologyPresentation_freeRank
    (complex : IntChainComplex) (n : Nat) :
    (complex.homologyPresentation n).freeRank =
      complex.bettiNumber n := by
  change
    Fintype.card (Fin (complex.kernelRank n)) -
        pidExecutableInvariantFactorCount
          (complex.kernelCoordinateMatrix n) =
      complex.kernelRank n -
        pidExecutableInvariantFactorCount
          (complex.kernelCoordinateMatrix n)
  rw [Fintype.card_fin]

/--
Certified torsion-plus-free decomposition of ordinary degree-`n` homology.

Unit invariant factors remain in the theorem-facing product as zero cyclic
summands. `homologyTorsionFactors` is the separate display projection that
removes them.
-/
@[expose] public noncomputable def homologyDecomposition
    (complex : IntChainComplex) (n : Nat) :
    complex.homology n ≃+
      (((i : Fin (complex.homologyInvariantFactorCount n)) →
          ZMod (complex.homologyInvariantFactor n i)) ×
        (Fin (complex.bettiNumber n) → Int)) := by
  let presentationEquiv := complex.homologyPresentationEquiv n
  let smithEquiv :=
    pidExecutableQuotientEquivPiZModProd
      (complex.kernelCoordinateMatrix n)
  let columnSpanEquiv :
      (complex.homologyPresentation n).presentedModule ≃ₗ[Int]
        ((Fin (complex.kernelRank n) → Int) ⧸
          pidSmithColumnSpan (complex.kernelCoordinateMatrix n)) := by
    apply Submodule.quotEquivOfEq
    change
      LinearMap.range (complex.kernelCoordinateMatrix n).mulVecLin =
        pidSmithColumnSpan (complex.kernelCoordinateMatrix n)
    exact
      (pidSmithColumnSpan_eq_range_mulVecLin
        (complex.kernelCoordinateMatrix n)).symm
  let normalizedSmithEquiv :
      ((Fin (complex.kernelRank n) → Int) ⧸
          pidSmithColumnSpan (complex.kernelCoordinateMatrix n)) ≃+
        (((i : Fin (complex.homologyInvariantFactorCount n)) →
            ZMod (complex.homologyInvariantFactor n i)) ×
          (Fin (complex.bettiNumber n) → Int)) := by
    rw [Fintype.card_fin] at smithEquiv
    exact smithEquiv
  exact presentationEquiv.toAddEquiv.trans <|
    columnSpanEquiv.toAddEquiv.trans normalizedSmithEquiv

end IntChainComplex

end NormalForms.Applications.Homology
