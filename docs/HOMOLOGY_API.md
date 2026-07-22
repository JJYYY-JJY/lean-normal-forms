# Finite-free integer homology API

Version: 1.2.2

Import the independently versioned application facade:

```lean
import NormalForms.Applications.Homology
```

The package-level `NormalForms` facade remains the frozen 1.0 HNF/SNF core
and does not re-export this application. The compile-time API baseline is
`NormalForms/Tests/Homology/PublicApi.lean`.

## Chain convention

```lean
structure IntChainComplex where
  topDegree : Nat
  rank : Nat → Nat
  finiteSupport : ∀ n, topDegree < n → rank n = 0
  boundary :
    (n : Nat) →
      Matrix (Fin (rank n)) (Fin (rank (n + 1))) Int
  boundary_squared :
    ∀ n, boundary n * boundary (n + 1) = 0
```

`boundary n` represents the column-vector map

```text
d_(n+1) : C_(n+1) → C_n.
```

Rows therefore index the basis of `C_n`; columns index the basis of
`C_(n+1)`. The derived `outgoingBoundary n` is `d_n`, while
`incomingBoundary n` is `d_(n+1)`. Degree zero uses the unique
`0 × rank 0` outgoing matrix.

`cycles`, `boundaries`, and `homology` denote

```text
ker d_n
im d_(n+1) inside ker d_n
ker d_n / im d_(n+1)
```

respectively. `outgoing_mul_incoming` is the matrix form of
`d_n d_(n+1) = 0`.

## Certified computation

The degree-`n` calculation follows six explicit steps.

1. `outgoingSmithResult n` computes a strong Smith result
   `U * d_n * V = S`, including chosen inverses for `U` and `V`.
2. The columns of `V` after the nonzero diagonal prefix form the basis
   `kernelBasisEquiv n : Int^kernelRank ≃ₗ ker d_n`.
3. `incomingSmithCoordinates n` computes `V⁻¹ * d_(n+1)`.
4. `incomingSmithCoordinates_leading_zero` proves every coordinate before
   the kernel tail is zero.
5. `kernelCoordinateMatrix n` restricts to the kernel tail, and
   `homologySmithResult n` performs a second strong Smith calculation.
6. `homologyPresentationEquiv` identifies ordinary homology with the
   resulting cokernel, and `homologyDecomposition` gives its complete
   torsion-plus-free decomposition.

The theorem-facing decomposition is:

```lean
homologyDecomposition :
  complex.homology n ≃+
    (((i : Fin (complex.homologyInvariantFactorCount n)) →
        ZMod (complex.homologyInvariantFactor n i)) ×
      (Fin (complex.bettiNumber n) → Int))
```

Unit factors remain in this product as zero cyclic summands. The display
reader `homologyTorsionFactors` filters them; it does not alter the theorem
data.

## Executable projection

The semantic quotient equivalences are noncomputable, but the full matrix
path is executable:

```lean
runtimeOutgoingRank
runtimeKernelCoordinateMatrix
runtimeHomologySmithResult
runtimeHomologyInvariantFactors
runtimeHomologyTorsionFactors
runtimeBettiNumber
runtimeHomologySummary
```

`runtimeOutgoingRank_eq_outgoingSmithRank` connects the executable prefix
length to the theorem-facing rank. `runtimeKernelCoordinateMatrix_reindex`
identifies the executable restricted matrix with
`kernelCoordinateMatrix` after transport along that equality.
`runtimeHomologyInvariantFactors_eq_strong` states that the runtime factor
list is read directly from the second strong Smith result.

Run the native regression with:

```sh
lake build normalforms-homology-smoke
.lake/build/bin/normalforms-homology-smoke
```

It checks all represented degrees of the circle, torus, real projective
plane, and a finite cellular example with `H₁ ≅ ℤ × ℤ/6`.

## Finite normalized simplicial data

Version 1.2.1 adds an executable frontend whose indices enumerate only
nondegenerate simplices:

```lean
structure FiniteNormalizedSimplicialData where
  topDimension : Nat
  simplexCount : Nat → Nat
  finiteSupport : ∀ n, topDimension < n → simplexCount n = 0
  face :
    (n : Nat) →
      Fin (n + 2) →
        Fin (simplexCount (n + 1)) →
          Option (Fin (simplexCount n))
  boundary_squared : ...
```

`face n i σ = some τ` says the `i`th face of the nondegenerate
`(n+1)`-simplex `σ` is the nondegenerate `n`-simplex `τ`. `none` says that
the face is degenerate and vanishes in normalized chains.

`normalizedBoundaryMatrix` is derived, not supplied separately:

```text
boundary[n][τ,σ] =
  Σ i, if face n i σ = some τ then (-1)^i else 0.
```

Repeated faces remain separate summands, so opposite signs cancel.
`normalizedFaceTerm_eq_zero_of_degenerate` records the `none` elimination
rule. `boundary_mul_boundary` exposes the validated chain equation for the
derived matrices, and `toIntChainComplex` feeds them directly into the
v1.2.0 certified homology calculation.

`ofDimensionTwo` is a convenience constructor for vertices, edges, and
triangles. Its only nonempty chain obligation is the derived equation
`d₁d₂ = 0`; all later products have an empty column type.

Regression data covers:

- a one-vertex, one-edge simplicial circle whose repeated endpoint faces
  cancel;
- `Δ² / ∂Δ²`, whose three two-simplex faces are explicitly `none`;
- the standard filled triangle with exact oriented `d₁` and `d₂` matrices.

After conversion, the native executable checks their homology alongside the
v1.2.0 cellular examples, for 20 complete summaries in total.

## mathlib homology comparison

Version 1.2.2 realizes the explicit matrix data directly as mathlib's
homological-complex object:

```lean
IntChainComplex.toMathlibChainComplex :
  ChainComplex (ModuleCat Int) Nat
```

Its objects are the finite function modules `Fin (rank n) → Int`, and
`toMathlibChainComplex_d` identifies the degree-`n+1` differential with
`boundary n`. The chain law is proved from `boundary_squared`.

`mathlibDegreeShortComplex n` uses the same incoming and outgoing matrices as
the intrinsic quotient. At positive degrees it compares to mathlib's
canonical short complex by identity maps up to index equalities. At degree
zero the project has the unique map `C₀ → 0`, whereas mathlib's canonical
short complex uses the zero endomorphism `C₀ → C₀`.
`degreeShortComplexToSc` represents that difference explicitly and
`degreeHomologyIso` proves its induced homology map is an isomorphism.
Consequently:

```lean
IntChainComplex.mathlibHomologyEquiv
IntChainComplex.mathlibHomologyDecomposition
```

identify the intrinsic quotient with mathlib categorical homology and
transport the complete certified cyclic-plus-free decomposition.

## Normalized Moore comparison

`FiniteNormalizedSimplicialData` deliberately stores only the finite
nondegenerate face table and its normalized chain equation. Those data are
weaker than a complete simplicial set: they do not include degeneracy maps or
all simplicial identities. The API therefore does not make the unsound claim
that every such table canonically determines an `SSet`.

Instead, `NormalizedMooreComparison data` is a certified realization witness.
It supplies:

- a genuine mathlib `SSet`;
- equivalences between the finite indices and its nondegenerate simplices;
- degreewise linear basis equivalences;
- proofs that `some` faces agree and `none` faces are degenerate;
- agreement with the canonical normalized-chain generators; and
- commutation with the differentials.

From a witness the library constructs:

```lean
NormalizedMooreComparison.chainIso
NormalizedMooreComparison.karoubiNormalizedMooreIso
NormalizedMooreComparison.normalizedMooreChainIso
NormalizedMooreComparison.normalizedChainHomologyDecomposition
NormalizedMooreComparison.normalizedMooreHomologyDecomposition
```

The first is an actual chain isomorphism with mathlib's nondegenerate
normalized chain complex. The second composes mathlib's splitting and
normalized-Moore comparison in the Karoubi envelope. Full faithfulness then
reflects it to the ordinary chain-complex isomorphism in the third
declaration. The final two definitions transport the certified homology
decomposition to both mathlib models.

## Scope and trust

Version 1.2.2 completes the planned comparison with mathlib
`HomologicalComplex` and normalized Moore complexes. The normalized Moore
result is conditional on the explicit `NormalizedMooreComparison` witness;
constructing a genuine simplicial realization from weaker normalized data is
outside the interface and is not assumed.

Application theorems are checked by Lean's kernel. The quotient and basis
layers may use `Classical.choice`; the homology audit permits only
`propext`, `Quot.sound`, and `Classical.choice`. It rejects project axioms,
`sorryAx`, and native/compiler trust. Native success is a regression report,
not a proof.
