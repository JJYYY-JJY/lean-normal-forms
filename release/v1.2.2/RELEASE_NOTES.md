# lean-normal-forms 1.2.2

Version 1.2.2 completes the independently imported finite-free integer
homology line by connecting its explicit matrix construction to mathlib
categorical homology and normalized Moore complexes. The frozen v1.0
HNF/SNF core, v1.1 rational-canonical facade, and v1.2.0/v1.2.1 data
interfaces remain compatible.

## Homological-complex comparison

- `IntChainComplex.toMathlibChainComplex` realizes every explicit complex as
  `ChainComplex (ModuleCat Int) Nat`.
- `toMathlibChainComplex_d` identifies its differential exactly with the
  stored boundary matrix.
- `degreeShortComplexToSc` handles the degree-zero difference between the
  project's outgoing map `C₀ → 0` and mathlib's canonical zero endomorphism
  `C₀ → C₀`.
- `degreeHomologyIso` proves the induced categorical homology map is an
  isomorphism.
- `mathlibHomologyEquiv` identifies the intrinsic quotient with mathlib
  homology, and `mathlibHomologyDecomposition` transports the complete
  cyclic-plus-free decomposition.

## Normalized Moore comparison

- `NormalizedMooreComparison` records a genuine mathlib simplicial set,
  equivalences with its nondegenerate simplices, degreewise bases, exact
  `some`-face semantics, degenerate `none` faces, canonical generators, and
  differential commutation.
- `chainIso` identifies the explicit matrix complex with mathlib's
  nondegenerate normalized chain complex.
- `karoubiNormalizedMooreIso` composes the canonical splitting with
  mathlib's normalized-Moore comparison.
- `normalizedMooreChainIso` reflects that isomorphism back from the Karoubi
  envelope to ordinary chain complexes.
- Both normalized models receive the certified homology decomposition.

The realization witness is deliberate: the v1.2.1 normalized face table and
`d² = 0` proof do not contain all simplicial identities or degeneracy maps,
so the library does not claim to synthesize a genuine simplicial set from
weaker data.

## Reproducibility and trust

- The independent homology API freeze checks 53 declarations.
- The homology audit covers 37 roots and observes only `propext`,
  `Quot.sound`, and `Classical.choice`.
- The native profile remains 20 complete deterministic summaries; the new
  categorical layer is verified through compile-time isomorphism and
  bijectivity regressions.
- `scripts/verify.sh homology` reproduces the code, API, axiom, native, and
  committed-evidence checks. Publication files remain separate.

Native success is observational evidence. Lean's kernel checks the matrix
complex, quotient comparison, chain isomorphisms, and transported
decompositions.

## Release boundary

These files prepare local release notes, source/paper archives, Zenodo
metadata, and checksums. They do not create a GitHub release, tag, DOI,
deposition, or upstream pull request.
