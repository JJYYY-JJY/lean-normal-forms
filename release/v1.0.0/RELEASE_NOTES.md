# lean-normal-forms 1.0.0

Version 1.0.0 freezes the certified executable HNF/SNF core on Lean and
mathlib 4.32.0. It is the stable base for later rational-canonical, homology,
and independent algorithm-research profiles.

## Frozen interfaces

- `normalforms.cert/v1`, including canonical integer spelling, matrix layout,
  caller-supplied expected input, error categories, and checker soundness;
- explicit `Fin`, caller-indexed, caller-equivalence, ordered, and
  noncomputable arbitrary-index entry points;
- chosen inverse matrices and both inverse identities in all strong results;
- intrinsic `SmithData`, `SmithSignature`, and determinantal-ideal recovery;
- columns-as-relations `FiniteFreePresentation`, representing
  `R^relations → R^generators`.

`NormalForms/Tests/CoreFreeze.lean` pins constructors and exact types.
`docs/PUBLIC_API.md` records the stable facade. No compatibility wrappers are
provided for the former equation-only result names, optional entry points, or
hidden-index predicates.

## Trusted computation

The integer and rational-polynomial `Fin` kernels execute through
`ComputableEuclideanOps`, construct inverse certificates directly, and do not
recover them through determinants or matrix inversion. The strict executable
and generated-certificate axiom audits admit only `propext` and `Quot.sound`;
they reject `Classical.choice`, project axioms, `sorryAx`, and compiler/native
trust. Arbitrary finite-index convenience wrappers remain a separately
reported classical layer.

The optional FLINT CLI and FFI are untrusted certificate generators. Both use
one C computation and decimal protocol, and both feed the same pure Lean
checker. Only a generated module recompiled by Lean constructs a theorem.

## Reproducibility

- Lean 4.32.0 and mathlib's exact resolved revision are pinned.
- `artifact/core/Dockerfile` pins the container base, Dockerfile frontend, and
  Lean archive checksum.
- `scripts/verify.sh core` rebuilds code, tests, execution baselines,
  axiom reports, strict imports, the module profile, committed benchmark
  evidence, and the mathlib patch. Publication checks remain separate.
- The module profiler fails deterministic allocation growth above twice the
  committed baseline and reports wall growth above three times as a warning.
- `scripts/BuildReleaseArchive.sh --with-flint-sources` prepares a local
  source/paper/metadata archive, corresponding FLINT/GMP/MPFR sources and
  licenses, build information, and verified SHA256 sums.
- Raw benchmark JSON/CSV remains authoritative; wall-clock comparisons require
  an identical hardware fingerprint.

## Deliberate boundaries

- The core facade does not import examples, recursive pivot state, reversible
  replay implementation, FFI, native-trust code, or research backends.
- The official external adapter platform is Linux x86_64 glibc; the core Lean
  library remains portable.
- Rational canonical form, integer homology, Kannan--Bachem, modular HNF, LLL,
  and bit-cost formalization are post-1.0 profiles and do not alter this
  release claim.
- These materials are prepared locally. No GitHub release, tag, DOI/Zenodo
  deposition, or upstream pull request is created by the release scripts.

## Verification

Run:

```sh
scripts/verify.sh core
scripts/verify.sh flint
scripts/BuildReleaseArchive.sh --with-flint-sources
```

The second command is optional and requires the supported FLINT adapter
platform. The archive command requires a clean committed tree.
