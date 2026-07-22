# Exact integer LLL artifact profile

This profile reproduces research version 0.1.0 of the independently imported
LLL development. It fixes row vectors, `delta = 3/4`, `eta = 1/2`, and exact
rational Gram--Schmidt semantics without enlarging the frozen `NormalForms`
facade.

The profile checks:

- a terminating full-row-rank kernel backed by the pinned
  `hex-lll-mathlib` revision;
- a transform accumulated from elementary row additions and swaps, together
  with its chosen inverse, both inverse identities, and `U * B = B'`;
- exact positivity, size-reduction, and Lovasz obligations;
- an HNF-based total wrapper for empty, zero, rectangular, and rank-deficient
  row inputs, with a reduced independent prefix and literal zero tail;
- a column entry implemented only by transposition;
- a profiled execution carrying the proved Hex fuel, exact event telemetry,
  an intermediate basis-and-multiplier height, and a profile-dependent
  sign-magnitude reference budget;
- a 114-entry facade manifest and 20-root JSON axiom audit;
- four deterministic native cases and five one-warmup,
  seven-measurement wall-time/RSS stages;
- an independent manuscript and pinned container recipe.

## Host reproduction

From the repository root:

```sh
scripts/verify.sh lll
```

The verifier retains deterministic execution and committed-baseline validation.
Reports are written beneath `build/verify/lll`. Fresh timing is an explicit
`scripts/bench.py lll` operation.

## Pinned container

Build and run the code, tests, audit, native corpus, and committed-baseline
checks:

```sh
docker build \
  --file artifact/lll/Dockerfile \
  --tag lean-normal-forms-lll:0.1.0 \
  .

docker run --rm lean-normal-forms-lll:0.1.0
```

The image pins the same Debian base, Lean 4.32.0 archive hash, and Lake
manifest as the core artifact. The verified dense backend is source-pinned in
`lake-manifest.json`; there is no FLINT dependency.

## Evidence and claim boundary

Semantic correctness, explicit inverse equations, total rank handling, the
tracked-event bound, result coefficient coverage, and the composed reference
budget are kernel-checked. Native time and RSS are observational regression
evidence and have no portable absolute threshold. The committed JSON and CSV
retain every raw observation plus source, binary, host, and hardware
fingerprints.

The bit theorem is deliberately profile-dependent: its common width is the
observed maximum of transformed basis entries and actual row-add multipliers.
It is not an input-only polynomial LLL theorem. It also excludes the HNF rank
decomposition used by `integerLLL`, transform-matrix multiplication costs,
Lean runtime allocation, and compiler behavior. Those exclusions prevent the
reference price from being mistaken for a native-time theorem.

The benchmark's small full-rank witnesses are discharged with `native_decide`
inside the executable only. They are observational test fixtures and are not
among the audited public theorem roots. No release, tag, DOI, deposition, or
upstream pull request is created by this profile.
