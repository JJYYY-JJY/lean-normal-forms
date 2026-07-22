# Kannan--Bachem normal-form artifact profile

This profile reproduces research version 0.1.0 of the independently imported
Kannan--Bachem development. It proves all four acceptance tiers for
nonsingular square integer HNF and SNF and does not change the frozen core
`NormalForms` facade.

The profile checks:

- the row-oriented transpose of the
  [Kannan--Bachem HNF schedule](https://doi.org/10.1137/0208040), with explicit
  forward and inverse transforms;
- the division-free, costed
  [Bird determinant](https://doi.org/10.1016/j.ipl.2011.08.006) used by row preparation;
- the row-oriented adaptation of Kannan--Bachem Smith Steps 4--7, including
  the repeated-pass and injection paths;
- total pivot stabilization by strict binary pivot decrease;
- lower-right Smith recursion returning the core `SNFResultFin` type;
- canonical equality with the core HNF/SNF implementations;
- exact ring/Euclidean operation telemetry and closed polynomial bounds;
- coefficient bounds for `S`, `U`, `U^-1`, `V`, and `V^-1`;
- a schoolbook bit-cost recurrence that charges every scalar primitive and
  all four matrix products in strong-certificate composition;
- a 572-declaration API freeze and 263-root axiom audit;
- three deterministic native cases and four one-warmup/seven-measurement
  wall-time/RSS stages with complete formal telemetry;
- the independent manuscript and local archival metadata.

## Host reproduction

From the repository root:

```sh
scripts/verify.sh kannan-bachem
```

The verifier retains deterministic native execution and committed-baseline
validation. Reports are written beneath `build/verify/kannan-bachem`. Fresh
timing is an explicit `scripts/bench.py kannan-bachem` operation.

## Pinned container

Build and run the code, tests, audit, native cases, and committed-baseline
checks:

```sh
docker build \
  --file artifact/kannan-bachem/Dockerfile \
  --tag lean-normal-forms-kannan-bachem:0.1.0 \
  .

docker run --rm lean-normal-forms-kannan-bachem:0.1.0
```

The image pins the same Debian base, Lean 4.32.0 archive hash, and Lake
manifest as the core artifact. It contains no FLINT dependency.

## Evidence and scope

Correctness and complexity are kernel-checked Lean theorems. The native
benchmark is observational regression evidence only; its absolute timing is
never a portable pass/fail threshold. The committed baseline stores source,
binary, host, and hardware fingerprints alongside exact deterministic
operation counts, coefficient widths, and modeled costs. On its captured
host, prepared HNF, repeated-pass SNF, injection SNF, and the complete corpus
have median wall times 4.20, 0.06, 2.25, and 6.38 seconds respectively.

Research version 0.1.0 is deliberately scoped to nonsingular square integer
matrices. It does not claim a rectangular or rank-deficient Kannan--Bachem
wrapper. Such inputs remain covered by the stable core normal-form algorithm.
No release, tag, DOI, deposition, or upstream pull request is created by this
profile.
