# Artifact profiles

This directory contains the frozen core profile and independently versioned
application/research profiles.

Current 1.2.2 baseline (stable 1.0 core plus independently imported rational
canonical and finite-free integer homology applications):

- Lean/mathlib 4.32.0;
- explicit finite indexings and permutation transport;
- strong HNF/SNF results with chosen inverses and both inverse identities;
- reversible operation logs with four accumulators;
- fixed-index HNF uniqueness and indexing-independent canonical `Fin` SNF;
- constructive `ComputableEuclideanOps` implementations for `Int` and
  `Polynomial Rat`;
- constructive finite matrix and rational algebra plus direct
  rational-polynomial finite-support arithmetic, long division,
  normalization, and extended gcd;
- pivot-measure SNF termination without UFD factorization;
- exact-output `#eval`, native certificate, and constructive-source audit
  baselines;
- pure `normalforms.cert/v1` parsing, checking, and soundness with exact
  caller-input binding;
- strict, separately reduced `decide_cbv` certificate modules and independent
  executable-core and certificate no-choice/no-native-trust axiom audits;
- an optional pinned FLINT/GMP/MPFR CLI generator, dynamically linked worker,
  source/license bundle, and end-to-end mutation corpus;
- a separately linked Lean FFI reusing the exact C decimal-protocol
  implementation and returning only untrusted raw data;
- fixed-seed internal/FFI and CLI/FFI normalized-invariant-factor
  regressions, with nonunique transforms intentionally ignored;
- separated internal, CLI, FFI, kernel/native checker, and end-to-end
  certificate-path benchmarks with raw JSON/CSV;
- intrinsic `SmithData` and `SmithSignature` with complete diagonals, unit
  factors, zero tails, and derived kernel/cokernel ranks;
- determinantal-ideal characterization, transform/reindex invariance, and
  recovery of rank and associate factors;
- canonical mathlib PID comparisons at associates, normalized, and sorted
  `Int.natAbs` levels;
- column-oriented finite-free presentations with cokernels, Fitting ideals,
  Smith decomposition, and mathlib `Module.Presentation`;
- an independent generic mathlib patch under `patches/mathlib`, prepared but
  not applied or submitted;
- the `Int` presentation specialization and existing abelian-group examples;
- `lake build`, `lake test`, public facade checks, and JSON axiom audit.

The exact facade, schema, indexing/result types, presentation direction,
paper, and reproducibility gate are frozen by the 1.0 profile.

The v1.1 rational-canonical profile adds executable `XI - A`, the
`Matrix.charmatrix` bridge, strong polynomial Smith factors,
`Module.AEval'` decomposition, characteristic/minimal-polynomial theorems,
explicit companion-block similarity, basis independence, a native Rat
benchmark, and its own paper and audit. It is reproduced through
`artifact/rational-canonical` and does not enlarge the core facade.

The v1.2 homology profile adds explicit finite-free integer chain
complexes, certified Smith kernel coordinates, an intrinsic homology quotient
and cyclic/free decomposition, a theorem-connected executable projection,
finite normalized simplicial face tables and derived boundaries, and a
20-case native regression. It also identifies the matrix complex with
mathlib categorical homology and transports the result to normalized chains
and normalized Moore complexes through a certified realization. It is
reproduced through
`artifact/homology`, has its own paper and audit, and does not enlarge the
core facade.

The independent `research/bit-cost` 0.1.0 profile adds canonical binary
sign-magnitude words, costed carry/borrow addition, schoolbook
multiplication, a shared signed Euclidean long-division pass, and a costed
extended-gcd loop. Kernel theorems prove exact integer semantics,
coefficient-width control, and explicit bit-operation budgets. It is
reproduced through `artifact/bit-cost`, has its own paper, audit, native
corpus, benchmark, and release gate, and does not enlarge the core facade or
claim matrix-algorithm complexity.

The independent `research/kannan-bachem` 0.1.0 profile closes semantic,
ring-operation, coefficient-width, and schoolbook bit-complexity tiers for
nonsingular square integer HNF and SNF. It includes deterministic prepared-HNF,
repeated-pass, and Step-7-injection cases, an exact audit and API freeze, raw
benchmark evidence, a manuscript, and a pinned container. It is reproduced
through `artifact/kannan-bachem` and remains outside the stable core facade.

The independent `research/modular-hnf` 0.1.0 profile supplies a typed
determinant-modulus DKT value kernel, proves its legal candidate equals the
canonical core HNF, and lifts it to all rectangular and rank-deficient integer
matrices through a checked fraction-free rank profile. It closes scalar
operation, intermediate/final coefficient, and schoolbook value-kernel bit
bounds, including an exact mirror of Lean's standard integer XGCD path. Its
157-entry API freeze, 43-root audit, native corpus, raw benchmark, manuscript,
and pinned container are reproduced through `artifact/modular-hnf`. It remains
outside the stable core facade; transform construction cost is not part of its
value-kernel complexity claim.

The independent `research/lll` 0.1.0 profile fixes exact row-basis LLL at
`delta = 3/4` and `eta = 1/2`. It pairs the source-pinned terminating reducer
with an explicit-inverse elementary trace, extends it to every row rank through
a verified HNF decomposition, and exposes columns only through transposition.
Its profile records exact events, verified fuel, intermediate coefficient
evidence, and an a-posteriori schoolbook reference budget. The 114-entry API
freeze, 20-root audit, four-case native corpus, five-stage raw benchmark,
manuscript, and pinned container are reproduced through `artifact/lll`. It
remains outside the stable core facade and does not claim an input-only
polynomial LLL complexity theorem.

Run the F2 execution profile with:

```sh
scripts/ExecutionAudit.sh
scripts/CertificateImportTest.sh
lake env lean scripts/CoreAxiomAudit.lean
lake env lean scripts/CertificateAxiomAudit.lean
scripts/ProfileLeanModules.py
```

The optional external-generator profile additionally runs:

```sh
scripts/BuildFlintAdapter.sh
scripts/FlintAdapterTest.sh
scripts/FlintFFITest.sh
scripts/bench.py certificate-paths --skip-build
```

`scripts/BundleFlintSources.sh DESTINATION` prepares exact upstream sources,
license texts, adapter sources, build configuration, and relink instructions.

The fixed-host native polynomial corpus baseline uses one warmup and seven
measurements. Its median is 4.66 seconds wall time and 72,056 KiB maximum RSS;
the raw observations, IQR, and hardware fingerprint are in
`benchmarks/baselines/v0.2.2-native-polynomial.{json,csv}`. It is an
observational baseline, not a hosted-CI pass/fail threshold.

The fixed-host v1.0.0 integer certificate-path profile uses one warmup and
seven measurements per stage. It records a 0.10 s internal Lean median,
0.03/0.06 s CLI/FFI generation medians, 0.02 s native-checker median, and
7.04 s strict-kernel median on the captured hardware. Its complete observations
and fingerprint are in
`benchmarks/baselines/v1.0.0-certificate-paths.{json,csv}`. Operation,
pivot, and gcd counts remain explicit nulls until truthful instrumentation
exists.

The fixed-host v1.1.0 rational-canonical profile uses one warmup and seven
measurements over a 2-by-2 rational Jordan block. It records factor degrees
`[0, 2]`, coefficient growth from 2 to 3 bits, 0.07 s median invariant
generation, and a 0.617 s isolated median for 1,000 companion checks. Complete
observations and fingerprints are in
`benchmarks/baselines/v1.1.0-rational-canonical.{json,csv}`.

The fixed-host `research/bit-cost` 0.1.0 profile uses one warmup and seven
measurements of a deterministic 13-case binary primitive corpus. The
committed run records a 23.3 ms median wall time and 69,620 KiB median maximum
RSS. The same report stores every modeled cost and proved budget, but native
timing remains observational. Complete raw data and source/binary/hardware
fingerprints are in
`benchmarks/baselines/research-bit-cost-v0.1.0.{json,csv}`.

The fixed-host `research/kannan-bachem` 0.1.0 profile measures prepared HNF,
two branch-sensitive SNF cases, and their end-to-end corpus after one warmup
and across seven observations per stage. Its deterministic fields include
operation counts, XGCD and pivot-path counts, certificate widths, exact modeled
cost, and the formal bound. Complete raw values and fingerprints are in
`benchmarks/baselines/research-kannan-bachem-v0.1.0.{json,csv}`.
The recorded median wall times are 4.20 s for prepared HNF, 0.06 s for the
repeat path, 2.25 s for the injection path, and 6.38 s end to end.

The fixed-host `research/modular-hnf` 0.1.0 profile measures scalar, tall, and
square determinant-modulus cases plus their end-to-end corpus after one
warmup and across seven observations per stage. Every stage records exact
operation telemetry, coefficient widths, modeled bit cost, and its formal
bound. All four recorded median wall times are 0.02 s. Complete raw values and
fingerprints are in
`benchmarks/baselines/research-modular-hnf-v0.1.0.{json,csv}`.

The fixed-host `research/lll` 0.1.0 profile measures Gaussian and dense
full-rank traces, a dependent-row total wrapper, the transpose column adapter,
and the complete corpus after one warmup and across seven observations per
stage. The captured median wall times are 0.02 s, 0.20 s, 0.06 s, 0.06 s, and
0.27 s respectively. Complete raw telemetry, formal profile bounds, and
fingerprints are in
`benchmarks/baselines/research-lll-v0.1.0.{json,csv}`.

The artifact family is split into independently reproducible profiles:

- core;
- rational canonical form;
- homology;
- Kannan--Bachem (`artifact/kannan-bachem`, research version 0.1.0);
- modular HNF (`artifact/modular-hnf`, research version 0.1.0);
- LLL (`artifact/lll`, research version 0.1.0);
- bit cost (`artifact/bit-cost`, research version 0.1.0).

FLINT remains an untrusted optional generator. The core Lean library and pure
checker must build and test without linking it.
