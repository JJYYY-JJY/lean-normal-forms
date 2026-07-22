# Benchmark evidence

`benchmarks/baselines/` contains the committed JSON and CSV observations.
The code verifier checks the exact file set, schemas, measurement policy,
case and stage identities, and deterministic result fields. It does not use
wall time or memory as portable pass/fail thresholds.

## Run a profile

Use the single benchmark entry point:

```sh
scripts/bench.py PROFILE
```

Fresh runs write to `build/benchmarks/` by default, so a local measurement
cannot overwrite committed history. Every profile accepts `--warmups`,
`--measurements`, `--skip-build`, and `--output-prefix`.

Available profiles:

| Profile | Executed evidence |
| --- | --- |
| `certificate-paths` | Internal Lean, optional FLINT CLI and FFI generation, pure checking, strict kernel import, and both end-to-end paths |
| `rational-canonical` | Invariant generation, companion verification, and the complete rational-canonical path |
| `bit-cost` | Thirteen deterministic binary arithmetic cases and native process cost |
| `kannan-bachem` | Prepared HNF, repeated-pass SNF, Step-7 injection, and the full corpus |
| `modular-hnf` | Scalar, rectangular, square, and full-corpus modular-HNF modes |
| `lll` | Gaussian, dense, rank-deficient, column-adapter, and full-corpus modes |

The certificate profile needs the pinned optional adapter. Build it before a
fresh run:

```sh
NORMALFORMS_FLINT_BUILD_LEAN_FFI=1 scripts/BuildFlintAdapter.sh
scripts/bench.py certificate-paths --skip-build
```

Pass an explicit baseline path only when creating reviewed evidence for a
new profile or release:

```sh
scripts/bench.py lll \
  --output-prefix benchmarks/baselines/research-lll-v0.1.0
```

Inspect the JSON and CSV diff before committing it. Routine verification
reads committed baselines and never rewrites them.

## Protocol and interpretation

The default protocol uses one warmup and seven measurements. JSON reports
retain raw observations, median, inclusive-quartile IQR, source and binary
fingerprints, and the relevant hardware description. CSV reports keep the
same raw measurement series for analysis.

Each runner validates its fixed case corpus before and during measurement.
Profile-specific parsers check normal-form results, operation telemetry,
coefficient widths, modeled costs, and theorem bounds where those fields
exist. A drift in deterministic output fails the run.

Native time and RSS are observational evidence. HNF/SNF correctness,
transformation equations, inverse identities, and complexity claims come
from the cited kernel-checked declarations, not from these measurements or
from differential tests.

## Committed baselines

The verifier retains these distinct historical roles:

- `v0.2.2-native-polynomial`: deterministic polynomial certificate corpus;
- `v0.3.1-certificate-paths` and `v1.0.0-certificate-paths`: seven-stage
  certificate profiles;
- `v1.0.0-module-profile`: deterministic Lean allocation profile;
- `v1.1.0-rational-canonical`: three-stage rational-canonical profile;
- `research-bit-cost-v0.1.0`: thirteen-case primitive cost profile;
- `research-kannan-bachem-v0.1.0`: four-stage HNF/SNF profile;
- `research-modular-hnf-v0.1.0`: four-stage modular-HNF profile;
- `research-lll-v0.1.0`: five-stage exact-integer LLL profile.

`scripts/verify.sh core` regenerates the module-allocation report in an
ignored report directory and compares it with the committed policy. The
complete code-only verifier validates every committed baseline before it
runs profile-specific checks.
