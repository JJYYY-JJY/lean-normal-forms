# Kannan--Bachem 0.2.0-dev artifact profile

This profile verifies the value-producing, leaf-instrumented HNF/SNF
execution for nonsingular square integer matrices.

```sh
scripts/verify.sh kannan-bachem
```

The v2 benchmark reports deterministic arithmetic fields from the same
execution charge list. Wall time, RSS, and the rebuilt binary hash are
environment fingerprints, not portable gates.

The source identity is the SHA-256 of the sorted files selected by
`source-manifest.txt`. Each path and content is framed by an unsigned
eight-byte big-endian byte length before hashing. Generated baselines,
reports, build output, and `.git` are excluded.

The baseline's `source.git_revision` records the clean source commit used to
generate it. The baseline-only commit therefore naturally has a later
revision.

```sh
docker build --no-cache \
  --file artifact/kannan-bachem/Dockerfile \
  --tag lean-normal-forms-kannan-bachem:0.2.0-dev .
docker run --rm lean-normal-forms-kannan-bachem:0.2.0-dev
```

The historical 0.1.0 release directory and baselines are unchanged.
