# Modular-HNF artifact profile

This profile reproduces research version 0.1.0 of the independently imported
modular Hermite-normal-form development. It formalizes a determinant-modulus
value kernel in the algorithm class of
[Domich--Kannan--Trotter](https://doi.org/10.1287/moor.12.1.50), proves its candidate
is the project's canonical HNF, and does not enlarge the frozen `NormalForms`
facade.

The profile checks:

- separate determinant-modulus and elementary-divisor contracts, with no
  undocumented assumption hidden in the executable entry point;
- a pure full-column-rank modular kernel with observable stage events and
  exact operation-category telemetry;
- equality of the legal-modulus candidate with `hermiteNormalFormFin`;
- the existing `HNFResultFin` strong interface, including an explicit inverse
  and both inverse identities;
- a checked fraction-free rank profile and a total rectangular/rank-deficient
  wrapper whose runtime search uses only finite integer data;
- a closed scalar-operation bound and explicit intermediate/final coefficient
  bounds;
- an exact cost mirror of Lean's actual `Int.gcdA`/`Int.gcdB` path and a
  conservative schoolbook bit-operation budget for the complete value kernel;
- a 157-entry facade manifest and 43-root JSON axiom audit;
- scalar, tall, and square deterministic native cases plus four one-warmup,
  seven-measurement wall-time/RSS stages;
- an independent manuscript and pinned container recipe.

## Host reproduction

From the repository root:

```sh
scripts/verify.sh modular-hnf
```

The verifier retains deterministic execution and committed-baseline validation.
Reports are written beneath `build/verify/modular-hnf`. Fresh timing is an
explicit `scripts/bench.py modular-hnf` operation.

## Pinned container

Build and run the code, tests, audit, native corpus, and committed-baseline
checks:

```sh
docker build \
  --file artifact/modular-hnf/Dockerfile \
  --tag lean-normal-forms-modular-hnf:0.1.0 \
  .

docker run --rm lean-normal-forms-modular-hnf:0.1.0
```

The image pins the same Debian base, Lean 4.32.0 archive hash, and Lake
manifest as the core artifact. It has no FLINT dependency. The pinned
[FLINT 3.6.0 documentation](https://github.com/flintlib/flint/blob/8d5454b96761fafe4d5a9da76a369a602f500f49/doc/source/fmpz_mat.rst#L1295-L1314)
was consulted only to distinguish its two unchecked modular-HNF contracts.

## Evidence, cost scope, and trust

Correctness, canonical equality, operation bounds, coefficient bounds, and the
priced telemetry theorem are kernel-checked. Native time and RSS are only
observational regression evidence and have no portable absolute threshold.
The committed baseline contains raw observations plus source, binary, host,
and hardware fingerprints. On the captured host, all four stages have a 0.02
second median; full raw values and IQRs remain in the JSON/CSV baseline.

The bit theorem covers the modular value kernel. The strong result reuses the
stable core transform only after proving that the independently computed
candidate equals the canonical HNF. Consequently this profile does not claim
that its bit-operation count includes construction of `U` or `U⁻¹`.

The automatic general-rank wrapper uses an exhaustive verified finite search;
its completeness proof may use erased rational linear algebra. The benchmark
targets the determinant-modulus value kernel, not the potentially expensive
rank-profile search. No release, tag, DOI, deposition, or upstream pull request
is created by this profile.
