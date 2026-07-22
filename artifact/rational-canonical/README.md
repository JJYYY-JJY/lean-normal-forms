# Rational canonical artifact profile

This profile reproduces the independent v1.1.0 rational-canonical
application on top of the frozen v1.0 HNF/SNF core. It does not change or
re-export the core `NormalForms` facade.

The profile checks:

- executable `XI - A` and its equality with mathlib `Matrix.charmatrix`;
- the strong polynomial Smith result and complete normalized factor list;
- the `Module.AEval'` cyclic decomposition;
- characteristic- and minimal-polynomial identities;
- executable companion matrices;
- the explicit basis change and both inverse identities;
- exact block-diagonal similarity;
- similarity invariance and basis independence;
- zero-dimensional, scalar, diagonal, Jordan, and coordinate-swap cases;
- the independent API freeze and axiom audit;
- the native Rat benchmark and committed raw JSON/CSV baseline.

## Host reproduction

From the repository root:

```sh
scripts/verify.sh rational-canonical
```

The verifier runs deterministic native execution, the application axiom audit,
and committed-baseline checks. It writes reports under
`build/verify/rational-canonical`. Fresh timing is an explicit
`scripts/bench.py rational-canonical` operation; absolute wall time is not a
portable pass/fail condition.

## Pinned container

Build and run the code, tests, audit, and benchmark without TeX:

```sh
docker build \
  --file artifact/rational-canonical/Dockerfile \
  --tag lean-normal-forms-rational-canonical:1.1.0 \
  .

docker run --rm lean-normal-forms-rational-canonical:1.1.0
```

The image pins the same Debian base, Lean archive hash, and Lake manifest as
the core artifact. It contains no FLINT dependency: the rational-canonical
profile uses the internal certified polynomial Smith kernel.

## Evidence and trust boundary

The raw baseline is
`benchmarks/baselines/v1.1.0-rational-canonical.{json,csv}`. It records the
source revision, full host fingerprint, degree list, rational coefficient
growth, wall time, RSS, and isolated companion-check timing.

Native success is a run report. Correctness comes from the kernel-checked
Smith, cyclic-decomposition, companion, minimal-polynomial, and similarity
theorems. The semantic application layer admits `Classical.choice` in
addition to `propext` and `Quot.sound`; compiler/native trust and
project-defined axioms remain forbidden.
