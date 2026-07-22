# Binary bit-cost reference artifact profile

This profile reproduces research version 0.1.0 of the independently imported
binary integer cost model. It does not change or re-export the frozen core
`NormalForms` facade, and it does not claim an HNF or SNF complexity theorem.

The profile checks:

- the explicit four-tier complexity vocabulary;
- canonical binary sign-magnitude encoding through mathlib's `ZNum`;
- exact mirrored counters for addition carry/borrow propagation;
- schoolbook shift-and-add multiplication;
- one shared signed Euclidean long-division pass;
- quotient, remainder, output-width, and strict remainder-decrease theorems;
- a well-founded extended Euclidean loop with normalized gcd and Bézout
  witnesses;
- path-sensitive coefficient-width and composed bit-operation budgets;
- a 49-declaration facade freeze and exact core-facade isolation diagnostic;
- a 21-root axiom audit;
- a deterministic 13-case native corpus;
- one warmup and seven raw JSON/CSV wall-time/RSS measurements with source,
  binary, hardware, and platform fingerprints.

## Host reproduction

From the repository root:

```sh
scripts/verify.sh bit-cost
```

Reports are written under `build/verify/bit-cost`. Fresh timing is an explicit
`scripts/bench.py bit-cost` operation.

## Pinned container

Build and run the code, tests, audit, native corpus, and committed-baseline
checks:

```sh
docker build \
  --file artifact/bit-cost/Dockerfile \
  --tag lean-normal-forms-bit-cost:0.1.0 \
  .

docker run --rm lean-normal-forms-bit-cost:0.1.0
```

The image pins the same Debian base, Lean 4.32.0 archive hash, and Lake
manifest as the core artifact. It contains no FLINT dependency.

## Evidence and trust boundary

Correctness comes from Lean's kernel checking the value, bit-length,
termination, and cost-bound theorems. The returned `.cost` is an exact count
for this reference implementation, while each public `*Bound` definition is
an independently proved upper budget.

The proof audit admits `Classical.choice`, `Quot.sound`, and `propext` because
the semantic bridge reuses mathlib's `ZNum` and `Nat.size` theorems. The
executable definitions remain constructive. Project axioms, `sorryAx`, and
native/compiler trust are forbidden.

Native wall time and RSS describe this host run; they are not formal
complexity evidence or portable pass/fail thresholds. The formal scope ends
at integer primitives and extended gcd. Later normal-form algorithms must
separately prove how often they call these primitives and how their
coefficients grow.
