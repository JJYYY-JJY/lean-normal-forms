# lean-normal-forms

`lean-normal-forms` provides certified Hermite and Smith normal forms in
Lean 4. Version 1.2.2 targets Euclidean domains, exposes finite-index
semantics in its types, and returns explicit transformation matrices with
chosen inverses. The repository pins Lean and mathlib 4.32.0.

## Verified capabilities

- HNF and SNF for zero-dimensional, rectangular, rank-deficient, and square
  matrices;
- transformation equations plus both left and right inverse identities;
- direct `Fin`, caller-supplied equivalence, ordered-index, and arbitrary
  finite-index entry points;
- constructive execution over `Int` and `Polynomial Rat`;
- canonical Smith data, determinantal ideals, finite-free presentations, and
  the mathlib PID bridge;
- a pure `normalforms.cert/v1` JSON parser and checker, with Lean source
  emission for kernel re-import;
- separate rational-canonical and finite-free integer homology applications;
- separate bit-cost, Kannan--Bachem, modular-HNF, and exact
  integer LLL research profiles.

The optional FLINT adapter generates certificate data through a process or
Lean FFI path. Neither path enters the default build, test suite, or trusted
core.

## Install and build

Install Lean through `elan`; the checked-in `lean-toolchain` selects the
required compiler. Fetch the mathlib cache and build the default library:

```sh
lake exe cache get
lake build
```

The repository uses Lake, Bash, and the Python standard library. Lint and
benchmark commands also require `rg` and GNU `/usr/bin/time`.

## Minimal example

```lean
import NormalForms

open scoped Matrix
open NormalForms.Matrix.Hermite NormalForms.Matrix.Smith

def input : Matrix (Fin 2) (Fin 3) Int :=
  !![6, 15, 9;
     4, 10, 6]

#eval ((hermiteNormalFormFin input).H, (smithNormalFormFin input).S)
```

Lean prints:

```text
(!![2, 5, 3; 0, 0, 0], !![1, 0, 0; 0, 0, 0])
```

Each result also contains its transform, explicit inverse certificate,
transformation equation, and normal-form proof.

## Public facade

Import `NormalForms` for the frozen core surface. The main executable layers
are:

```lean
hermiteNormalFormFin
hermiteNormalFormWithIndexing
hermiteNormalFormWithEquiv
hermiteNormalFormOrdered
hermiteNormalForm

smithNormalFormFin
smithNormalFormWithIndexing
smithNormalFormWithEquiv
smithNormalFormOrdered
smithNormalForm
```

`FiniteIndexing` and `MatrixIndexing` make row and column enumeration
explicit. `HNFResultFin` and `SNFResultFin` carry strong certificates with
chosen inverses. A finite-free presentation uses an `m`-by-`n` relation
matrix as the map `R^n -> R^m`, so columns are relations.

Applications and research profiles use their own imports and do not enlarge
the core facade:

```lean
import NormalForms.Applications.RationalCanonical
import NormalForms.Applications.Homology
import NormalForms.Research.BitCost
import NormalForms.Research.KannanBachem
import NormalForms.Research.ModularHNF
import NormalForms.Research.LLL
```

See [the public API reference](docs/PUBLIC_API.md) for declarations and
conventions. The exact constructor and argument-order freeze lives in
`NormalForms/Tests/CoreFreeze.lean`. The wire format is specified in
[the certificate schema](docs/CERTIFICATE_SCHEMA_V1.md).

## Test and verify

Daily software maintenance has five authoritative entry points:

```sh
lake build
lake test
lake lint
scripts/verify.sh all
scripts/bench.py PROFILE
```

`lake test` compiles every deterministic non-optional positive test and the
exact-diagnostic negative facade-isolation corpus. `lake lint` checks trust
markers, facade imports, whitespace, and import hygiene without editing
files.

`scripts/verify.sh` accepts `core`, `rational-canonical`, `homology`,
`bit-cost`, `kannan-bachem`, `modular-hnf`, `lll`, `flint`, or `all`. The
`all` profile runs code-only API freezes, axiom audits, deterministic native
cases, certificate emission and kernel import, baseline validation, and the
standalone mathlib patch check. It runs FLINT checks when the pinned adapter
is present. An explicit `flint` profile fails with build instructions when
the adapter is absent.

`scripts/bench.py` accepts `certificate-paths`, `rational-canonical`,
`bit-cost`, `kannan-bachem`, `modular-hnf`, or `lll`. Fresh observations go
to ignored `build/benchmarks/` files unless you pass an output prefix. See
[the benchmark evidence guide](benchmarks/README.md).

No default software command builds publication material.

## Trust boundary

Lean's kernel checks the normal-form theorems, certificate soundness, and
explicit inverse identities. The operational certificate path uses
`decide_cbv`; strict source and axiom audits reject `sorryAx`, project axioms,
and compiler or native trust.

The strict executable core and strict certificate tier allow `propext` and
`Quot.sound`. The arbitrary finite-index facade and separate audited
semantic application or research layers may also use `Classical.choice`.
Each tier keeps its own declaration roots and allowlist.

FLINT remains an untrusted optional generator. Lean checks the caller-owned
input, transformation equations, inverse equations, and normal-form
predicates before constructing a theorem. Native runs, benchmark timing, and
differential tests provide regression evidence rather than proofs.

## Software documentation

- [Public API](docs/PUBLIC_API.md)
- [Certificate schema v1](docs/CERTIFICATE_SCHEMA_V1.md)
- [Rational-canonical API](docs/RATIONAL_CANONICAL_API.md)
- [Homology API](docs/HOMOLOGY_API.md)
- [Bit-cost API](docs/BIT_COST_API.md)
- [Kannan--Bachem API](docs/KANNAN_BACHEM_API.md)
- [Modular-HNF API](docs/MODULAR_HNF_API.md)
- [LLL API](docs/LLL_API.md)
- [Optional FLINT adapter](adapters/flint/README.md)
- [Artifact profiles](artifact/README.md)
- [Changelog](CHANGELOG.md)
- [Current maintenance boundary](PLAN.md)

## License and citation

The project is available under the [Apache License 2.0](LICENSE). Use the
repository's [citation metadata](CITATION.cff) when citing the software.
