# Core artifact profile

This profile rebuilds the stable core without FLINT and without trusting
generated native code for certificate theorems.

The container pins:

- Debian 13.1 slim by OCI digest;
- Lean 4.32.0's official Linux release archive by SHA256;
- mathlib and every transitive Lake dependency through `lake-manifest.json`.

Build from the repository root:

```sh
docker build \
  --file artifact/core/Dockerfile \
  --tag lean-normal-forms-core:1.0.0 \
  .
```

The image build downloads the mathlib cache and runs the code-only core
verifier. It compiles the facade and exact type freeze, runs all deterministic
tests and executable baselines, emits both restricted axiom reports plus the
facade-wide report, recompiles generated strict certificate modules, validates
committed benchmark evidence, and checks the standalone mathlib patch.

Run the same verifier on the host with:

```sh
scripts/verify.sh core
```

Run `scripts/verify.sh flint` separately when the pinned optional Linux x86_64
adapter is available. The core library, pure checker, and strict theorem path
do not link FLINT.
