# FLINT certificate generator adapter

This directory is an optional, untrusted certificate generator. It is not
imported by the `NormalForms` facade, linked into the core Lean library, or
used as a premise of any theorem. A generated JSON file becomes meaningful
only after the pure Lean checker accepts it; the strict import path additionally
recompiles the generated module with Lean's kernel.

The supported v0.3 platform is Linux x86_64 with glibc. Versions are fixed to:

- FLINT 3.6.0;
- GMP 6.3.0;
- MPFR 4.2.2.

The HTTPS source URLs and SHA256 values live in `versions.env` and
`SOURCES.sha256`. The pinned-base build container starts from the Linux/amd64
manifest of `debian:13.1-slim`, fixed by digest in `container/Dockerfile`; its
Dockerfile frontend is fixed by digest as well. Remote `ADD --checksum` layers
cache each verified source archive independently, and the dynamic library
build is cached independently from adapter source and unrelated repository
changes.

## Build and use

```sh
scripts/BuildFlintAdapter.sh
python3 adapters/flint/python/normalforms_flint.py snf \
  --input Tests/Certificate/flint/nontrivial.json \
  --output /tmp/nontrivial-snf.json
lake build normalforms-check
.lake/build/bin/normalforms-check emit-lean \
  --certificate /tmp/nontrivial-snf.json \
  --import NormalForms.Tests.External.ExpectedMatrices \
  --matrix NormalForms.Tests.External.nontrivial \
  --theorem NontrivialSNF \
  --output /tmp/NontrivialSNF.lean
lake env lean /tmp/NontrivialSNF.lean
```

The first command downloads and verifies upstream archives, then installs
shared-only libraries under `.lake/externals/prefix`. The worker has a
`$ORIGIN/../lib` RUNPATH, so the entire prefix can be relocated as a unit.
Set `NORMALFORMS_FLINT_JOBS` to control parallel compilation and
`NORMALFORMS_FLINT_RUN_UPSTREAM_TESTS=1` to run each upstream test suite.
When Lean is available the build also creates
`libnormalforms_flint_leanffi.a`; set
`NORMALFORMS_FLINT_BUILD_LEAN_FFI=0`, `1`, or `auto` to control that step.

The separately linked FFI profile is built and tested with:

```sh
NORMALFORMS_FLINT_BUILD_LEAN_FFI=1 scripts/BuildFlintAdapter.sh
lake build normalforms-flint-ffi-worker normalforms-flint-differential
scripts/FlintFFITest.sh
```

Only those optional executables link FLINT. The FFI worker has a relocatable
`$ORIGIN/../../externals/prefix/lib` RUNPATH. Lean 4.32's bundled link sysroot
predates some symbols used by host-built glibc libraries, so these optional
targets allow unresolved shared-library references at link time; the host
dynamic loader must resolve them at execution, and the tests verify all three
pinned libraries resolve from the adapter prefix.

The exact configure policy is:

```text
Environment for all three:
  CC=cc CFLAGS="-O2 -std=gnu17"
GMP:
  --prefix=PREFIX --libdir=PREFIX/lib
  --enable-shared --disable-static --with-pic
MPFR:
  --prefix=PREFIX --libdir=PREFIX/lib
  --enable-shared --disable-static --with-pic --with-gmp=PREFIX
FLINT:
  --prefix=PREFIX --libdir=PREFIX/lib
  --enable-shared --disable-static --with-pic --disable-debug
  --with-gmp=PREFIX --with-mpfr=PREFIX
```

`scripts/BundleFlintSources.sh DESTINATION` creates the corresponding source
and license bundle at a destination that does not already exist. It includes
all three verified source archives, the hash manifest, upstream license files,
these rebuild instructions, and clean copies of the adapter source and build
scripts. `REBUILD.md` gives a bundle-local rebuild and relink procedure. A
recipient may replace or relink the shared libraries by rebuilding the same
prefix and keeping the documented ABI versions. No static linking is used.

## Process and data boundary

The C worker accepts only `normalforms.decimal/v1`: dimensions followed by one
canonical decimal integer per line. It rejects leading zeros, `-0`, extra
input, oversized dimensions, and every integer spelling except `0` or
`-?[1-9][0-9]*`. It calls:

- `fmpz_mat_hnf_transform`, obtaining `U A = H`;
- `fmpz_mat_snf_transform`, obtaining `U A V = S`;
- `fmpz_mat_inv`, accepting an inverse only when the common denominator has
  absolute value one and normalizing a negative denominator.

The Python wrapper uses only the standard library. It validates JSON, runs the
worker as a separate process, checks the complete output protocol, and emits
`normalforms.cert/v1`. Generator version, build string, and hash are inert
metadata. Neither process emits proofs or a typed Lean result.

The common computation implementation is in `c/normalforms_flint.c`.
`c/worker.c` exports the complete decimal-protocol function. The process
worker calls it with standard streams; `c/lean_ffi.c` calls that exact function
with memory streams and returns `IO (Except String String)`. The Lean layer
strictly parses the protocol, reconstructs `normalforms.cert/v1`, checks the
echoed input, and invokes the same pure checker used by the CLI path. It can
return raw or checked data but never a proof or strong normal-form result.

The fixed-seed differential suite compares only normalized invariant factors:
transformation matrices are deliberately ignored because they are not unique.
This is regression evidence, not a mathematical or trust argument. A
successful generated module still has to compile through the strict kernel
path.

## Licensing and source provision

FLINT and MPFR are distributed under LGPL terms; GMP uses its upstream
dual-license terms. The adapter itself remains Apache-2.0. Dynamic linking
keeps the optional components separate, but release artifacts still ship the
exact corresponding sources, copyright/license texts, build configuration,
and relink instructions. Run the bundle script rather than copying only the
worker binary.
