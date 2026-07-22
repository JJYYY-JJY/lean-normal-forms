# Rebuilding and relinking the FLINT adapter

The optional worker is dynamically linked. Its `$ORIGIN/../lib` RUNPATH makes
the installed prefix relocatable as a unit and lets a recipient replace the
corresponding libraries without modifying the executable.

From a release source bundle, verify and reuse the bundled upstream archives:

```sh
bundle_root="$(pwd)"
external_root="$bundle_root/build"
mkdir -p "$external_root/downloads"
cp "$bundle_root"/sources/*.tar.* "$external_root/downloads/"
cd "$bundle_root/lean-normal-forms"
NORMALFORMS_FLINT_EXTERNAL_ROOT="$external_root" \
  scripts/BuildFlintAdapter.sh
```

The resulting prefix is `build/prefix`. To relink with a modified compatible
build, replace `libgmp.so*`, `libmpfr.so*`, and `libflint.so*` under
`build/prefix/lib` together, preserving the ABI sonames expected by
`build/prefix/bin/normalforms-flint-worker`. With Lean available, the build
also emits `build/prefix/lib/libnormalforms_flint_leanffi.a`; relink the
optional Lake FFI executables after replacing the shared libraries. Both
process and FFI workers check the loaded GMP, MPFR, and FLINT version strings
before accepting input.

The exact source hashes, configure switches, platform boundary, and trust
boundary are recorded in `README.md`, `versions.env`, and `SOURCES.sha256`.
