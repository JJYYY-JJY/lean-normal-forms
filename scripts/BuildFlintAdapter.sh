#!/usr/bin/env bash
# Copyright (c) 2026 Junye Ji. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
# Resolved from the runtime repository root.
# shellcheck disable=SC1091
source "$repo_root/adapters/flint/versions.env"

external_root="${NORMALFORMS_FLINT_EXTERNAL_ROOT:-$repo_root/.lake/externals}"
download_dir="$external_root/downloads"
source_dir="$external_root/src"
build_dir="$external_root/build"
prefix="${NORMALFORMS_FLINT_PREFIX:-$external_root/prefix}"
jobs="${NORMALFORMS_FLINT_JOBS:-$(getconf _NPROCESSORS_ONLN)}"
run_upstream_tests="${NORMALFORMS_FLINT_RUN_UPSTREAM_TESTS:-0}"
libraries_only="${NORMALFORMS_FLINT_LIBRARIES_ONLY:-0}"
build_lean_ffi="${NORMALFORMS_FLINT_BUILD_LEAN_FFI:-auto}"
cc="${CC:-cc}"
ar="${AR:-ar}"

if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo "the v0.3 FLINT adapter supports Linux x86_64 only" >&2
  exit 1
fi

if [[ "$run_upstream_tests" != 0 && "$run_upstream_tests" != 1 ]]; then
  echo "NORMALFORMS_FLINT_RUN_UPSTREAM_TESTS must be 0 or 1" >&2
  exit 1
fi
if [[ "$libraries_only" != 0 && "$libraries_only" != 1 ]]; then
  echo "NORMALFORMS_FLINT_LIBRARIES_ONLY must be 0 or 1" >&2
  exit 1
fi
if [[ "$build_lean_ffi" != 0 && "$build_lean_ffi" != 1 \
    && "$build_lean_ffi" != auto ]]; then
  echo "NORMALFORMS_FLINT_BUILD_LEAN_FFI must be 0, 1, or auto" >&2
  exit 1
fi
if [[ "$build_lean_ffi" == auto ]]; then
  if command -v lean >/dev/null 2>&1; then
    build_lean_ffi=1
  else
    build_lean_ffi=0
  fi
fi

for command in curl sha256sum tar make m4 "$cc"; do
  if ! command -v "$command" >/dev/null 2>&1; then
    echo "missing required build command: $command" >&2
    exit 1
  fi
done
if [[ "$build_lean_ffi" == 1 ]]; then
  for command in "$ar" lean; do
    if ! command -v "$command" >/dev/null 2>&1; then
      echo "missing required Lean FFI build command: $command" >&2
      exit 1
    fi
  done
fi

mkdir -p -- "$download_dir" "$source_dir" "$build_dir" \
  "$prefix/bin" "$prefix/include" "$prefix/lib"

download_and_verify() {
  local archive="$1"
  local url="$2"
  local expected="$3"
  local destination="$download_dir/$archive"

  if [[ ! -f "$destination" ]]; then
    echo "downloading $archive"
    curl --fail --location --proto '=https' --tlsv1.2 \
      --output "$destination" "$url"
  fi

  local actual
  actual="$(sha256sum "$destination" | cut -d ' ' -f 1)"
  if [[ "$actual" != "$expected" ]]; then
    echo "SHA256 mismatch for $archive" >&2
    echo "expected: $expected" >&2
    echo "actual:   $actual" >&2
    exit 1
  fi
}

extract_archive() {
  local archive="$1"
  local directory="$2"

  if [[ ! -d "$source_dir/$directory" ]]; then
    echo "extracting $archive"
    tar -xf "$download_dir/$archive" -C "$source_dir"
  fi
  if [[ ! -d "$source_dir/$directory" ]]; then
    echo "$archive did not contain the expected $directory directory" >&2
    exit 1
  fi
}

run_make() {
  local directory="$1"
  shift
  make -C "$directory" -j "$jobs" "$@"
}

maybe_test() {
  local directory="$1"
  if [[ "$run_upstream_tests" == 1 ]]; then
    run_make "$directory" check
  fi
}

download_and_verify "$FLINT_ARCHIVE" "$FLINT_URL" "$FLINT_SHA256"
download_and_verify "$GMP_ARCHIVE" "$GMP_URL" "$GMP_SHA256"
download_and_verify "$MPFR_ARCHIVE" "$MPFR_URL" "$MPFR_SHA256"

extract_archive "$GMP_ARCHIVE" "gmp-$GMP_VERSION"
extract_archive "$MPFR_ARCHIVE" "mpfr-$MPFR_VERSION"
extract_archive "$FLINT_ARCHIVE" "flint-$FLINT_VERSION"

gmp_build="$build_dir/gmp-$GMP_VERSION"
if [[ ! -f "$prefix/lib/libgmp.so" ]]; then
  mkdir -p -- "$gmp_build"
  if [[ ! -f "$gmp_build/Makefile" ]]; then
    (
      cd -- "$gmp_build"
      CC="$cc" \
      CFLAGS="-O2 -std=gnu17" \
      "$source_dir/gmp-$GMP_VERSION/configure" \
        "--prefix=$prefix" \
        "--libdir=$prefix/lib" \
        --enable-shared \
        --disable-static \
        --with-pic
    )
  fi
  run_make "$gmp_build"
  maybe_test "$gmp_build"
  run_make "$gmp_build" install
fi

mpfr_build="$build_dir/mpfr-$MPFR_VERSION"
if [[ ! -f "$prefix/lib/libmpfr.so" ]]; then
  mkdir -p -- "$mpfr_build"
  if [[ ! -f "$mpfr_build/Makefile" ]]; then
    (
      cd -- "$mpfr_build"
      CC="$cc" \
      CFLAGS="-O2 -std=gnu17" \
      CPPFLAGS="-I$prefix/include" \
      LDFLAGS="-L$prefix/lib" \
      "$source_dir/mpfr-$MPFR_VERSION/configure" \
        "--prefix=$prefix" \
        "--libdir=$prefix/lib" \
        --enable-shared \
        --disable-static \
        --with-pic \
        "--with-gmp=$prefix"
    )
  fi
  run_make "$mpfr_build"
  maybe_test "$mpfr_build"
  run_make "$mpfr_build" install
fi

flint_build="$build_dir/flint-$FLINT_VERSION"
if [[ ! -f "$prefix/lib/libflint.so" ]]; then
  mkdir -p -- "$flint_build"
  if [[ ! -f "$flint_build/Makefile" ]]; then
    (
      cd -- "$flint_build"
      CC="$cc" \
      CFLAGS="-O2 -std=gnu17" \
      CPPFLAGS="-I$prefix/include" \
      LDFLAGS="-L$prefix/lib" \
      LD_LIBRARY_PATH="$prefix/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
      "$source_dir/flint-$FLINT_VERSION/configure" \
        "--prefix=$prefix" \
        "--libdir=$prefix/lib" \
        --enable-shared \
        --disable-static \
        --with-pic \
        --disable-debug \
        "--with-gmp=$prefix" \
        "--with-mpfr=$prefix"
    )
  fi
  run_make "$flint_build"
  if [[ "$run_upstream_tests" == 1 ]]; then
    LD_LIBRARY_PATH="$prefix/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
      run_make "$flint_build" check
  fi
  run_make "$flint_build" install
fi

if [[ "$libraries_only" == 1 ]]; then
  echo "built pinned FLINT libraries under $prefix"
  exit 0
fi

adapter_build="$build_dir/normalforms-flint-adapter"
mkdir -p -- "$adapter_build"

common_flags=(
  -std=c11
  -O2
  -fPIC
  -Wall
  -Wextra
  -Werror
  -Wpedantic
  -Wshadow
  -Wformat=2
  "-I$prefix/include"
  "-I$repo_root/adapters/flint/c"
)

"$cc" "${common_flags[@]}" \
  -c "$repo_root/adapters/flint/c/normalforms_flint.c" \
  -o "$adapter_build/normalforms_flint.o"
"$cc" "${common_flags[@]}" \
  -c "$repo_root/adapters/flint/c/worker.c" \
  -o "$adapter_build/worker.o"
"$cc" \
  "$adapter_build/normalforms_flint.o" \
  "$adapter_build/worker.o" \
  "-L$prefix/lib" \
  -Wl,--no-as-needed \
  -lflint \
  -lmpfr \
  -lgmp \
  -Wl,--as-needed \
  "-Wl,-rpath,\$ORIGIN/../lib" \
  -o "$prefix/bin/normalforms-flint-worker"

if [[ "$build_lean_ffi" == 1 ]]; then
  lean_prefix="$(lean --print-prefix)"
  "$cc" "${common_flags[@]}" \
    -DNORMALFORMS_FLINT_NO_MAIN \
    -c "$repo_root/adapters/flint/c/worker.c" \
    -o "$adapter_build/protocol_ffi.o"
  "$cc" "${common_flags[@]}" \
    "-I$lean_prefix/include" \
    -Wno-pedantic \
    -c "$repo_root/adapters/flint/c/lean_ffi.c" \
    -o "$adapter_build/lean_ffi.o"
  "$ar" rcs "$prefix/lib/libnormalforms_flint_leanffi.a" \
    "$adapter_build/normalforms_flint.o" \
    "$adapter_build/protocol_ffi.o" \
    "$adapter_build/lean_ffi.o"
fi

install -m 0644 \
  "$repo_root/adapters/flint/c/normalforms_flint.h" \
  "$prefix/include/normalforms_flint.h"
install -m 0644 \
  "$repo_root/adapters/flint/c/normalforms_protocol.h" \
  "$prefix/include/normalforms_protocol.h"

echo "built $prefix/bin/normalforms-flint-worker"
if [[ "$build_lean_ffi" == 1 ]]; then
  echo "built $prefix/lib/libnormalforms_flint_leanffi.a"
fi
