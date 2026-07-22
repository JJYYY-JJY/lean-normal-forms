#!/usr/bin/env bash
# Copyright (c) 2026 Junye Ji. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
# Resolved from the runtime repository root.
# shellcheck disable=SC1091
source "$repo_root/adapters/flint/versions.env"

external_root="${NORMALFORMS_FLINT_EXTERNAL_ROOT:-$repo_root/.lake/externals}"
destination="${1:-$external_root/flint-source-bundle}"
downloads="$external_root/downloads"
sources="$external_root/src"
project="$destination/lean-normal-forms"

if [[ -e "$destination" ]]; then
  echo "bundle destination already exists: $destination" >&2
  exit 1
fi

"$repo_root/scripts/BuildFlintAdapter.sh"

mkdir -p -- "$destination/sources" "$destination/licenses" \
  "$project/adapters/flint/c" "$project/adapters/flint/python" \
  "$project/adapters/flint/container" "$project/scripts"

install -m 0644 "$downloads/$FLINT_ARCHIVE" "$destination/sources/"
install -m 0644 "$downloads/$GMP_ARCHIVE" "$destination/sources/"
install -m 0644 "$downloads/$MPFR_ARCHIVE" "$destination/sources/"
install -m 0644 "$repo_root/adapters/flint/SOURCES.sha256" \
  "$destination/sources/SHA256SUMS"

install -m 0644 "$sources/flint-$FLINT_VERSION/COPYING" \
  "$destination/licenses/FLINT-COPYING"
install -m 0644 "$sources/gmp-$GMP_VERSION/COPYINGv2" \
  "$destination/licenses/GMP-COPYINGv2"
install -m 0644 "$sources/gmp-$GMP_VERSION/COPYINGv3" \
  "$destination/licenses/GMP-COPYINGv3"
install -m 0644 "$sources/gmp-$GMP_VERSION/COPYING.LESSERv3" \
  "$destination/licenses/GMP-COPYING.LESSERv3"
install -m 0644 "$sources/mpfr-$MPFR_VERSION/COPYING" \
  "$destination/licenses/MPFR-COPYING"
install -m 0644 "$sources/mpfr-$MPFR_VERSION/COPYING.LESSER" \
  "$destination/licenses/MPFR-COPYING.LESSER"

install -m 0644 "$repo_root/adapters/flint/c/normalforms_flint.h" \
  "$project/adapters/flint/c/"
install -m 0644 "$repo_root/adapters/flint/c/normalforms_protocol.h" \
  "$project/adapters/flint/c/"
install -m 0644 "$repo_root/adapters/flint/c/normalforms_flint.c" \
  "$project/adapters/flint/c/"
install -m 0644 "$repo_root/adapters/flint/c/worker.c" \
  "$project/adapters/flint/c/"
install -m 0644 "$repo_root/adapters/flint/c/lean_ffi.c" \
  "$project/adapters/flint/c/"
install -m 0755 "$repo_root/adapters/flint/python/normalforms_flint.py" \
  "$project/adapters/flint/python/"
install -m 0755 "$repo_root/adapters/flint/python/differential.py" \
  "$project/adapters/flint/python/"
install -m 0644 "$repo_root/adapters/flint/container/Dockerfile" \
  "$project/adapters/flint/container/"
install -m 0644 "$repo_root/adapters/flint/README.md" \
  "$project/adapters/flint/README.md"
install -m 0644 "$repo_root/adapters/flint/REBUILD.md" \
  "$project/adapters/flint/REBUILD.md"
install -m 0644 "$repo_root/adapters/flint/versions.env" \
  "$project/adapters/flint/versions.env"
install -m 0644 "$repo_root/adapters/flint/SOURCES.sha256" \
  "$project/adapters/flint/SOURCES.sha256"
install -m 0644 "$repo_root/LICENSE" "$project/LICENSE"
install -m 0755 "$repo_root/scripts/BuildFlintAdapter.sh" \
  "$project/scripts/"
install -m 0755 "$repo_root/scripts/BundleFlintSources.sh" \
  "$project/scripts/"

(
  cd -- "$destination/sources"
  sha256sum --check SHA256SUMS
)

echo "created FLINT source and license bundle at $destination"
