#!/usr/bin/env bash
# Copyright (c) 2026 Junye Ji. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$repo_root"

if [[ "${NORMALFORMS_FLINT_SKIP_BUILD:-0}" != 1 ]]; then
  NORMALFORMS_FLINT_BUILD_LEAN_FFI=1 scripts/BuildFlintAdapter.sh
fi

prefix="${NORMALFORMS_FLINT_PREFIX:-$repo_root/.lake/externals/prefix}"
cli_worker="$prefix/bin/normalforms-flint-worker"
ffi_worker="$repo_root/.lake/build/bin/normalforms-flint-ffi-worker"
differential="$repo_root/.lake/build/bin/normalforms-flint-differential"

lake build \
  normalforms-check \
  normalforms-flint-ffi-worker \
  normalforms-flint-differential \
  NormalForms.Tests.External.ExpectedMatrices

tmp_dir="$(mktemp -d)"
trap 'rm -r -- "$tmp_dir"' EXIT

if ldd "$repo_root/.lake/build/bin/normalforms-check" | rg -q 'libflint'; then
  echo "the pure certificate CLI unexpectedly links FLINT" >&2
  exit 1
fi

if ! readelf -d "$ffi_worker" |
    rg -q '\$ORIGIN/\.\./\.\./externals/prefix/lib'; then
  echo "Lean FFI worker does not carry the relocatable library RUNPATH" >&2
  exit 1
fi

assert_prefix_link() {
  local executable="$1"
  local library="$2"
  local resolved

  resolved="$(
    ldd "$executable" |
      awk -v library="$library" \
        '$1 ~ ("^" library "[.]so") { print $3; exit }'
  )"
  if [[ -z "$resolved" ]] \
      || [[ "$(dirname -- "$(realpath -- "$resolved")")" \
        != "$(realpath -- "$prefix/lib")" ]]; then
    echo "$(basename -- "$executable") did not resolve pinned $library" >&2
    ldd "$executable" >&2
    exit 1
  fi
}

for executable in "$ffi_worker" "$differential"; do
  assert_prefix_link "$executable" libflint
  assert_prefix_link "$executable" libmpfr
  assert_prefix_link "$executable" libgmp
done

request="$tmp_dir/request.txt"
printf '%s\n' \
  normalforms.decimal/v1 \
  'kind snf' \
  'rows 2' \
  'cols 3' \
  'entries 6' \
  6 9 3 4 6 2 \
  end >"$request"
"$cli_worker" <"$request" >"$tmp_dir/cli.protocol"
"$ffi_worker" <"$request" >"$tmp_dir/ffi.protocol"
if ! cmp -s "$tmp_dir/cli.protocol" "$tmp_dir/ffi.protocol"; then
  echo "C worker and Lean FFI worker returned different decimal data" >&2
  diff -u "$tmp_dir/cli.protocol" "$tmp_dir/ffi.protocol" >&2
  exit 1
fi

certificate="$tmp_dir/ffi-snf.json"
python3 adapters/flint/python/normalforms_flint.py snf \
  --input Tests/Certificate/flint/nontrivial.json \
  --worker "$ffi_worker" \
  --generator normalforms-flint-ffi \
  --output "$certificate"

python3 - "$certificate" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as source:
    certificate = json.load(source)
assert certificate["schema"] == "normalforms.cert/v1"
assert certificate["kind"] == "snf"
assert certificate["metadata"]["generator"] == "normalforms-flint-ffi"
assert certificate["metadata"]["flintVersion"] == "3.6.0"
assert set(certificate) == {
    "schema", "kind", "input", "U", "UInverse", "S", "V", "VInverse",
    "metadata",
}
PY

generated_module="$tmp_dir/FlintFFINontrivialSNF.lean"
.lake/build/bin/normalforms-check emit-lean \
  --certificate "$certificate" \
  --import NormalForms.Tests.External.ExpectedMatrices \
  --matrix NormalForms.Tests.External.nontrivial \
  --theorem NormalForms.Tests.External.flintFFINontrivialSNF \
  --output "$generated_module"
lake env lean "$generated_module"

python3 adapters/flint/python/differential.py \
  --cli-worker "$cli_worker" \
  --ffi-worker "$ffi_worker"
"$differential"

if printf '%s\n' \
    normalforms.decimal/v1 \
    'kind snf' \
    'rows 1' \
    'cols 1' \
    'entries 1' \
    00 \
    end |
    "$ffi_worker" >"$tmp_dir/invalid.out" 2>"$tmp_dir/invalid.log"; then
  echo "Lean FFI worker accepted a noncanonical decimal integer" >&2
  exit 1
fi
if ! rg -q 'not a canonical integer' "$tmp_dir/invalid.log"; then
  echo "Lean FFI worker returned an unexpected malformed-input diagnostic" >&2
  sed -n '1,80p' "$tmp_dir/invalid.log" >&2
  exit 1
fi

echo "FLINT FFI, checker, and differential tests passed"
