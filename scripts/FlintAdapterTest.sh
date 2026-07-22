#!/usr/bin/env bash
# Copyright (c) 2026 Junye Ji. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$repo_root"

if [[ "${NORMALFORMS_FLINT_SKIP_BUILD:-0}" != 1 ]]; then
  scripts/BuildFlintAdapter.sh
fi

# Resolved after changing to the repository root.
# shellcheck disable=SC1091
source adapters/flint/versions.env
prefix="${NORMALFORMS_FLINT_PREFIX:-$repo_root/.lake/externals/prefix}"
worker="$prefix/bin/normalforms-flint-worker"
wrapper=(
  python3
  adapters/flint/python/normalforms_flint.py
)

lake build normalforms-check NormalForms.Tests.External.ExpectedMatrices

tmp_dir="$(mktemp -d)"
trap 'rm -r -- "$tmp_dir"' EXIT

if ! readelf -d "$worker" | rg -q '\$ORIGIN/\.\./lib'; then
  echo "worker does not carry the relocatable library RUNPATH" >&2
  exit 1
fi

assert_prefix_link() {
  local library="$1"
  local resolved

  resolved="$(
    ldd "$worker" |
      awk -v library="$library" \
        '$1 ~ ("^" library "[.]so") { print $3; exit }'
  )"
  if [[ -z "$resolved" ]] \
      || [[ "$(dirname -- "$(realpath -- "$resolved")")" \
        != "$(realpath -- "$prefix/lib")" ]]; then
    echo "worker did not resolve the pinned $library shared library" >&2
    ldd "$worker" >&2
    exit 1
  fi
}

assert_prefix_link libflint
assert_prefix_link libmpfr
assert_prefix_link libgmp

emit_compile() {
  local kind="$1"
  local input="$2"
  local matrix="$3"
  local stem="$4"
  local certificate="$tmp_dir/$stem.json"
  local module="$tmp_dir/$stem.lean"

  "${wrapper[@]}" "$kind" \
    --input "$input" \
    --worker "$worker" \
    --output "$certificate"

  .lake/build/bin/normalforms-check emit-lean \
    --certificate "$certificate" \
    --import NormalForms.Tests.External.ExpectedMatrices \
    --matrix "$matrix" \
    --theorem "NormalForms.Tests.External.${stem}Certificate" \
    --output "$module"

  if rg -n \
      'native_decide|decide[[:space:]]+\\+native|Lean\\.ofReduceBool|Lean\\.ofReduceNat' \
      "$module"; then
    echo "FLINT-generated strict module contains forbidden native trust" >&2
    return 1
  fi

  lake env lean "$module"
}

emit_compile \
  hnf \
  Tests/Certificate/flint/nontrivial.json \
  NormalForms.Tests.External.nontrivial \
  FlintNontrivialHNF
emit_compile \
  snf \
  Tests/Certificate/flint/nontrivial.json \
  NormalForms.Tests.External.nontrivial \
  FlintNontrivialSNF
emit_compile \
  snf \
  Tests/Certificate/flint/rank-deficient.json \
  NormalForms.Tests.External.rankDeficient \
  FlintRankDeficientSNF
emit_compile \
  hnf \
  Tests/Certificate/flint/zero-rows.json \
  NormalForms.Tests.External.zeroRows \
  FlintZeroRowsHNF
emit_compile \
  snf \
  Tests/Certificate/flint/zero-rows.json \
  NormalForms.Tests.External.zeroRows \
  FlintZeroRowsSNF
emit_compile \
  hnf \
  Tests/Certificate/flint/zero-columns.json \
  NormalForms.Tests.External.zeroColumns \
  FlintZeroColumnsHNF
emit_compile \
  snf \
  Tests/Certificate/flint/zero-columns.json \
  NormalForms.Tests.External.zeroColumns \
  FlintZeroColumnsSNF

python3 - "$tmp_dir/FlintNontrivialSNF.json" <<'PY'
import json
import sys

path = sys.argv[1]
certificate = json.load(open(path, encoding="utf-8"))
assert certificate["schema"] == "normalforms.cert/v1"
assert certificate["metadata"]["flintVersion"] == "3.6.0"
assert certificate["metadata"]["hash"].startswith("sha256:")
certificate["UInverse"]["entries"][0] = "2"
with open(path, "w", encoding="utf-8") as output:
    json.dump(certificate, output)
    output.write("\n")
PY

bad_module="$tmp_dir/TamperedInverse.lean"
.lake/build/bin/normalforms-check emit-lean \
  --certificate "$tmp_dir/FlintNontrivialSNF.json" \
  --import NormalForms.Tests.External.ExpectedMatrices \
  --matrix NormalForms.Tests.External.nontrivial \
  --theorem NormalForms.Tests.External.tamperedInverse \
  --output "$bad_module"

if lake env lean "$bad_module" >"$tmp_dir/tampered.log" 2>&1; then
  echo "tampered FLINT inverse compiled successfully" >&2
  exit 1
fi
if ! rg -q '`decide_cbv` failed' "$tmp_dir/tampered.log"; then
  echo "tampered FLINT inverse failed with an unexpected diagnostic" >&2
  sed -n '1,120p' "$tmp_dir/tampered.log" >&2
  exit 1
fi

if printf '%s\n' \
    normalforms.decimal/v1 \
    'kind hnf' \
    'rows 1' \
    'cols 1' \
    'entries 1' \
    '00' \
    end \
    | "$worker" >"$tmp_dir/invalid.out" 2>"$tmp_dir/invalid.log"; then
  echo "worker accepted a noncanonical decimal integer" >&2
  exit 1
fi
if ! rg -q 'not a canonical integer' "$tmp_dir/invalid.log"; then
  echo "worker rejected malformed input with an unexpected diagnostic" >&2
  sed -n '1,80p' "$tmp_dir/invalid.log" >&2
  exit 1
fi

if "${wrapper[@]}" hnf \
    --input Tests/Certificate/flint/nontrivial.json \
    --output "$tmp_dir/invalid-timeout.json" \
    --timeout-seconds nan >"$tmp_dir/invalid-timeout.out" 2>&1; then
  echo "wrapper accepted a non-finite timeout" >&2
  exit 1
fi
if ! rg -q 'timeout must be positive' "$tmp_dir/invalid-timeout.out"; then
  echo "wrapper rejected a non-finite timeout with an unexpected diagnostic" >&2
  sed -n '1,80p' "$tmp_dir/invalid-timeout.out" >&2
  exit 1
fi

echo "FLINT adapter and strict Lean recheck tests passed"
