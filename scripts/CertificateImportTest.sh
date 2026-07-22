#!/usr/bin/env bash
# Copyright (c) 2026 Junye Ji. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

lake build normalforms-check NormalForms.Tests.Generated.ExpectedMatrices

tmp_dir="$(mktemp -d)"
trap 'rm -r -- "$tmp_dir"' EXIT

emit_and_check() {
  local kind="$1"
  local theorem_name="$2"
  local tracked="$3"
  local generated="$tmp_dir/$(basename -- "$tracked")"

  .lake/build/bin/normalforms-check emit-lean \
    --certificate "Tests/Certificate/corpus/valid-medium-${kind}.json" \
    --import NormalForms.Tests.Generated.ExpectedMatrices \
    --matrix NormalForms.Tests.Generated.mediumInput \
    --theorem "$theorem_name" \
    --output "$generated"

  if ! diff -u -- "$tracked" "$generated"; then
    echo "generated ${kind} module is stale" >&2
    return 1
  fi

  lake env lean "$generated"
}

emit_and_check \
  hnf \
  NormalForms.Tests.Generated.mediumHNFCertificate \
  NormalForms/Tests/Generated/MediumHNF.lean

emit_and_check \
  snf \
  NormalForms.Tests.Generated.mediumSNFCertificate \
  NormalForms/Tests/Generated/MediumSNF.lean

if rg -n \
    'native_decide|decide[[:space:]]+\\+native|Lean\\.ofReduceBool|Lean\\.ofReduceNat' \
    "$tmp_dir/MediumHNF.lean" "$tmp_dir/MediumSNF.lean"; then
  echo "strict generated modules contain a forbidden trust primitive" >&2
  exit 1
fi

bad_module="$tmp_dir/OtherMatrixSNF.lean"
.lake/build/bin/normalforms-check emit-lean \
  --certificate Tests/Certificate/corpus/valid-medium-snf.json \
  --import NormalForms.Tests.Generated.ExpectedMatrices \
  --matrix NormalForms.Tests.Generated.otherInput \
  --theorem NormalForms.Tests.Generated.otherMatrixSNFCertificate \
  --output "$bad_module"

if lake env lean "$bad_module" \
    >"$tmp_dir/bad.log" 2>&1; then
  echo "certificate for another expected matrix compiled successfully" >&2
  exit 1
fi

if ! rg -q '`decide_cbv` failed' "$tmp_dir/bad.log"; then
  echo "other-matrix rejection failed with an unexpected diagnostic" >&2
  sed -n '1,120p' "$tmp_dir/bad.log" >&2
  exit 1
fi

echo "strict certificate emit/import tests passed"
