#!/usr/bin/env bash
# Copyright (c) 2026 Junye Ji. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$repo_root"

profile="${1:-all}"
if [[ "$#" -gt 1 ]]; then
  printf 'usage: scripts/verify.sh [profile]\n' >&2
  exit 2
fi

case "$profile" in
  core | rational-canonical | homology | bit-cost | kannan-bachem | \
    modular-hnf | lll | flint | all)
    ;;
  *)
    printf 'unknown verification profile: %s\n' "$profile" >&2
    printf '%s\n' \
      'profiles: core rational-canonical homology bit-cost kannan-bachem' \
      '          modular-hnf lll flint all' >&2
    exit 2
    ;;
esac

report_root="${NORMALFORMS_VERIFY_REPORT_DIR:-$repo_root/build/verify}"
mkdir -p -- "$report_root"

prepare() {
  local selected="$1"

  case "$selected" in
    core)
      lake build \
        NormalForms \
        NormalForms.Tests.AuditEngine \
        NormalForms.Tests.PublicApi \
        NormalForms.Tests.CoreFreeze \
        normalforms-check \
        normalforms-polynomial-smoke
      ;;
    rational-canonical)
      lake build \
        NormalForms.Applications.RationalCanonical \
        NormalForms.Tests.AuditEngine \
        NormalForms.Tests.RationalCanonical.PublicApi \
        NormalForms.Tests.CoreFreeze \
        normalforms-rational-canonical-benchmark
      ;;
    homology)
      lake build \
        NormalForms.Applications.Homology \
        NormalForms.Tests.AuditEngine \
        NormalForms.Tests.Homology.PublicApi \
        NormalForms.Tests.CoreFreeze \
        normalforms-homology-smoke
      ;;
    bit-cost)
      lake build \
        NormalForms.Research.BitCost \
        NormalForms.Tests.AuditEngine \
        NormalForms.Tests.Research.BitCost.PublicApi \
        NormalForms.Tests.Research.BitCost.PublicApiV010 \
        NormalForms.Tests.Research.BitCost.Execution \
        NormalForms.Tests.CoreFreeze \
        normalforms-bit-cost-benchmark
      ;;
    kannan-bachem)
      lake build \
        NormalForms.Research.KannanBachem \
        NormalForms.Tests.AuditEngine \
        NormalForms.Tests.Research.KannanBachem.PublicApi \
        NormalForms.Tests.Research.KannanBachem.Execution \
        NormalForms.Tests.CoreFreeze \
        normalforms-kannan-bachem-benchmark
      ;;
    modular-hnf)
      lake build \
        NormalForms.Research.ModularHNF \
        NormalForms.Tests.AuditEngine \
        NormalForms.Tests.Research.ModularHNF.PublicApi \
        NormalForms.Tests.Research.ModularHNF.Execution \
        NormalForms.Tests.CoreFreeze \
        normalforms-modular-hnf-benchmark
      ;;
    lll)
      lake build \
        NormalForms.Research.LLL \
        NormalForms.Tests.AuditEngine \
        NormalForms.Tests.Research.LLL.PublicApi \
        NormalForms.Tests.Research.LLL.Execution \
        NormalForms.Tests.CoreFreeze \
        normalforms-lll-smoke
      ;;
    all)
      # One Lake build command covers every non-optional executable used below.
      lake build \
        NormalForms \
        NormalForms.Tests.AuditEngine \
        NormalForms.Tests.PublicApi \
        NormalForms.Tests.CoreFreeze \
        NormalForms.Tests.Research.BitCost.PublicApiV010 \
        normalforms-check \
        normalforms-polynomial-smoke \
        normalforms-rational-canonical-benchmark \
        normalforms-homology-smoke \
        normalforms-bit-cost-benchmark \
        normalforms-kannan-bachem-benchmark \
        normalforms-modular-hnf-benchmark \
        normalforms-lll-smoke
      ;;
  esac

  lake test
  lake lint
}

run_audit() {
  local source="$1"
  local destination="$2"

  lake env lean "$source" > "$destination"
}

verify_core() {
  local directory="$report_root/core"
  mkdir -p -- "$directory"

  scripts/ExecutionAudit.sh
  run_audit scripts/AxiomAudit.lean "$directory/facade-axioms.json"
  run_audit scripts/CoreAxiomAudit.lean "$directory/core-axioms.json"
  run_audit \
    scripts/CertificateAxiomAudit.lean \
    "$directory/certificate-axioms.json"
  scripts/CertificateImportTest.sh
  scripts/ProfileLeanModules.py --report "$directory/module-profile.json"

  git -C .lake/packages/mathlib apply --check \
    "$repo_root/patches/mathlib/finite-matrix-presentation.patch"

  scripts/VerifyCode.py profile core \
    --axiom "$directory/facade-axioms.json" \
    --axiom "$directory/core-axioms.json" \
    --axiom "$directory/certificate-axioms.json"
}

verify_rational_canonical() {
  local directory="$report_root/rational-canonical"
  mkdir -p -- "$directory"

  .lake/build/bin/normalforms-rational-canonical-benchmark invariants
  .lake/build/bin/normalforms-rational-canonical-benchmark companion
  .lake/build/bin/normalforms-rational-canonical-benchmark total \
    | tee "$directory/native-smoke.txt"
  run_audit \
    scripts/RationalCanonicalAxiomAudit.lean \
    "$directory/axioms.json"
  scripts/VerifyCode.py profile rational-canonical \
    --axiom "$directory/axioms.json" \
    --native "$directory/native-smoke.txt"
}

verify_homology() {
  local directory="$report_root/homology"
  mkdir -p -- "$directory"

  .lake/build/bin/normalforms-homology-smoke \
    | tee "$directory/native-smoke.txt"
  run_audit scripts/HomologyAxiomAudit.lean "$directory/axioms.json"
  scripts/VerifyCode.py profile homology \
    --axiom "$directory/axioms.json" \
    --native "$directory/native-smoke.txt"
}

verify_bit_cost() {
  local directory="$report_root/bit-cost"
  mkdir -p -- "$directory"

  .lake/build/bin/normalforms-bit-cost-benchmark \
    | tee "$directory/native-smoke.txt"
  run_audit \
    scripts/BitCostAxiomAuditV010.lean \
    "$directory/axioms-v0.1.0.json"
  run_audit scripts/BitCostAxiomAudit.lean "$directory/axioms-current.json"
  scripts/VerifyCode.py profile bit-cost \
    --axiom "$directory/axioms-v0.1.0.json" \
    --axiom "$directory/axioms-current.json" \
    --native "$directory/native-smoke.txt"
}

verify_kannan_bachem() {
  local directory="$report_root/kannan-bachem"
  mkdir -p -- "$directory"

  # Force every executable guard to re-elaborate instead of using Lake artifacts.
  lake env lean NormalForms/Tests/Research/KannanBachem/Execution.lean
  .lake/build/bin/normalforms-kannan-bachem-benchmark all \
    | tee "$directory/native-smoke.txt"
  run_audit scripts/KannanBachemAxiomAudit.lean "$directory/axioms.json"
  scripts/VerifyCode.py profile kannan-bachem \
    --axiom "$directory/axioms.json" \
    --native "$directory/native-smoke.txt"
}

verify_modular_hnf() {
  local directory="$report_root/modular-hnf"
  mkdir -p -- "$directory"

  # Force every executable guard to re-elaborate instead of using Lake artifacts.
  lake env lean NormalForms/Tests/Research/ModularHNF/Execution.lean
  .lake/build/bin/normalforms-modular-hnf-benchmark all \
    | tee "$directory/native-smoke.txt"
  run_audit scripts/ModularHNFAxiomAudit.lean "$directory/axioms.json"
  scripts/VerifyCode.py profile modular-hnf \
    --axiom "$directory/axioms.json" \
    --native "$directory/native-smoke.txt"
}

verify_lll() {
  local directory="$report_root/lll"
  mkdir -p -- "$directory"

  # Force every executable guard to re-elaborate instead of using Lake artifacts.
  lake env lean NormalForms/Tests/Research/LLL/Execution.lean
  .lake/build/bin/normalforms-lll-smoke all \
    | tee "$directory/native-smoke.txt"
  run_audit scripts/LLLAxiomAudit.lean "$directory/axioms.json"
  scripts/VerifyCode.py profile lll \
    --axiom "$directory/axioms.json" \
    --native "$directory/native-smoke.txt"
}

verify_flint() {
  local availability="${1:-required}"
  local prefix="${NORMALFORMS_FLINT_PREFIX:-$repo_root/.lake/externals/prefix}"
  local required=(
    "$prefix/bin/normalforms-flint-worker"
    "$prefix/lib/libnormalforms_flint_leanffi.a"
    "$prefix/lib/libflint.so"
    "$prefix/lib/libmpfr.so"
    "$prefix/lib/libgmp.so"
  )
  local missing=()
  local path

  for path in "${required[@]}"; do
    if [[ ! -e "$path" ]]; then
      missing+=("$path")
    fi
  done
  if [[ "${#missing[@]}" -ne 0 ]]; then
    if [[ "$availability" == optional ]]; then
      printf 'optional FLINT verification skipped; pinned build is unavailable:\n'
      printf '  %s\n' "${missing[@]}"
      return 0
    fi
    printf 'FLINT verification requires the pinned adapter build:\n' >&2
    printf '  %s\n' "${missing[@]}" >&2
    printf 'run scripts/BuildFlintAdapter.sh first\n' >&2
    return 1
  fi

  NORMALFORMS_FLINT_SKIP_BUILD=1 scripts/FlintAdapterTest.sh
  NORMALFORMS_FLINT_SKIP_BUILD=1 scripts/FlintFFITest.sh
}

scripts/VerifyCode.py repository

case "$profile" in
  all)
    prepare all
    verify_core
    verify_rational_canonical
    verify_homology
    verify_bit_cost
    verify_kannan_bachem
    verify_modular_hnf
    verify_lll
    verify_flint optional
    ;;
  flint)
    verify_flint required
    ;;
  *)
    prepare "$profile"
    "verify_${profile//-/_}"
    ;;
esac

if [[ -d .git ]]; then
  git diff --check
fi

printf 'code verification passed: profile=%s reports=%s\n' \
  "$profile" "$report_root"
