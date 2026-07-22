#!/usr/bin/env bash

set -euo pipefail

readonly algorithm_files=(
  NormalForms/Matrix/Elementary/Basic.lean
  NormalForms/Matrix/Certificates/ReversibleLog.lean
  NormalForms/Matrix/Hermite/Algorithm.lean
  NormalForms/Matrix/Smith/Algorithm.lean
)

# Benchmark and test modules are observational harnesses. Their theorem roots
# have separate axiom audits, while this source scan covers trusted library
# modules only.
mapfile -t trusted_source_files < <(
  rg --files NormalForms \
    -g '*.lean' \
    -g '!NormalForms/Benchmarks/**' \
    -g '!NormalForms/Tests/**'
)
trusted_source_files+=(NormalForms.lean)
readonly trusted_source_files

fail_on_match() {
  local description="$1"
  local pattern="$2"
  shift 2

  local matches
  matches="$(rg -n -- "$pattern" "$@" || true)"
  if [[ -n "$matches" ]]; then
    printf '%s\n%s\n' "$description" "$matches" >&2
    exit 1
  fi
}

fail_on_match \
  "executable normal-form modules still depend on factorization-based termination" \
  'normalizedFactors|UniqueFactorization' \
  "${algorithm_files[@]}"

fail_on_match \
  "the rational-polynomial runtime still calls mathlib extended-gcd data" \
  'EuclideanDomain\.(gcdA|gcdB)' \
  NormalForms/Euclidean/PolynomialRat.lean

fail_on_match \
  "the operational certificate path reconstructs an inverse nonconstructively" \
  'Matrix\.inv|nonsing_inv' \
  "${algorithm_files[@]}"

fail_on_match \
  "trusted library sources contain compiler/native trust primitives" \
  'native_decide|decide[[:space:]]+\+native|Lean\.ofReduce(Bool|Nat)' \
  "${trusted_source_files[@]}"

rg -q 'private def rawXgcd' NormalForms/Euclidean/PolynomialRat.lean
rg -q 'ComputableEuclideanOps\.dvdB' NormalForms/Matrix/Smith/Algorithm.lean
rg -q 'ComputableEuclideanOps\.measure' NormalForms/Matrix/Smith/Algorithm.lean

readonly expected_int='(!![2, 5, 3; 0, 0, 0], !![1, 0, 0; 0, 0, 0])'
int_output="$(lake env lean Tests/Execution/IntEval.lean)"
if [[ "$int_output" != "$expected_int" ]]; then
  printf 'unexpected Int #eval output:\n%s\n' "$int_output" >&2
  exit 1
fi

poly_output="$(lake env lean Tests/Execution/PolynomialEval.lean)"
if [[ "$poly_output" != 'true' ]]; then
  printf 'unexpected Polynomial Rat #eval output:\n%s\n' "$poly_output" >&2
  exit 1
fi

lake build normalforms-polynomial-smoke

readonly expected_native=$(
  printf '%s\n' \
    'pivot-improvement certificate check passed' \
    'zero-matrix certificate check passed' \
    'constant full-rank certificate check passed' \
    'rank-deficient certificate check passed' \
    'zero-row certificate check passed'
)
native_output="$(.lake/build/bin/normalforms-polynomial-smoke)"
if [[ "$native_output" != "$expected_native" ]]; then
  printf 'unexpected native polynomial smoke output:\n%s\n' "$native_output" >&2
  exit 1
fi

printf '%s\n' \
  'constructive source audit passed' \
  'Int #eval baseline passed' \
  'Polynomial Rat #eval baseline passed' \
  'native polynomial certificate baseline passed'
