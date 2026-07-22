#!/usr/bin/env bash
# Copyright (c) 2026 Junye Ji. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$repo_root"

with_flint_sources=0

for argument in "$@"; do
  case "$argument" in
    --with-flint-sources)
      with_flint_sources=1
      ;;
    *)
      printf 'unknown argument: %s\n' "$argument" >&2
      exit 2
      ;;
  esac
done

version="$(
  python3 -c \
    'import pathlib,tomllib; print(tomllib.loads(pathlib.Path("lakefile.toml").read_text())["version"])'
)"
prefix="lean-normal-forms-$version"
destination="$repo_root/dist/v$version"
archive="$destination/$prefix.tar.gz"

scripts/ValidateReleaseMetadata.py \
  --version "$version" \
  --require-release-materials

if [[ -n "$(git status --porcelain --untracked-files=normal)" ]]; then
  printf 'release archive requires a clean tracked worktree\n' >&2
  git status --short >&2
  exit 1
fi

commit="$(git rev-parse HEAD)"
source_epoch="$(git show -s --format=%ct HEAD)"
mathlib_revision="$(
  python3 -c \
    'import json,pathlib; d=json.loads(pathlib.Path("lake-manifest.json").read_text()); print(next(p["rev"] for p in d["packages"] if p["name"] == "mathlib"))'
)"

rm -rf -- "$destination"
mkdir -p -- "$destination"
temporary="$(mktemp -d)"
trap 'rm -rf -- "$temporary"' EXIT

git archive --format=tar --prefix="$prefix/" HEAD > "$temporary/source.tar"
gzip -n -9 < "$temporary/source.tar" > "$archive"

install -m 0644 "release/v$version/RELEASE_NOTES.md" \
  "$destination/RELEASE_NOTES.md"
install -m 0644 "release/v$version/zenodo.json" \
  "$destination/zenodo.json"

if [[ "$with_flint_sources" -eq 1 ]]; then
  bundle_root="$temporary/$prefix-flint-sources"
  scripts/BundleFlintSources.sh "$bundle_root"
  tar \
    --sort=name \
    --mtime="@$source_epoch" \
    --owner=0 \
    --group=0 \
    --numeric-owner \
    -C "$temporary" \
    -cf "$temporary/flint-sources.tar" \
    "$prefix-flint-sources"
  gzip -n -9 < "$temporary/flint-sources.tar" \
    > "$destination/$prefix-flint-sources.tar.gz"
fi

python3 - "$destination/BUILDINFO.json" "$version" "$commit" \
  "$source_epoch" "$mathlib_revision" <<'PY'
import json
from pathlib import Path
import sys

path, version, commit, source_epoch, mathlib_revision = sys.argv[1:]
payload = {
    "schema": "normalforms.release-build/v1",
    "version": version,
    "sourceCommit": commit,
    "sourceDateEpoch": int(source_epoch),
    "leanToolchain": "leanprover/lean4:v4.32.0",
    "mathlibRevision": mathlib_revision,
}
Path(path).write_text(
    json.dumps(payload, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
PY

(
  cd -- "$destination"
  find . -maxdepth 1 -type f ! -name SHA256SUMS -printf '%f\n' \
    | LC_ALL=C sort \
    | xargs sha256sum \
    > SHA256SUMS
  sha256sum --check SHA256SUMS
)

printf 'release archive created: %s\n' "$destination"
