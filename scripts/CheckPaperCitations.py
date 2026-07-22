#!/usr/bin/env python3
"""Static and build checks for the seven project manuscripts."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
BIBLIOGRAPHY = PAPER / "references.bib"
MANUSCRIPTS = (
    PAPER,
    PAPER / "rational-canonical",
    PAPER / "homology",
    PAPER / "bit-cost",
    PAPER / "kannan-bachem",
    PAPER / "modular-hnf",
    PAPER / "lll",
)

CITATION_RE = re.compile(
    r"\\cite[a-zA-Z]*\*?(?:\s*\[[^]]*\]){0,2}\s*\{([^}]*)\}", re.DOTALL
)
DOI_RE = re.compile(r"(?im)^\s*doi\s*=\s*[\{\"]([^}\"]+)[}\"]")
BIBITEM_RE = re.compile(r"\\bibitem(?:\[[^]]*\])?\{([^}]+)\}")


def without_comments(text: str) -> str:
    return "\n".join(re.sub(r"(?<!\\)%.*$", "", line) for line in text.splitlines())


def citation_keys() -> tuple[set[str], list[str]]:
    keys: set[str] = set()
    errors: list[str] = []
    for tex in sorted(PAPER.rglob("*.tex")):
        text = without_comments(tex.read_text(encoding="utf-8"))
        for match in CITATION_RE.finditer(text):
            for raw_key in match.group(1).split(","):
                key = raw_key.strip()
                if not key:
                    errors.append(f"{tex.relative_to(ROOT)}: empty citation key")
                else:
                    keys.add(key)
    return keys, errors


def bib_entries(text: str) -> tuple[dict[str, str], list[str]]:
    entries: dict[str, str] = {}
    errors: list[str] = []
    cursor = 0
    while True:
        start = text.find("@", cursor)
        if start < 0:
            break
        opening = text.find("{", start)
        if opening < 0:
            errors.append("bibliography: entry without opening brace")
            break
        comma = text.find(",", opening)
        if comma < 0:
            errors.append("bibliography: entry without key separator")
            break
        key = text[opening + 1 : comma].strip()
        depth = 1
        index = opening + 1
        while depth and index + 1 < len(text):
            index += 1
            if text[index] == "{" and text[index - 1] != "\\":
                depth += 1
            elif text[index] == "}" and text[index - 1] != "\\":
                depth -= 1
        if depth:
            errors.append(f"bibliography: unterminated entry {key or '<unknown>'}")
            break
        entry = text[start : index + 1]
        if not key:
            errors.append("bibliography: empty entry key")
        elif key in entries:
            errors.append(f"bibliography: duplicate key {key}")
        else:
            entries[key] = entry
        cursor = index + 1
    return entries, errors


def normalized_doi(value: str) -> str:
    doi = value.strip().lower()
    for prefix in ("https://doi.org/", "http://doi.org/", "doi:"):
        if doi.startswith(prefix):
            doi = doi[len(prefix) :]
    return doi.rstrip("./")


def static_checks() -> list[str]:
    errors: list[str] = []
    local_bibs = sorted(path for path in PAPER.rglob("*.bib") if path != BIBLIOGRAPHY)
    if local_bibs:
        rendered = ", ".join(str(path.relative_to(ROOT)) for path in local_bibs)
        errors.append(f"local bibliographies are forbidden: {rendered}")

    cited, citation_errors = citation_keys()
    errors.extend(citation_errors)
    entries, bib_errors = bib_entries(BIBLIOGRAPHY.read_text(encoding="utf-8"))
    errors.extend(bib_errors)

    missing = sorted(cited - entries.keys())
    unused = sorted(entries.keys() - cited)
    if missing:
        errors.append("missing bibliography keys: " + ", ".join(missing))
    if unused:
        errors.append("unused bibliography entries: " + ", ".join(unused))

    dois: dict[str, str] = {}
    for key, entry in entries.items():
        match = DOI_RE.search(entry)
        if not match:
            continue
        doi = normalized_doi(match.group(1))
        if doi in dois:
            errors.append(f"duplicate DOI {doi}: {dois[doi]}, {key}")
        else:
            dois[doi] = key
    return errors


def run_build(directory: Path) -> list[str]:
    label = directory.relative_to(PAPER).as_posix() if directory != PAPER else "core"
    result = subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
        cwd=directory,
        env=os.environ.copy(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    errors: list[str] = []
    if result.returncode:
        tail = "\n".join(result.stdout.splitlines()[-35:])
        errors.append(f"{label}: latexmk failed\n{tail}")
        return errors

    log = (directory / "main.log").read_text(encoding="utf-8", errors="replace")
    forbidden = {
        "undefined citation": re.compile(r"Citation .* undefined|undefined citations", re.I),
        "undefined reference": re.compile(r"Reference .* undefined|undefined references", re.I),
        "overfull box": re.compile(r"Overfull \\(?:hbox|vbox)"),
    }
    for description, pattern in forbidden.items():
        if pattern.search(log):
            errors.append(f"{label}: {description} in main.log")

    blg = directory / "main.blg"
    if blg.exists():
        blg_text = blg.read_text(encoding="utf-8", errors="replace")
        if re.search(
            r"Warning--I didn't find a database entry|Repeated entry|I couldn't open database file",
            blg_text,
            re.I,
        ):
            errors.append(f"{label}: BibTeX database error in main.blg")

    bbl = directory / "main.bbl"
    if not bbl.exists():
        errors.append(f"{label}: main.bbl was not produced")
    else:
        items = BIBITEM_RE.findall(bbl.read_text(encoding="utf-8", errors="replace"))
        duplicates = sorted({item for item in items if items.count(item) > 1})
        if duplicates:
            errors.append(f"{label}: duplicate bibliography output: {', '.join(duplicates)}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--build",
        action="store_true",
        help="also compile all seven manuscripts and inspect their final logs",
    )
    args = parser.parse_args()

    errors = static_checks()
    if args.build and not errors:
        for directory in MANUSCRIPTS:
            errors.extend(run_build(directory))

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    scope = "static checks and seven builds" if args.build else "static checks"
    print(f"paper citations: {scope} passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
