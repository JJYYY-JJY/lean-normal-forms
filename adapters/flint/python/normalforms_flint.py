#!/usr/bin/env python3
"""Untrusted JSON wrapper for the normalforms FLINT decimal worker."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any


SCHEMA = "normalforms.cert/v1"
PROTOCOL = "normalforms.decimal/v1"
FLINT_VERSION = "3.6.0"
GMP_VERSION = "6.3.0"
MPFR_VERSION = "4.2.2"
MAX_DIMENSION = 4096
MAX_ENTRIES = 16_777_216
CANONICAL_INTEGER = re.compile(r"(?:0|-[1-9][0-9]*|[1-9][0-9]*)\Z")


class AdapterError(Exception):
    """A deterministic input, worker, or output protocol failure."""


def _default_worker() -> Path:
    repository = Path(__file__).resolve().parents[3]
    return repository / ".lake" / "externals" / "prefix" / "bin" / (
        "normalforms-flint-worker"
    )


def _load_matrix(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise AdapterError(f"cannot read input matrix: {error}") from error

    if not isinstance(value, dict) or set(value) != {"rows", "cols", "entries"}:
        raise AdapterError("input must contain exactly rows, cols, and entries")

    rows = value["rows"]
    columns = value["cols"]
    entries = value["entries"]
    if (
        isinstance(rows, bool)
        or not isinstance(rows, int)
        or rows < 0
        or rows > MAX_DIMENSION
    ):
        raise AdapterError(f"rows must be an integer from 0 to {MAX_DIMENSION}")
    if (
        isinstance(columns, bool)
        or not isinstance(columns, int)
        or columns < 0
        or columns > MAX_DIMENSION
    ):
        raise AdapterError(f"cols must be an integer from 0 to {MAX_DIMENSION}")
    if rows * columns > MAX_ENTRIES:
        raise AdapterError(f"input may contain at most {MAX_ENTRIES} entries")
    if not isinstance(entries, list) or len(entries) != rows * columns:
        raise AdapterError("entry count does not match rows times cols")
    for index, entry in enumerate(entries):
        if not isinstance(entry, str) or CANONICAL_INTEGER.fullmatch(entry) is None:
            raise AdapterError(f"entries[{index}] is not a canonical integer string")

    return {"rows": rows, "cols": columns, "entries": entries}


def _worker_request(kind: str, matrix: dict[str, Any]) -> str:
    lines = [
        PROTOCOL,
        f"kind {kind}",
        f"rows {matrix['rows']}",
        f"cols {matrix['cols']}",
        f"entries {len(matrix['entries'])}",
        *matrix["entries"],
        "end",
    ]
    return "\n".join(lines) + "\n"


def _matrix_dimensions(
    kind: str, name: str, rows: int, columns: int
) -> tuple[int, int]:
    if name in {"input", "H", "S"}:
        return rows, columns
    if name in {"U", "UInverse"}:
        return rows, rows
    if kind == "snf" and name in {"V", "VInverse"}:
        return columns, columns
    raise AdapterError(f"worker returned unexpected matrix {name}")


def _parse_worker_output(
    kind: str, source: str, rows: int, columns: int
) -> dict[str, dict[str, Any]]:
    if "\r" in source or "\x00" in source or not source.endswith("\n"):
        raise AdapterError("worker output is not canonical LF-delimited text")
    lines = source.splitlines()
    cursor = 0

    def take(description: str) -> str:
        nonlocal cursor
        if cursor >= len(lines):
            raise AdapterError(f"worker output is missing {description}")
        line = lines[cursor]
        cursor += 1
        return line

    if take("protocol header") != PROTOCOL:
        raise AdapterError("worker returned the wrong protocol header")
    if take("kind") != f"kind {kind}":
        raise AdapterError("worker returned the wrong certificate kind")
    if take("FLINT version") != f"flint {FLINT_VERSION}":
        raise AdapterError(f"worker did not report FLINT {FLINT_VERSION}")

    names = (
        ["input", "U", "UInverse", "H"]
        if kind == "hnf"
        else ["input", "U", "UInverse", "S", "V", "VInverse"]
    )
    matrices: dict[str, dict[str, Any]] = {}
    for expected_name in names:
        header = take(f"{expected_name} header").split(" ")
        if len(header) != 5 or header[0] != "matrix":
            raise AdapterError(f"worker returned an invalid {expected_name} header")
        _, name, raw_rows, raw_columns, raw_count = header
        if name != expected_name:
            raise AdapterError(
                f"worker returned {name} where {expected_name} was required"
            )
        dimension_parts = (raw_rows, raw_columns, raw_count)
        if not all(
            part.isascii()
            and part.isdecimal()
            and (part == "0" or not part.startswith("0"))
            for part in dimension_parts
        ):
            raise AdapterError(f"worker returned invalid dimensions for {name}")
        actual_rows = int(raw_rows)
        actual_columns = int(raw_columns)
        count = int(raw_count)
        expected_rows, expected_columns = _matrix_dimensions(
            kind, name, rows, columns
        )
        if (actual_rows, actual_columns) != (expected_rows, expected_columns):
            raise AdapterError(f"worker returned wrong dimensions for {name}")
        if count != actual_rows * actual_columns:
            raise AdapterError(f"worker returned wrong entry count for {name}")

        entries = [take(f"{name} entry {index}") for index in range(count)]
        for index, entry in enumerate(entries):
            if CANONICAL_INTEGER.fullmatch(entry) is None:
                raise AdapterError(
                    f"worker returned a noncanonical {name} entry at {index}"
                )
        matrices[name] = {
            "rows": actual_rows,
            "cols": actual_columns,
            "entries": entries,
        }

    if take("end marker") != "end":
        raise AdapterError("worker output is missing its end marker")
    if cursor != len(lines):
        raise AdapterError("worker output has trailing lines")
    return matrices


def _run_worker(
    worker: Path,
    kind: str,
    matrix: dict[str, Any],
    timeout_seconds: float,
) -> dict[str, dict[str, Any]]:
    if not worker.is_file() or not os.access(worker, os.X_OK):
        raise AdapterError(f"worker is not executable: {worker}")

    try:
        result = subprocess.run(
            [str(worker)],
            input=_worker_request(kind, matrix),
            text=True,
            encoding="utf-8",
            errors="strict",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=timeout_seconds,
        )
    except (OSError, UnicodeError, subprocess.TimeoutExpired) as error:
        raise AdapterError(f"worker execution failed: {error}") from error

    if result.returncode != 0:
        detail = result.stderr.strip()
        raise AdapterError(
            f"worker exited with status {result.returncode}: {detail}"
        )
    if result.stderr:
        raise AdapterError("worker wrote unexpected stderr on success")

    return _parse_worker_output(
        kind, result.stdout, matrix["rows"], matrix["cols"]
    )


def _certificate(
    kind: str,
    input_matrix: dict[str, Any],
    matrices: dict[str, dict[str, Any]],
    generator: str = "normalforms-flint-cli",
) -> dict[str, Any]:
    if matrices["input"] != input_matrix:
        raise AdapterError("worker did not echo the caller's exact input")

    result: dict[str, Any] = {
        "schema": SCHEMA,
        "kind": kind,
        "input": input_matrix,
        "U": matrices["U"],
        "UInverse": matrices["UInverse"],
    }
    if kind == "hnf":
        result["H"] = matrices["H"]
    else:
        result["S"] = matrices["S"]
        result["V"] = matrices["V"]
        result["VInverse"] = matrices["VInverse"]

    canonical_payload = json.dumps(
        result, ensure_ascii=True, separators=(",", ":"), sort_keys=True
    ).encode("ascii")
    result["metadata"] = {
        "generator": generator,
        "flintVersion": FLINT_VERSION,
        "build": (
            f"gmp={GMP_VERSION};mpfr={MPFR_VERSION};"
            "link=dynamic;protocol=normalforms.decimal/v1"
        ),
        "hash": f"sha256:{hashlib.sha256(canonical_payload).hexdigest()}",
    }
    return result


def _write_json(path: str, value: dict[str, Any]) -> None:
    rendered = json.dumps(value, ensure_ascii=True, indent=2) + "\n"
    if path == "-":
        sys.stdout.write(rendered)
        return

    destination = Path(path)
    temporary = destination.with_name(f".{destination.name}.tmp-{os.getpid()}")
    try:
        temporary.write_text(rendered, encoding="utf-8")
        os.replace(temporary, destination)
    except OSError as error:
        try:
            temporary.unlink(missing_ok=True)
        except OSError:
            pass
        raise AdapterError(f"cannot write certificate: {error}") from error


def _positive_timeout(value: str) -> float:
    try:
        timeout = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("timeout must be a number") from error
    if not math.isfinite(timeout) or timeout <= 0:
        raise argparse.ArgumentTypeError("timeout must be positive")
    return timeout


def _argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Generate an untrusted normalforms.cert/v1 certificate with FLINT. "
            "Lean must still check the result."
        )
    )
    parser.add_argument("kind", choices=("hnf", "snf"))
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True)
    parser.add_argument("--worker", type=Path, default=_default_worker())
    parser.add_argument(
        "--generator",
        choices=("normalforms-flint-cli", "normalforms-flint-ffi"),
        default="normalforms-flint-cli",
        help="inert provenance label for the selected worker path",
    )
    parser.add_argument(
        "--timeout-seconds",
        type=_positive_timeout,
        default=300.0,
    )
    return parser


def main() -> int:
    arguments = _argument_parser().parse_args()
    try:
        matrix = _load_matrix(arguments.input)
        matrices = _run_worker(
            arguments.worker,
            arguments.kind,
            matrix,
            arguments.timeout_seconds,
        )
        _write_json(
            arguments.output,
            _certificate(
                arguments.kind,
                matrix,
                matrices,
                arguments.generator,
            ),
        )
    except AdapterError as error:
        print(f"normalforms-flint: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
