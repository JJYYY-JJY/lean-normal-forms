#!/usr/bin/env python3
"""Fixed-seed regression comparison for the FLINT CLI and Lean FFI paths."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Any, Callable

import normalforms_flint as adapter


MODULUS = 4_294_967_296


def _lcg(seed: int) -> Callable[[], int]:
    state = seed

    def next_value() -> int:
        nonlocal state
        state = (1_664_525 * state + 1_013_904_223) % MODULUS
        return state

    return next_value


def _matrix(rows: list[list[int]]) -> dict[str, Any]:
    row_count = len(rows)
    column_count = len(rows[0]) if rows else 0
    if any(len(row) != column_count for row in rows):
        raise ValueError("test matrix is not rectangular")
    return {
        "rows": row_count,
        "cols": column_count,
        "entries": [str(entry) for row in rows for entry in row],
    }


def _dense(seed: int, rows: int, columns: int) -> dict[str, Any]:
    sample = _lcg(seed)
    return _matrix(
        [
            [sample() % 41 - 20 for _ in range(columns)]
            for _ in range(rows)
        ]
    )


def _sparse(seed: int, rows: int, columns: int) -> dict[str, Any]:
    sample = _lcg(seed)
    values: list[list[int]] = []
    for _ in range(rows):
        row: list[int] = []
        for _ in range(columns):
            value = sample()
            row.append(value % 23 - 11 if value % 5 == 0 else 0)
        values.append(row)
    return _matrix(values)


def _rank_deficient(seed: int, columns: int) -> dict[str, Any]:
    sample = _lcg(seed)
    first = [sample() % 19 - 9 for _ in range(columns)]
    second = [sample() % 19 - 9 for _ in range(columns)]
    return _matrix(
        [
            first,
            second,
            [2 * value for value in first],
            [left - right for left, right in zip(first, second, strict=True)],
        ]
    )


def _invariant_factors(smith: dict[str, Any]) -> list[int]:
    rows = smith["rows"]
    columns = smith["cols"]
    entries = smith["entries"]
    factors: list[int] = []
    for index in range(min(rows, columns)):
        value = abs(int(entries[index * columns + index]))
        if value != 0:
            factors.append(value)
    return factors


def _argument_parser() -> argparse.ArgumentParser:
    repository = Path(__file__).resolve().parents[3]
    prefix = repository / ".lake" / "externals" / "prefix"
    parser = argparse.ArgumentParser(
        description=(
            "Compare normalized Smith invariant factors from the process and "
            "Lean FFI adapters. This is regression evidence, not a proof."
        )
    )
    parser.add_argument(
        "--cli-worker",
        type=Path,
        default=prefix / "bin" / "normalforms-flint-worker",
    )
    parser.add_argument(
        "--ffi-worker",
        type=Path,
        default=repository
        / ".lake"
        / "build"
        / "bin"
        / "normalforms-flint-ffi-worker",
    )
    parser.add_argument(
        "--timeout-seconds",
        type=adapter._positive_timeout,
        default=300.0,
    )
    return parser


def main() -> int:
    arguments = _argument_parser().parse_args()
    cases = [
        ("dense-wide", _dense(0x00C0FFEE, 3, 5)),
        ("dense-tall", _dense(0x12345678, 5, 3)),
        ("sparse-rectangular", _sparse(0x0BADF00D, 4, 6)),
        ("rank-deficient", _rank_deficient(0x5EED1234, 5)),
    ]
    try:
        for name, matrix in cases:
            cli = adapter._run_worker(
                arguments.cli_worker,
                "snf",
                matrix,
                arguments.timeout_seconds,
            )
            ffi = adapter._run_worker(
                arguments.ffi_worker,
                "snf",
                matrix,
                arguments.timeout_seconds,
            )
            cli_factors = _invariant_factors(cli["S"])
            ffi_factors = _invariant_factors(ffi["S"])
            if cli_factors != ffi_factors:
                raise adapter.AdapterError(
                    f"{name}: invariant factors differ: "
                    f"cli={cli_factors}, ffi={ffi_factors}"
                )
            print(f"{name}: {cli_factors}")
    except (adapter.AdapterError, OSError, ValueError) as error:
        print(f"normalforms-flint-differential: {error}", file=sys.stderr)
        return 2

    print(
        "FLINT CLI/FFI differential regression passed "
        "(normalized invariant factors only)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
