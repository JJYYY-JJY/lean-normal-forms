#!/usr/bin/env python3
"""One end-to-end FLINT generation, emission, and strict kernel import."""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys
import tempfile


def _run(command: list[str], repository: Path) -> None:
    result = subprocess.run(
        command,
        cwd=repository,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"{' '.join(command)} failed with status {result.returncode}: "
            f"{result.stderr.strip()}"
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worker", required=True, type=Path)
    parser.add_argument(
        "--generator",
        required=True,
        choices=("normalforms-flint-cli", "normalforms-flint-ffi"),
    )
    parser.add_argument("--input", required=True, type=Path)
    arguments = parser.parse_args()

    repository = Path(__file__).resolve().parents[1]
    wrapper = repository / "adapters" / "flint" / "python" / (
        "normalforms_flint.py"
    )
    checker = repository / ".lake" / "build" / "bin" / "normalforms-check"

    try:
        with tempfile.TemporaryDirectory(prefix="normalforms-c1-total-") as raw:
            temporary = Path(raw)
            certificate = temporary / "certificate.json"
            module = temporary / "CertificateImport.lean"
            _run(
                [
                    sys.executable,
                    str(wrapper),
                    "snf",
                    "--input",
                    str(arguments.input),
                    "--worker",
                    str(arguments.worker),
                    "--generator",
                    arguments.generator,
                    "--output",
                    str(certificate),
                ],
                repository,
            )
            _run(
                [
                    str(checker),
                    "emit-lean",
                    "--certificate",
                    str(certificate),
                    "--import",
                    "NormalForms.Tests.External.ExpectedMatrices",
                    "--matrix",
                    "NormalForms.Tests.External.benchmarkSmall",
                    "--theorem",
                    "NormalForms.Tests.External.c1TotalCertificate",
                    "--output",
                    str(module),
                ],
                repository,
            )
            _run(["lake", "env", "lean", str(module)], repository)
    except (OSError, RuntimeError) as error:
        print(f"normalforms-c1-total: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
