#!/usr/bin/env python3
"""Measure deterministic Lean allocation counters and advisory wall time."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BASELINE = ROOT / "benchmarks/baselines/v1.0.0-module-profile.json"
TRACE_THRESHOLD = 10_000
DEFAULT_MODULES = (
    "NormalForms/Euclidean/PolynomialRat.lean",
    "NormalForms/Matrix/Hermite/Algorithm.lean",
    "NormalForms/Matrix/Smith/Algorithm.lean",
    "NormalForms/Certificate/Checker.lean",
)


@dataclass(frozen=True)
class Measurement:
    module: str
    allocation_count: int
    heartbeats: float
    wall_seconds: float
    max_rss_kib: int

    def to_json(self) -> dict[str, object]:
        return {
            "module": self.module,
            "allocation_count": self.allocation_count,
            "heartbeats": self.heartbeats,
            "wall_seconds": self.wall_seconds,
            "max_rss_kib": self.max_rss_kib,
        }


def run_text(command: list[str]) -> str:
    result = subprocess.run(
        command,
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.stdout.strip()


def source_metadata() -> dict[str, object]:
    try:
        git_revision = run_text(["git", "rev-parse", "HEAD"])
        working_tree_clean: bool | None = not bool(
            run_text(["git", "status", "--porcelain", "--untracked-files=normal"])
        )
    except subprocess.CalledProcessError:
        # Release source archives and the core OCI context intentionally omit
        # `.git`; profiling remains meaningful without checkout metadata.
        git_revision = "unavailable"
        working_tree_clean = None
    return {
        "git_revision": git_revision,
        "working_tree_clean": working_tree_clean,
        "lean": run_text(["lake", "env", "lean", "--version"]),
        "machine": platform.machine(),
        "system": platform.system(),
    }


def traced_allocations(path: Path) -> int:
    profile = json.loads(path.read_text(encoding="utf-8"))
    threads = profile.get("threads")
    if not isinstance(threads, list) or not threads:
        raise RuntimeError("Lean profiler output has no threads")

    total = 0.0
    for thread in threads:
        if not isinstance(thread, dict):
            raise RuntimeError("Lean profiler thread is not an object")
        samples = thread.get("samples")
        if not isinstance(samples, dict):
            raise RuntimeError("Lean profiler thread has no samples")
        weights = samples.get("weight")
        if not isinstance(weights, list):
            raise RuntimeError("Lean profiler samples have no weights")
        values = weights
        if thread.get("isMainThread") is True:
            # Lean 4.32 brackets the main heartbeat trace with monotonic-clock
            # samples. Their cross-unit weights are not allocation counters.
            if len(values) < 3:
                raise RuntimeError("Lean profiler main thread is too short")
            values = values[2:-1]
        for value in values:
            if isinstance(value, (int, float)) and value > 0:
                total += value
    return round(total)


def measure(module: str) -> Measurement:
    path = ROOT / module
    if not path.is_file():
        raise RuntimeError(f"profile module does not exist: {module}")

    with tempfile.TemporaryDirectory(prefix="normalforms-profile-") as raw:
        temporary = Path(raw)
        profile = temporary / "profile.json"
        stdout = temporary / "stdout"
        stderr = temporary / "stderr"
        resource_report = temporary / "resources"
        command = [
            "/usr/bin/time",
            "-f",
            "%e %M",
            "-o",
            str(resource_report),
            "lake",
            "env",
            "lean",
            "-Dtrace.profiler=true",
            "-Dtrace.profiler.useHeartbeats=true",
            f"-Dtrace.profiler.threshold={TRACE_THRESHOLD}",
            f"-Dtrace.profiler.output={profile}",
            module,
        ]
        started = time.monotonic()
        with stdout.open("wb") as out, stderr.open("wb") as err:
            result = subprocess.run(command, cwd=ROOT, stdout=out, stderr=err)
        elapsed = time.monotonic() - started
        if result.returncode != 0:
            detail = stderr.read_text(encoding="utf-8", errors="replace")
            raise RuntimeError(f"Lean profiling failed for {module}:\n{detail}")

        fields = resource_report.read_text(encoding="utf-8").split()
        if len(fields) != 2:
            raise RuntimeError(f"invalid resource report for {module}")
        reported_wall = float(fields[0])
        max_rss_kib = int(fields[1])
        allocation_count = traced_allocations(profile)
        if allocation_count <= 0:
            raise RuntimeError(f"nonpositive allocation count for {module}")

    return Measurement(
        module=module,
        allocation_count=allocation_count,
        heartbeats=allocation_count / 1000,
        wall_seconds=max(reported_wall, round(elapsed, 2)),
        max_rss_kib=max_rss_kib,
    )


def make_report(modules: list[str]) -> dict[str, object]:
    measurements = []
    for module in modules:
        print(f"profiling {module}", file=sys.stderr, flush=True)
        measurements.append(measure(module).to_json())
    return {
        "schema": "normalforms.module-profile/v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "policy": {
            "allocation_failure_factor": 2.0,
            "wall_warning_factor": 3.0,
            "absolute_wall_failure": False,
            "trace_threshold": TRACE_THRESHOLD,
            "allocation_definition": (
                "sum of retained Lean 4.32 trace-profiler heartbeat intervals; "
                "one public heartbeat is 1000 small allocation increments"
            ),
        },
        "source": source_metadata(),
        "modules": measurements,
    }


def read_report(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError(f"{path} root is not an object")
    if value.get("schema") != "normalforms.module-profile/v1":
        raise RuntimeError(f"{path} has an unsupported schema")
    return value


def indexed_modules(report: dict[str, object]) -> dict[str, dict[str, object]]:
    modules = report.get("modules")
    if not isinstance(modules, list):
        raise RuntimeError("module profile has no module list")
    indexed: dict[str, dict[str, object]] = {}
    for row in modules:
        if not isinstance(row, dict) or not isinstance(row.get("module"), str):
            raise RuntimeError("module profile contains an invalid row")
        indexed[row["module"]] = row
    return indexed


def compare(
    baseline: dict[str, object],
    current: dict[str, object],
    allocation_factor: float,
    wall_factor: float,
) -> int:
    old = indexed_modules(baseline)
    new = indexed_modules(current)
    failures: list[str] = []
    warnings: list[str] = []
    for module, row in new.items():
        if module not in old:
            failures.append(f"no baseline for {module}")
            continue
        old_row = old[module]
        old_alloc = int(old_row["allocation_count"])
        new_alloc = int(row["allocation_count"])
        old_wall = float(old_row["wall_seconds"])
        new_wall = float(row["wall_seconds"])
        allocation_ratio = new_alloc / old_alloc
        wall_ratio = new_wall / old_wall
        print(
            f"{module}: allocations={new_alloc} "
            f"ratio={allocation_ratio:.3f} wall={new_wall:.2f}s "
            f"ratio={wall_ratio:.3f}"
        )
        if allocation_ratio > allocation_factor:
            failures.append(
                f"{module} allocation ratio {allocation_ratio:.3f} "
                f"exceeds {allocation_factor:.3f}"
            )
        if wall_ratio > wall_factor:
            warnings.append(
                f"{module} wall ratio {wall_ratio:.3f} "
                f"exceeds advisory {wall_factor:.3f}"
            )
    for warning in warnings:
        print(f"warning: {warning}", file=sys.stderr)
    for failure in failures:
        print(f"error: {failure}", file=sys.stderr)
    return 1 if failures else 0


def write_report(path: Path, report: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument("--write-baseline", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--module", action="append", dest="modules")
    parser.add_argument("--allocation-factor", type=float, default=2.0)
    parser.add_argument("--wall-warning-factor", type=float, default=3.0)
    args = parser.parse_args()

    modules = args.modules or list(DEFAULT_MODULES)
    try:
        report = make_report(modules)
        if args.report is not None:
            write_report(args.report, report)
        if args.write_baseline is not None:
            write_report(args.write_baseline, report)
            print(f"module profile baseline written: {args.write_baseline}")
            return 0
        baseline = read_report(args.baseline)
        return compare(
            baseline,
            report,
            args.allocation_factor,
            args.wall_warning_factor,
        )
    except (OSError, RuntimeError, subprocess.CalledProcessError, ValueError) as error:
        print(f"module profiling failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
