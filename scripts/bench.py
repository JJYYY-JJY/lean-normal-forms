#!/usr/bin/env python3
"""Run explicit, reproducible benchmark profiles.

Timing, source and host fingerprints, summary statistics, and CSV emission
are shared here.  Each profile keeps its own parser, deterministic checks,
schema, report fields, and trust statement.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import sys
import tempfile
import time
import tomllib
from typing import Any, Callable, Iterable


ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "build" / "benchmarks"
TIME_EXECUTABLE = Path("/usr/bin/time")
TIME_FORMAT = "\n".join(
    [
        "wall_seconds=%e",
        "maximum_rss_kib=%M",
        "user_seconds=%U",
        "system_seconds=%S",
        "exit_status=%x",
    ]
)
OBSERVATION_FIELDS = (
    "wall_seconds",
    "maximum_rss_kib",
    "user_seconds",
    "system_seconds",
)


def run(
    command: list[str],
    *,
    capture: bool = False,
    env: dict[str, str] | None = None,
) -> str:
    result = subprocess.run(
        command,
        cwd=ROOT,
        env=env,
        stdout=subprocess.PIPE if capture else subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if result.returncode != 0:
        details = result.stderr.strip()
        if capture and result.stdout.strip():
            details = f"{details}\n{result.stdout.strip()}".strip()
        raise RuntimeError(
            f"{' '.join(command)} failed with status {result.returncode}: "
            f"{details}"
        )
    return result.stdout.strip() if capture else ""


def measure(
    command: list[str],
    timing_file: Path,
    *,
    capture_stdout: bool,
) -> tuple[dict[str, float | int], str, int]:
    start = time.perf_counter_ns()
    result = subprocess.run(
        [
            str(TIME_EXECUTABLE),
            "-o",
            str(timing_file),
            "-f",
            TIME_FORMAT,
            "--",
            *command,
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE if capture_stdout else subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    elapsed_ns = time.perf_counter_ns() - start
    if result.returncode != 0:
        details = result.stderr.strip()
        if capture_stdout and result.stdout.strip():
            details = f"{details}\n{result.stdout.strip()}".strip()
        raise RuntimeError(
            f"{' '.join(command)} failed with status {result.returncode}: "
            f"{details}"
        )
    values: dict[str, str] = {}
    for line in timing_file.read_text(encoding="utf-8").splitlines():
        key, separator, value = line.partition("=")
        if separator:
            values[key] = value
    if values.get("exit_status") != "0":
        raise RuntimeError(f"time reported a failed command: {values}")
    observation: dict[str, float | int] = {
        "wall_seconds": float(values["wall_seconds"]),
        "maximum_rss_kib": int(values["maximum_rss_kib"]),
        "user_seconds": float(values["user_seconds"]),
        "system_seconds": float(values["system_seconds"]),
    }
    return observation, result.stdout if capture_stdout else "", elapsed_ns


def summary(values: Iterable[float | int]) -> dict[str, float]:
    ordered = sorted(float(value) for value in values)
    q1, _, q3 = statistics.quantiles(ordered, n=4, method="inclusive")
    return {
        "median": statistics.median(ordered),
        "q1": q1,
        "q3": q3,
        "iqr": q3 - q1,
        "minimum": ordered[0],
        "maximum": ordered[-1],
    }


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def source_fingerprint() -> dict[str, object]:
    revision = run(["git", "rev-parse", "HEAD"], capture=True)
    tracked = run(
        ["git", "diff", "--no-ext-diff", "--binary", "HEAD"], capture=True
    )
    staged = run(
        ["git", "diff", "--cached", "--no-ext-diff", "--binary", "HEAD"],
        capture=True,
    )
    status = run(["git", "status", "--short"], capture=True)
    patch_hash = hashlib.sha256(
        (tracked + "\n" + staged).encode("utf-8")
    ).hexdigest()
    return {
        "git_revision": revision,
        "working_tree_clean": status == "",
        "tracked_patch_sha256": patch_hash,
    }


KANNAN_BACHEM_SOURCE_MANIFEST = (
    ROOT / "artifact" / "kannan-bachem" / "source-manifest.txt"
)


def profile_source_fingerprint(manifest: Path) -> dict[str, object]:
    patterns = [
        line.strip()
        for line in manifest.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    files: set[Path] = set()
    for pattern in patterns:
        matches = [path for path in ROOT.glob(pattern) if path.is_file()]
        if not matches:
            raise RuntimeError(f"source-manifest pattern matched no files: {pattern}")
        files.update(matches)
    ordered = sorted(files, key=lambda path: path.relative_to(ROOT).as_posix())
    digest = hashlib.sha256()
    for path in ordered:
        relative_bytes = path.relative_to(ROOT).as_posix().encode("utf-8")
        content = path.read_bytes()
        digest.update(len(relative_bytes).to_bytes(8, "big"))
        digest.update(relative_bytes)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return {
        "profile_source_sha256": digest.hexdigest(),
        "profile_source_file_count": len(ordered),
    }


def source_commit() -> str:
    fingerprint = source_fingerprint()
    return str(fingerprint["git_revision"]) + (
        "" if fingerprint["working_tree_clean"] else "-dirty"
    )


def cpu_model() -> str:
    try:
        for line in Path("/proc/cpuinfo").read_text(
            encoding="utf-8"
        ).splitlines():
            if line.startswith("model name"):
                return line.partition(":")[2].strip()
    except OSError:
        pass
    return platform.processor() or "unknown"


def memory_total_kib() -> int | None:
    try:
        for line in Path("/proc/meminfo").read_text(
            encoding="utf-8"
        ).splitlines():
            if line.startswith("MemTotal:"):
                return int(line.split()[1])
    except (OSError, ValueError, IndexError):
        pass
    return None


def hardware_fingerprint() -> dict[str, object]:
    return {
        "system": platform.system(),
        "release": platform.release(),
        "machine": platform.machine(),
        "cpu_model": cpu_model(),
        "logical_cpus": os.cpu_count(),
        "memory_total_kib": memory_total_kib(),
        "libc": list(platform.libc_ver()),
        "python": platform.python_version(),
        "lean": run(["lean", "--version"], capture=True),
    }


def bit_cost_hardware_fingerprint() -> dict[str, object]:
    return {
        "cpu": cpu_model(),
        "logicalCpus": os.cpu_count(),
        "machine": platform.machine(),
        "kernel": platform.release(),
        "platform": platform.platform(),
        "python": platform.python_version(),
    }


def policy(warmups: int, measurements: int) -> dict[str, object]:
    return {
        "warmups": warmups,
        "measurements": measurements,
        "hosted_ci_absolute_time_gate": False,
        "comparison_requires_identical_hardware_fingerprint": True,
        "summary_method": "median and inclusive quartiles",
    }


def resolve(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def output_paths(prefix: Path) -> tuple[Path, Path]:
    resolved = resolve(prefix)
    return Path(f"{resolved}.json"), Path(f"{resolved}.csv")


def write_json(path: Path, report: dict[str, object], *, sort_keys: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(report, indent=2, sort_keys=sort_keys) + "\n",
        encoding="utf-8",
    )


def write_csv(
    path: Path,
    fields: list[str],
    rows: Iterable[dict[str, object]],
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as output:
        writer = csv.DictWriter(output, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row.get(field, "") for field in fields})


def summarize_observations(
    observations: list[dict[str, float | int]],
) -> dict[str, dict[str, float]]:
    return {
        metric: summary(observation[metric] for observation in observations)
        for metric in OBSERVATION_FIELDS
    }


def parse_scalar(raw: str, *, comma_lists: bool) -> object:
    if raw == "true":
        return True
    if raw == "false":
        return False
    if comma_lists and "," in raw:
        try:
            return [int(value) for value in raw.split(",")]
        except ValueError:
            return raw
    try:
        return int(raw)
    except ValueError:
        return raw


def parse_case_blocks(
    output: str, *, comma_lists: bool
) -> list[dict[str, object]]:
    cases: list[dict[str, object]] = []
    current: dict[str, object] | None = None
    for line in output.splitlines():
        key, separator, raw = line.partition("=")
        if not separator:
            continue
        if key == "case":
            if current is not None:
                cases.append(current)
            current = {"case": raw}
        elif current is not None:
            current[key] = parse_scalar(raw, comma_lists=comma_lists)
            if key == "valid":
                cases.append(current)
                current = None
    if current is not None:
        cases.append(current)
    if not cases or any(case.get("valid") is not True for case in cases):
        raise RuntimeError(f"benchmark cases are incomplete or invalid:\n{output}")
    return cases


def parse_kannan_bachem_cases(output: str) -> list[dict[str, object]]:
    cases = parse_case_blocks(output, comma_lists=True)
    required = {
        "case",
        "dimension",
        "input_bits",
        "determinant_bits",
        "input_encoding_bits",
        "additions",
        "multiplications",
        "xgcd_calls",
        "normalizations",
        "standalone_divmod_calls",
        "arithmetic_operation_total",
        "result_bits",
        "left_bits",
        "left_inverse_bits",
        "right_bits",
        "right_inverse_bits",
        "passes",
        "injections",
        "bit_cost",
        "bit_bound",
        "diagonal",
        "valid",
    }
    for case in cases:
        if not required.issubset(case):
            raise RuntimeError(f"benchmark case lacks metrics: {case}")
        if str(case["case"]).startswith("smith-") and (
            "output_encoding_bits" not in case
        ):
            raise RuntimeError(f"Smith case lacks output encoding length: {case}")
        if int(case["bit_cost"]) > int(case["bit_bound"]):
            raise RuntimeError(f"modeled cost exceeds bound: {case}")
    return cases


def parse_modular_hnf_cases(output: str) -> list[dict[str, object]]:
    cases = parse_case_blocks(output, comma_lists=True)
    required = {
        "case",
        "rows",
        "columns",
        "input_bits",
        "modulus_bits",
        "stages",
        "additions",
        "multiplications",
        "xgcd_calls",
        "exact_divisions",
        "modular_reductions",
        "comparisons",
        "operation_total",
        "operation_bound",
        "intermediate_height_bits",
        "result_bits",
        "modeled_bit_cost_bits",
        "modeled_bit_bound_bits",
        "valid",
    }
    for case in cases:
        if not required.issubset(case):
            raise RuntimeError(f"benchmark case lacks metrics: {case}")
        if int(case["operation_total"]) > int(case["operation_bound"]):
            raise RuntimeError(f"operation count exceeds bound: {case}")
        if int(case["modeled_bit_cost_bits"]) > int(
            case["modeled_bit_bound_bits"]
        ):
            raise RuntimeError(f"modeled bit-cost width exceeds bound: {case}")
    return cases


def parse_lll_cases(output: str) -> list[dict[str, object]]:
    cases = parse_case_blocks(output, comma_lists=False)
    common = {
        "case",
        "kind",
        "rows",
        "columns",
        "rank",
        "input_bits",
        "result_bits",
        "strong_result",
        "valid",
    }
    profiled = {
        "fuel",
        "size_reductions",
        "swaps",
        "refreshes",
        "operation_total",
        "operation_bound",
        "intermediate_coefficient_bits",
        "modeled_bit_cost",
        "modeled_bit_bound",
    }
    for case in cases:
        if not common.issubset(case):
            raise RuntimeError(f"benchmark case lacks common metrics: {case}")
        if case["kind"] == "profiled-full-rank":
            if not profiled.issubset(case):
                raise RuntimeError(f"profiled case lacks cost metrics: {case}")
            if int(case["operation_total"]) > int(case["operation_bound"]):
                raise RuntimeError(f"operation count exceeds bound: {case}")
            if int(case["modeled_bit_cost"]) > int(case["modeled_bit_bound"]):
                raise RuntimeError(f"modeled bit cost exceeds bound: {case}")
    return cases


@dataclass(frozen=True)
class Stage:
    id: str
    description: str
    mode: str
    case_names: tuple[str, ...]


@dataclass(frozen=True)
class StructuredProfile:
    build_target: str
    binary_name: str
    profile: str
    schema: str
    research_version: str
    expected_cases: tuple[str, ...]
    stages: tuple[Stage, ...]
    parser: Callable[[str], list[dict[str, object]]]
    csv_fields: tuple[str, ...]
    trust_boundary: str


KANNAN_BACHEM = StructuredProfile(
    build_target="normalforms-kannan-bachem-benchmark",
    binary_name="normalforms-kannan-bachem-benchmark",
    profile="research-kannan-bachem-v0.2.0-dev",
    schema="normalforms.kannan-bachem-benchmark/v2",
    research_version="0.2.0-dev",
    expected_cases=(
        "hnf-prepared-3x3",
        "smith-repeat-2x2",
        "smith-injection-2x2",
    ),
    stages=(
        Stage(
            "prepared_hnf",
            "prepared principal-minor HNF on a 3-by-3 input",
            "hnf",
            ("hnf-prepared-3x3",),
        ),
        Stage(
            "smith_repeat",
            "Smith stabilization with a repeated pass",
            "smith-repeat",
            ("smith-repeat-2x2",),
        ),
        Stage(
            "smith_injection",
            "Smith stabilization through Step 7 injection",
            "smith-injection",
            ("smith-injection-2x2",),
        ),
        Stage(
            "end_to_end",
            "all three deterministic research cases",
            "all",
            (
                "hnf-prepared-3x3",
                "smith-repeat-2x2",
                "smith-injection-2x2",
            ),
        ),
    ),
    parser=parse_kannan_bachem_cases,
    csv_fields=(
        "stage",
        "iteration",
        "wall_seconds",
        "maximum_rss_kib",
        "user_seconds",
        "system_seconds",
        "case",
        "dimension",
        "input_bits",
        "determinant_bits",
        "input_encoding_bits",
        "arithmetic_operation_total",
        "additions",
        "multiplications",
        "xgcd_calls",
        "normalizations",
        "standalone_divmod_calls",
        "passes",
        "injections",
        "result_bits",
        "left_bits",
        "left_inverse_bits",
        "right_bits",
        "right_inverse_bits",
        "bit_cost",
        "bit_bound",
        "output_encoding_bits",
    ),
    trust_boundary=(
        "Native time and RSS are observational regression evidence. "
        "Kernel-checked theorems establish normal-form correctness, concrete "
        "encoding-length bounds, and the leaf-trace binary arithmetic cost. "
        "Decoding, serialization, storage, traversal, allocation, and native "
        "runtime costs are excluded."
    ),
)


MODULAR_HNF = StructuredProfile(
    build_target="normalforms-modular-hnf-benchmark",
    binary_name="normalforms-modular-hnf-benchmark",
    profile="research-modular-hnf-v0.1.0",
    schema="normalforms.modular-hnf-benchmark/v1",
    research_version="0.1.0",
    expected_cases=("scalar-1x1", "tall-2x1", "square-2x2"),
    stages=(
        Stage(
            "scalar",
            "one-column scalar determinant-modulus run",
            "scalar",
            ("scalar-1x1",),
        ),
        Stage(
            "tall",
            "rectangular full-column-rank run",
            "tall",
            ("tall-2x1",),
        ),
        Stage(
            "square",
            "two-column determinant-modulus run",
            "square",
            ("square-2x2",),
        ),
        Stage(
            "end_to_end",
            "all three deterministic modular-HNF cases",
            "all",
            ("scalar-1x1", "tall-2x1", "square-2x2"),
        ),
    ),
    parser=parse_modular_hnf_cases,
    csv_fields=(
        "stage",
        "iteration",
        "wall_seconds",
        "maximum_rss_kib",
        "user_seconds",
        "system_seconds",
        "case",
        "rows",
        "columns",
        "input_bits",
        "modulus_bits",
        "stages",
        "operation_total",
        "operation_bound",
        "xgcd_calls",
        "intermediate_height_bits",
        "result_bits",
        "modeled_bit_cost_bits",
        "modeled_bit_bound_bits",
    ),
    trust_boundary=(
        "Native time and RSS are observational regression evidence. "
        "Kernel-checked theorems establish normal-form correctness, operation "
        "bounds, coefficient bounds, the standard-XGCD mirror, and modeled "
        "bit cost."
    ),
)


LLL = StructuredProfile(
    build_target="normalforms-lll-smoke",
    binary_name="normalforms-lll-smoke",
    profile="research-lll-v0.1.0",
    schema="normalforms.lll-benchmark/v1",
    research_version="0.1.0",
    expected_cases=(
        "gauss-2x2",
        "dense-3x3",
        "dependent-3x3",
        "column-3x3",
    ),
    stages=(
        Stage(
            "gauss",
            "profiled two-row Gaussian reduction",
            "gauss",
            ("gauss-2x2",),
        ),
        Stage(
            "dense",
            "profiled dense three-row reduction",
            "dense",
            ("dense-3x3",),
        ),
        Stage(
            "dependent",
            "total rank-deficient row wrapper",
            "dependent",
            ("dependent-3x3",),
        ),
        Stage(
            "column",
            "transpose-only total column adapter",
            "column",
            ("column-3x3",),
        ),
        Stage(
            "end_to_end",
            "all deterministic LLL cases",
            "all",
            (
                "gauss-2x2",
                "dense-3x3",
                "dependent-3x3",
                "column-3x3",
            ),
        ),
    ),
    parser=parse_lll_cases,
    csv_fields=(
        "stage",
        "iteration",
        "wall_seconds",
        "maximum_rss_kib",
        "user_seconds",
        "system_seconds",
        "case",
        "kind",
        "rows",
        "columns",
        "rank",
        "input_bits",
        "result_bits",
        "fuel",
        "size_reductions",
        "swaps",
        "refreshes",
        "operation_total",
        "operation_bound",
        "intermediate_coefficient_bits",
        "modeled_bit_cost",
        "modeled_bit_bound",
    ),
    trust_boundary=(
        "Native time and RSS are observational regression evidence. "
        "Kernel-checked theorems establish strong row/column results, the "
        "tracked-event bound, intermediate coefficient evidence, and the "
        "profile-dependent sign-magnitude reference budget. The cost claim "
        "excludes HNF rank decomposition and is not an input-only polynomial "
        "bound."
    ),
)


def run_structured_profile(
    arguments: argparse.Namespace, profile: StructuredProfile
) -> int:
    binary = ROOT / ".lake" / "build" / "bin" / profile.binary_name
    if not arguments.skip_build:
        run(["lake", "build", profile.build_target])
    if not binary.is_file():
        raise RuntimeError(f"missing benchmark executable: {binary}")

    fixed_cases = profile.parser(run([str(binary), "all"], capture=True))
    if tuple(str(case["case"]) for case in fixed_cases) != profile.expected_cases:
        raise RuntimeError("the fixed benchmark corpus changed")

    stages: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(
        prefix=f"normalforms-{profile.binary_name}-"
    ) as raw_directory:
        temporary = Path(raw_directory)
        for stage_spec in profile.stages:
            expected = [
                case
                for case in fixed_cases
                if case["case"] in stage_spec.case_names
            ]
            command = [str(binary), stage_spec.mode]
            for warmup in range(arguments.warmups):
                _, stdout, _ = measure(
                    command,
                    temporary / f"{stage_spec.id}-warmup-{warmup}.time",
                    capture_stdout=True,
                )
                if profile.parser(stdout) != expected:
                    raise RuntimeError(f"{stage_spec.id} warmup metrics drifted")
            observations: list[dict[str, float | int]] = []
            for iteration in range(arguments.measurements):
                observation, stdout, _ = measure(
                    command,
                    temporary / f"{stage_spec.id}-{iteration}.time",
                    capture_stdout=True,
                )
                if profile.parser(stdout) != expected:
                    raise RuntimeError(f"{stage_spec.id} metrics drifted")
                observation["iteration"] = iteration + 1
                observations.append(observation)
            stages.append(
                {
                    "id": stage_spec.id,
                    "description": stage_spec.description,
                    "case_names": list(stage_spec.case_names),
                    "observations": observations,
                    "summary": summarize_observations(observations),
                }
            )

    source = source_fingerprint()
    if profile.profile == KANNAN_BACHEM.profile:
        source.update(profile_source_fingerprint(KANNAN_BACHEM_SOURCE_MANIFEST))
    report: dict[str, object] = {
        "schema": profile.schema,
        "profile": profile.profile,
        "research_version": profile.research_version,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "policy": policy(arguments.warmups, arguments.measurements),
        "cases": fixed_cases,
        "hardware": hardware_fingerprint(),
        "source": source,
        "binary_sha256": sha256(binary),
        "stages": stages,
        "trust_boundary": profile.trust_boundary,
    }
    json_path, csv_path = output_paths(arguments.output_prefix)
    write_json(json_path, report, sort_keys=True)
    cases_by_name = {str(case["case"]): case for case in fixed_cases}
    rows: list[dict[str, object]] = []
    for stage in stages:
        for observation in stage["observations"]:  # type: ignore[union-attr]
            for case_name in stage["case_names"]:  # type: ignore[union-attr]
                rows.append(
                    {
                        "stage": stage["id"],
                        **observation,
                        **cases_by_name[str(case_name)],
                    }
                )
    write_csv(csv_path, list(profile.csv_fields), rows)
    print(json_path)
    print(csv_path)
    return 0


def parse_rational_canonical_metrics(output: str) -> dict[str, object]:
    values: dict[str, str] = {}
    for line in output.splitlines():
        key, separator, value = line.partition("=")
        if separator:
            values[key] = value
    if values.get("valid") != "true":
        raise RuntimeError(f"benchmark did not report valid=true: {output}")
    required = {
        "factor_degrees",
        "maximum_input_coefficient_bits",
        "maximum_factor_coefficient_bits",
        "companion_repetitions",
    }
    if not required.issubset(values):
        raise RuntimeError(f"benchmark metrics are incomplete: {output}")
    metrics: dict[str, object] = {
        "factor_degrees": [
            int(value) for value in values["factor_degrees"].split(",") if value
        ],
        "maximum_input_coefficient_bits": int(
            values["maximum_input_coefficient_bits"]
        ),
        "maximum_factor_coefficient_bits": int(
            values["maximum_factor_coefficient_bits"]
        ),
        "companion_repetitions": int(values["companion_repetitions"]),
    }
    if "companion_nanoseconds" in values:
        metrics["companion_batch_nanoseconds"] = int(
            values["companion_nanoseconds"]
        )
    return metrics


def run_rational_canonical(arguments: argparse.Namespace) -> int:
    binary = ROOT / ".lake/build/bin/normalforms-rational-canonical-benchmark"
    if not arguments.skip_build:
        run(["lake", "build", "normalforms-rational-canonical-benchmark"])
    if not binary.is_file():
        raise RuntimeError(f"missing benchmark executable: {binary}")

    deterministic_metrics = parse_rational_canonical_metrics(
        run([str(binary), "total"], capture=True)
    )
    stage_specs = (
        (
            "invariant_generation",
            "choice-free polynomial Smith generation and factor checks",
            "invariants",
        ),
        (
            "companion_verification",
            "1000 structural companion-block checks after factor setup",
            "companion",
        ),
        (
            "end_to_end",
            "factor generation plus one companion-block verification",
            "total",
        ),
    )
    stages: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(
        prefix="normalforms-rational-canonical-benchmark-"
    ) as raw_directory:
        temporary = Path(raw_directory)
        for stage_id, description, mode in stage_specs:
            command = [str(binary), mode]
            for warmup in range(arguments.warmups):
                _, stdout, _ = measure(
                    command,
                    temporary / f"{stage_id}-warmup-{warmup}.time",
                    capture_stdout=True,
                )
                parse_rational_canonical_metrics(stdout)
            observations: list[dict[str, float | int]] = []
            companion_batches: list[int] = []
            for iteration in range(arguments.measurements):
                observation, stdout, _ = measure(
                    command,
                    temporary / f"{stage_id}-{iteration}.time",
                    capture_stdout=True,
                )
                metrics = parse_rational_canonical_metrics(stdout)
                observation["iteration"] = iteration + 1
                if "companion_batch_nanoseconds" in metrics:
                    batch = int(metrics["companion_batch_nanoseconds"])
                    repetitions = int(metrics["companion_repetitions"])
                    observation["companion_batch_nanoseconds"] = batch
                    observation["companion_per_check_nanoseconds"] = (
                        batch / repetitions
                    )
                    companion_batches.append(batch)
                observations.append(observation)
            stage_summary: dict[str, object] = summarize_observations(observations)
            if companion_batches:
                batch_summary = summary(companion_batches)
                stage_summary["isolated_companion_batch_nanoseconds"] = (
                    batch_summary
                )
                repetitions = int(deterministic_metrics["companion_repetitions"])
                stage_summary["isolated_companion_per_check_nanoseconds"] = {
                    key: value / repetitions for key, value in batch_summary.items()
                }
            stages.append(
                {
                    "id": stage_id,
                    "description": description,
                    "observations": observations,
                    "summary": stage_summary,
                }
            )

    report: dict[str, object] = {
        "schema": "normalforms.benchmark/v1",
        "profile": "v1.1.0-rational-canonical",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "policy": policy(arguments.warmups, arguments.measurements),
        "case": {
            "name": "rational-jordan-2x2",
            "rows": 2,
            "cols": 2,
            **deterministic_metrics,
        },
        "instrumentation": {
            "ring_operation_count": None,
            "pivot_count": None,
            "gcd_count": None,
            "status": (
                "not exposed by the executable kernel; formal operation "
                "telemetry belongs to the independent bit-cost line"
            ),
        },
        "hardware": hardware_fingerprint(),
        "source": source_fingerprint(),
        "stages": stages,
        "trust_boundary": (
            "This native profile is observational regression evidence. The "
            "application theorems, not benchmark success, establish rational "
            "canonical correctness."
        ),
    }
    json_path, csv_path = output_paths(arguments.output_prefix)
    write_json(json_path, report, sort_keys=True)
    case = report["case"]
    rows = []
    for stage in stages:
        for observation in stage["observations"]:  # type: ignore[union-attr]
            rows.append(
                {
                    "stage": stage["id"],
                    **observation,
                    "factor_degrees": ",".join(
                        str(value) for value in case["factor_degrees"]  # type: ignore[index]
                    ),
                    "maximum_input_coefficient_bits": case[
                        "maximum_input_coefficient_bits"  # type: ignore[index]
                    ],
                    "maximum_factor_coefficient_bits": case[
                        "maximum_factor_coefficient_bits"  # type: ignore[index]
                    ],
                }
            )
    write_csv(
        csv_path,
        [
            "stage",
            "iteration",
            "wall_seconds",
            "maximum_rss_kib",
            "user_seconds",
            "system_seconds",
            "companion_batch_nanoseconds",
            "companion_per_check_nanoseconds",
            "factor_degrees",
            "maximum_input_coefficient_bits",
            "maximum_factor_coefficient_bits",
        ],
        rows,
    )
    print(json_path)
    print(csv_path)
    return 0


def parse_bit_cost_cases(stdout: str) -> list[dict[str, object]]:
    cases: list[dict[str, object]] = []
    for line in stdout.splitlines():
        if not line.startswith("operation="):
            continue
        row: dict[str, object] = {}
        for field in line.split():
            key, value = field.split("=", 1)
            if value in ("true", "false"):
                row[key] = value == "true"
            else:
                try:
                    row[key] = int(value)
                except ValueError:
                    row[key] = value
        cases.append(row)
    if len(cases) != 13 or any(case.get("valid") is not True for case in cases):
        raise RuntimeError("native bit-cost corpus did not validate all 13 cases")
    if "cases=13\n" not in stdout or not stdout.endswith("valid=true\n"):
        raise RuntimeError("native bit-cost summary is incomplete")
    return cases


def run_bit_cost(arguments: argparse.Namespace) -> int:
    binary = ROOT / ".lake/build/bin/normalforms-bit-cost-benchmark"
    if not arguments.skip_build:
        run(["lake", "build", "normalforms-bit-cost-benchmark"])
    if not binary.is_file():
        raise RuntimeError(f"missing benchmark executable: {binary}")

    measurements: list[dict[str, int]] = []
    cases: list[dict[str, object]] | None = None
    with tempfile.TemporaryDirectory(
        prefix="normalforms-bit-cost-benchmark-"
    ) as raw_directory:
        temporary = Path(raw_directory)
        for warmup in range(arguments.warmups):
            _, stdout, _ = measure(
                [str(binary)],
                temporary / f"warmup-{warmup}.time",
                capture_stdout=True,
            )
            parse_bit_cost_cases(stdout)
        for iteration in range(arguments.measurements):
            observation, stdout, elapsed_ns = measure(
                [str(binary)],
                temporary / f"measurement-{iteration}.time",
                capture_stdout=True,
            )
            observed = parse_bit_cost_cases(stdout)
            if cases is None:
                cases = observed
            elif observed != cases:
                raise RuntimeError(
                    "fixed bit-cost case output changed between measurements"
                )
            measurements.append(
                {
                    "wall_ns": elapsed_ns,
                    "max_rss_kib": int(observation["maximum_rss_kib"]),
                }
            )
    if cases is None:
        raise RuntimeError("bit-cost benchmark produced no measurements")
    wall = [measurement["wall_ns"] for measurement in measurements]
    rss = [measurement["max_rss_kib"] for measurement in measurements]
    wall_q1, _, wall_q3 = statistics.quantiles(
        wall, n=4, method="inclusive"
    )
    rss_q1, _, rss_q3 = statistics.quantiles(
        rss, n=4, method="inclusive"
    )
    report: dict[str, object] = {
        "schema": "normalforms.bit-cost-benchmark/v1",
        "researchVersion": "0.1.0",
        "sourceCommit": source_commit(),
        "binarySha256": sha256(binary),
        "warmups": arguments.warmups,
        "measurementCount": arguments.measurements,
        "hardware": bit_cost_hardware_fingerprint(),
        "measurements": measurements,
        "summary": {
            "wall_ns_median": statistics.median(wall),
            "wall_ns_iqr": wall_q3 - wall_q1,
            "max_rss_kib_median": statistics.median(rss),
            "max_rss_kib_iqr": rss_q3 - rss_q1,
        },
        "cases": cases,
        "interpretation": (
            "Native wall time is experimental. Formal claims use the modeled "
            "cost, coefficient_bound, and proved bound fields."
        ),
    }
    json_path, csv_path = output_paths(arguments.output_prefix)
    write_json(json_path, report, sort_keys=False)
    rows: list[dict[str, object]] = []
    for index, measurement in enumerate(measurements):
        rows.append({"record": "measurement", "index": index, **measurement})
    for index, case in enumerate(cases):
        rows.append({"record": "case", "index": index, **case})
    write_csv(
        csv_path,
        [
            "record",
            "index",
            "wall_ns",
            "max_rss_kib",
            "operation",
            "left",
            "right",
            "value",
            "quotient",
            "remainder",
            "gcd",
            "left_coeff",
            "right_coeff",
            "cost",
            "coefficient_bound",
            "bound",
            "valid",
        ],
        rows,
    )
    print(json_path)
    print(csv_path)
    return 0


def max_integer_bits(value: Any) -> int:
    if isinstance(value, dict):
        return max((max_integer_bits(item) for item in value.values()), default=0)
    if isinstance(value, list):
        return max((max_integer_bits(item) for item in value), default=0)
    if isinstance(value, str) and re.fullmatch(r"-?(?:0|[1-9][0-9]*)", value):
        return abs(int(value)).bit_length()
    return 0


def write_certificate(worker: Path, generator: str, destination: Path) -> None:
    run(
        [
            sys.executable,
            str(ROOT / "adapters/flint/python/normalforms_flint.py"),
            "snf",
            "--input",
            str(ROOT / "Tests/Certificate/flint/benchmark-small.json"),
            "--worker",
            str(worker),
            "--generator",
            generator,
            "--output",
            str(destination),
        ]
    )


def run_certificate_paths(arguments: argparse.Namespace) -> int:
    prefix = ROOT / ".lake/externals/prefix"
    cli_worker = prefix / "bin/normalforms-flint-worker"
    ffi_worker = ROOT / ".lake/build/bin/normalforms-flint-ffi-worker"
    native_benchmark = ROOT / ".lake/build/bin/normalforms-certificate-benchmark"
    checker = ROOT / ".lake/build/bin/normalforms-check"
    input_path = ROOT / "Tests/Certificate/flint/benchmark-small.json"
    wrapper = ROOT / "adapters/flint/python/normalforms_flint.py"
    total = ROOT / "benchmarks/c1_total.py"

    if not arguments.skip_build:
        environment = os.environ.copy()
        environment["NORMALFORMS_FLINT_BUILD_LEAN_FFI"] = "1"
        result = subprocess.run(
            [str(ROOT / "scripts/BuildFlintAdapter.sh")],
            cwd=ROOT,
            env=environment,
            check=False,
        )
        if result.returncode != 0:
            raise RuntimeError(
                "scripts/BuildFlintAdapter.sh failed with status "
                f"{result.returncode}"
            )
        run(
            [
                "lake",
                "build",
                "normalforms-check",
                "normalforms-certificate-benchmark",
                "normalforms-flint-ffi-worker",
            ]
        )
    for required in (
        cli_worker,
        ffi_worker,
        native_benchmark,
        checker,
        input_path,
        wrapper,
        total,
    ):
        if not required.is_file():
            raise RuntimeError(f"missing benchmark dependency: {required}")

    with tempfile.TemporaryDirectory(
        prefix="normalforms-certificate-paths-benchmark-"
    ) as raw_directory:
        temporary = Path(raw_directory)
        cli_certificate = temporary / "cli.json"
        ffi_certificate = temporary / "ffi.json"
        generated_module = temporary / "KernelCheck.lean"
        write_certificate(
            cli_worker, "normalforms-flint-cli", cli_certificate
        )
        write_certificate(
            ffi_worker, "normalforms-flint-ffi", ffi_certificate
        )
        run(
            [
                str(checker),
                "emit-lean",
                "--certificate",
                str(cli_certificate),
                "--import",
                "NormalForms.Tests.External.ExpectedMatrices",
                "--matrix",
                "NormalForms.Tests.External.benchmarkSmall",
                "--theorem",
                "NormalForms.Tests.External.c1KernelBenchmark",
                "--output",
                str(generated_module),
            ]
        )
        stages: list[dict[str, object]] = [
            {
                "id": "internal_lean",
                "description": "internal Lean SNF generation and inverse checks",
                "command": [str(native_benchmark), "internal"],
            },
            {
                "id": "flint_cli_generation",
                "description": "FLINT process worker plus JSON wrapper",
                "command": [
                    sys.executable,
                    str(wrapper),
                    "snf",
                    "--input",
                    str(input_path),
                    "--worker",
                    str(cli_worker),
                    "--generator",
                    "normalforms-flint-cli",
                    "--output",
                    str(cli_certificate),
                ],
            },
            {
                "id": "flint_ffi_generation",
                "description": "Lean FFI worker plus the same JSON wrapper",
                "command": [
                    sys.executable,
                    str(wrapper),
                    "snf",
                    "--input",
                    str(input_path),
                    "--worker",
                    str(ffi_worker),
                    "--generator",
                    "normalforms-flint-ffi",
                    "--output",
                    str(ffi_certificate),
                ],
            },
            {
                "id": "kernel_checker",
                "description": "strict generated module checked with decide_cbv",
                "command": ["lake", "env", "lean", str(generated_module)],
            },
            {
                "id": "native_checker",
                "description": "pure checker executed as native run report",
                "command": [str(native_benchmark), "check", str(cli_certificate)],
            },
            {
                "id": "cli_generate_import_total",
                "description": "CLI generation, source emission, and kernel import",
                "command": [
                    sys.executable,
                    str(total),
                    "--worker",
                    str(cli_worker),
                    "--generator",
                    "normalforms-flint-cli",
                    "--input",
                    str(input_path),
                ],
            },
            {
                "id": "ffi_generate_import_total",
                "description": "FFI generation, source emission, and kernel import",
                "command": [
                    sys.executable,
                    str(total),
                    "--worker",
                    str(ffi_worker),
                    "--generator",
                    "normalforms-flint-ffi",
                    "--input",
                    str(input_path),
                ],
            },
        ]
        for stage in stages:
            command = stage["command"]
            for warmup in range(arguments.warmups):
                measure(
                    command,
                    temporary / f"{stage['id']}-warmup-{warmup}.time",
                    capture_stdout=False,
                )
            observations: list[dict[str, float | int]] = []
            for iteration in range(arguments.measurements):
                observation, _, _ = measure(
                    command,
                    temporary / f"{stage['id']}-{iteration}.time",
                    capture_stdout=False,
                )
                observation["iteration"] = iteration + 1
                observations.append(observation)
            del stage["command"]
            stage["observations"] = observations
            stage["summary"] = summarize_observations(observations)

        input_json = json.loads(input_path.read_text(encoding="utf-8"))
        cli_json = json.loads(cli_certificate.read_text(encoding="utf-8"))
        ffi_json = json.loads(ffi_certificate.read_text(encoding="utf-8"))
        by_id = {str(stage["id"]): stage for stage in stages}

        def median(stage_id: str) -> float:
            stage = by_id[stage_id]
            stage_summary = stage["summary"]
            return float(stage_summary["wall_seconds"]["median"])

        native_check_median = median("native_checker")
        report: dict[str, object] = {
            "schema": "normalforms.benchmark/v1",
            "profile": arguments.report_profile,
            "created_utc": datetime.now(timezone.utc).isoformat(),
            "policy": {
                "warmups": arguments.warmups,
                "measurements": arguments.measurements,
                "hosted_ci_absolute_time_gate": False,
                "comparison_requires_identical_hardware_fingerprint": True,
            },
            "case": {
                "name": "benchmark-small-2x3-int-snf",
                "rows": input_json["rows"],
                "cols": input_json["cols"],
                "nonzero_entries": sum(
                    entry != "0" for entry in input_json["entries"]
                ),
                "maximum_input_integer_bits": max_integer_bits(input_json),
                "maximum_cli_certificate_integer_bits": max_integer_bits(cli_json),
                "maximum_ffi_certificate_integer_bits": max_integer_bits(ffi_json),
                "maximum_polynomial_degree": None,
                "polynomial_degree_status": "not applicable to Int profile",
            },
            "instrumentation": {
                "ring_operation_count": None,
                "pivot_count": None,
                "gcd_count": None,
                "status": (
                    "not exposed by the pure kernel or FLINT API; formal "
                    "operation telemetry is a separate research gate"
                ),
            },
            "certificate_bytes": {
                "cli": cli_certificate.stat().st_size,
                "ffi": ffi_certificate.stat().st_size,
                "generated_lean": generated_module.stat().st_size,
            },
            "hardware": hardware_fingerprint(),
            "source": source_fingerprint(),
            "stages": stages,
            "ratios": {
                "cli_generation_to_native_check": (
                    median("flint_cli_generation") / native_check_median
                    if native_check_median
                    else None
                ),
                "ffi_generation_to_native_check": (
                    median("flint_ffi_generation") / native_check_median
                    if native_check_median
                    else None
                ),
                "cli_total_to_generation": (
                    median("cli_generate_import_total")
                    / median("flint_cli_generation")
                ),
                "ffi_total_to_generation": (
                    median("ffi_generate_import_total")
                    / median("flint_ffi_generation")
                ),
            },
            "trust_boundary": (
                "Only recompiling a generated strict module yields a Lean "
                "theorem. CLI, FFI, differential, and native-checker success "
                "are untrusted run reports."
            ),
        }

    json_path, csv_path = output_paths(arguments.output_prefix)
    write_json(json_path, report, sort_keys=True)
    rows: list[dict[str, object]] = []
    for stage in report["stages"]:  # type: ignore[union-attr]
        for observation in stage["observations"]:
            rows.append(
                {
                    "stage": stage["id"],
                    **observation,
                    "maximum_input_integer_bits": report["case"][
                        "maximum_input_integer_bits"
                    ],
                    "ring_operation_count": "",
                    "pivot_count": "",
                    "gcd_count": "",
                }
            )
    write_csv(
        csv_path,
        [
            "stage",
            "iteration",
            "wall_seconds",
            "maximum_rss_kib",
            "user_seconds",
            "system_seconds",
            "maximum_input_integer_bits",
            "ring_operation_count",
            "pivot_count",
            "gcd_count",
        ],
        rows,
    )
    print(json_path)
    print(csv_path)
    return 0


def add_common_arguments(
    parser: argparse.ArgumentParser,
    *,
    default_prefix: Path,
) -> None:
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--measurements", type=int, default=7)
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--output-prefix", type=Path, default=default_prefix)


def argument_parser() -> argparse.ArgumentParser:
    package_version = tomllib.loads(
        (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    )["version"]
    certificate_profile = f"v{package_version}-certificate-paths"
    parser = argparse.ArgumentParser(
        description="Run one explicit normalforms benchmark profile."
    )
    subparsers = parser.add_subparsers(
        dest="benchmark_profile", required=True, metavar="PROFILE"
    )

    certificate = subparsers.add_parser(
        "certificate-paths", help="certificate generation/checking stages"
    )
    add_common_arguments(
        certificate,
        default_prefix=GENERATED / certificate_profile,
    )
    certificate.add_argument(
        "--profile", dest="report_profile", default=certificate_profile
    )
    certificate.set_defaults(handler=run_certificate_paths)

    rational = subparsers.add_parser(
        "rational-canonical", help="rational canonical executable profile"
    )
    add_common_arguments(
        rational,
        default_prefix=GENERATED / "v1.1.0-rational-canonical",
    )
    rational.set_defaults(handler=run_rational_canonical)

    bit_cost = subparsers.add_parser(
        "bit-cost", help="binary primitive cost corpus"
    )
    bit_cost.add_argument("--warmups", type=int, default=1)
    bit_cost.add_argument("--measurements", type=int, default=7)
    bit_cost.add_argument("--skip-build", action="store_true")
    bit_cost.add_argument(
        "--output-prefix",
        type=Path,
        default=GENERATED / "research-bit-cost-v0.1.0",
    )
    bit_cost.set_defaults(handler=run_bit_cost)

    for name, help_text, profile in (
        ("kannan-bachem", "Kannan--Bachem HNF/SNF profile", KANNAN_BACHEM),
        ("modular-hnf", "modular-HNF value-kernel profile", MODULAR_HNF),
        ("lll", "exact integer LLL profile", LLL),
    ):
        subparser = subparsers.add_parser(name, help=help_text)
        add_common_arguments(
            subparser,
            default_prefix=GENERATED / profile.profile,
        )
        subparser.set_defaults(
            handler=lambda arguments, selected=profile: run_structured_profile(
                arguments, selected
            )
        )
    return parser


def main() -> int:
    arguments = argument_parser().parse_args()
    minimum_measurements = 4 if arguments.benchmark_profile == "bit-cost" else 2
    if arguments.warmups < 0 or arguments.measurements < minimum_measurements:
        print(
            "warmups must be nonnegative and measurements must be at least "
            f"{minimum_measurements}",
            file=sys.stderr,
        )
        return 64
    if not TIME_EXECUTABLE.is_file():
        print("/usr/bin/time is required", file=sys.stderr)
        return 69
    try:
        return arguments.handler(arguments)
    except (OSError, RuntimeError, ValueError, KeyError, TypeError) as error:
        print(
            f"normalforms-{arguments.benchmark_profile}-benchmark: {error}",
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
