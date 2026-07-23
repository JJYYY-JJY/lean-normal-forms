#!/usr/bin/env python3
"""Validate code-only repository evidence and verifier reports."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tomllib
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
BASELINES = ROOT / "benchmarks" / "baselines"

STRICT_ALLOWLIST = ["propext", "Quot.sound"]
SEMANTIC_ALLOWLIST = ["propext", "Quot.sound", "Classical.choice"]
SEMANTIC_OBSERVED = ["Classical.choice", "Quot.sound", "propext"]

EXPECTED_JSON_BASELINES = {
    "research-bit-cost-v0.1.0.json": "normalforms.bit-cost-benchmark/v1",
    "research-kannan-bachem-v0.1.0.json":
        "normalforms.kannan-bachem-benchmark/v1",
    "research-kannan-bachem-v0.2.0-dev.json":
        "normalforms.kannan-bachem-benchmark/v2",
    "research-lll-v0.1.0.json": "normalforms.lll-benchmark/v1",
    "research-modular-hnf-v0.1.0.json":
        "normalforms.modular-hnf-benchmark/v1",
    "v0.2.2-native-polynomial.json": "normalforms.benchmark/v1",
    "v0.3.1-certificate-paths.json": "normalforms.benchmark/v1",
    "v1.0.0-certificate-paths.json": "normalforms.benchmark/v1",
    "v1.0.0-module-profile.json": "normalforms.module-profile/v1",
    "v1.1.0-rational-canonical.json": "normalforms.benchmark/v1",
}

EXPECTED_CSV_BASELINES = {
    "research-bit-cost-v0.1.0.csv": 20,
    "research-kannan-bachem-v0.1.0.csv": 42,
    "research-kannan-bachem-v0.2.0-dev.csv": 42,
    "research-lll-v0.1.0.csv": 56,
    "research-modular-hnf-v0.1.0.csv": 42,
    "v0.2.2-native-polynomial.csv": 7,
    "v0.3.1-certificate-paths.csv": 49,
    "v1.0.0-certificate-paths.csv": 49,
    "v1.1.0-rational-canonical.csv": 21,
}

EXPECTED_BASELINE_SHA256 = {
    "research-bit-cost-v0.1.0.json":
        "4c2674c72ddb2f7ef6f37a14b90bbf613bd422b010188efcab9ecc5e91580b72",
    "research-kannan-bachem-v0.1.0.json":
        "99520568b6f420c98a03e52d95aa236e63cfb0f2ff330b21813a64f162bcfbe7",
    "research-lll-v0.1.0.json":
        "4762da624970db2c99936fb1035fdd5e3deba5c4a146462dd1135ba8a5da4ea4",
    "research-modular-hnf-v0.1.0.json":
        "18590922d8f586f72325b2f426cbd8678298afb8a2dd42e1fffae3fe815cd1df",
    "v0.2.2-native-polynomial.json":
        "9b32d6392594433fc59d07b366f8a87ba00a583e20614c0a690f7544c66da654",
    "v0.3.1-certificate-paths.json":
        "af8fe2d96bbc7afd0ba776f595b94182d5cbaaa265370c58f7493692ec66621a",
    "v1.0.0-certificate-paths.json":
        "5d3e3930c6705f8aa08bd3350bbecfdac345f429b4bab7df866585a1770fd27d",
    "v1.0.0-module-profile.json":
        "38adba8460f3ccc79bcf5b6163d2fbe9d0b2d1fe510a1c8a23c592693b3d075e",
    "v1.1.0-rational-canonical.json":
        "b7e3340a769dc7efef6b8de5da05a339765cfde0bc90143832dfb1d6ad2c1dd5",
    "research-bit-cost-v0.1.0.csv":
        "e5bf8f67d1b623c74253a66c6f8f49d586d36b450d329fec0facf612d3553cd8",
    "research-kannan-bachem-v0.1.0.csv":
        "465eeaaf4979741b85bade515fe38b47a402af26a625256142304181523740be",
    "research-lll-v0.1.0.csv":
        "2cbaee31dda527502343574c0a1e0bd3fa3f7f6a9d213dfefd73fdf19acde2a9",
    "research-modular-hnf-v0.1.0.csv":
        "3ffd0085472f272fa2359ca32a19eace39a0f8a76007229e3506e86502479be3",
    "v0.2.2-native-polynomial.csv":
        "3fa92d2228a6e47b6d193b2afcec3d3d77b30001d1cfc51ec48184b1dda4826f",
    "v0.3.1-certificate-paths.csv":
        "f9d23950626220bc431e7bb87f5cd3066e03d4166376cfa1260655eaf4e43ed7",
    "v1.0.0-certificate-paths.csv":
        "1388859d84056c6ec132083072de583c7719d147f8dbba9cef2717639bba13da",
    "v1.1.0-rational-canonical.csv":
        "fd67ed9279f50c748cb5f8f4a60fa7031cced1e62355ced3cf80f5ec7a34abf0",
}

EXTERNAL_CHECKSUM_BASELINES = {
    "research-kannan-bachem-v0.2.0-dev.json",
    "research-kannan-bachem-v0.2.0-dev.csv",
}
KANNAN_V2_CHECKSUM = (
    BASELINES / "research-kannan-bachem-v0.2.0-dev.sha256"
)
KANNAN_SOURCE_MANIFEST = (
    ROOT / "artifact/kannan-bachem/source-manifest.txt"
)


class ValidationError(RuntimeError):
    """A committed code artifact or fresh verifier report is invalid."""


def fail(message: str) -> None:
    raise ValidationError(message)


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(f"{path}: invalid JSON: {error}")
    if not isinstance(value, dict):
        fail(f"{path}: root must be an object")
    return value


def require_contains(relative_path: str, expected: str) -> None:
    path = ROOT / relative_path
    if expected not in path.read_text(encoding="utf-8"):
        fail(f"{relative_path}: missing {expected!r}")


def require_equal(actual: object, expected: object, description: str) -> None:
    if actual != expected:
        fail(f"{description}: expected {expected!r}, observed {actual!r}")


def validate_policy(report: dict[str, Any], path: Path) -> None:
    policy = report.get("policy")
    if not isinstance(policy, dict):
        fail(f"{path}: missing benchmark policy")
    require_equal(policy.get("warmups"), 1, f"{path} warmups")
    require_equal(policy.get("measurements"), 7, f"{path} measurements")


def validate_stages(
    report: dict[str, Any], path: Path, expected_ids: list[str]
) -> None:
    stages = report.get("stages")
    if not isinstance(stages, list):
        fail(f"{path}: stages must be an array")
    observed_ids = [stage.get("id") for stage in stages if isinstance(stage, dict)]
    require_equal(observed_ids, expected_ids, f"{path} stage ids")
    for stage in stages:
        if not isinstance(stage, dict):
            fail(f"{path}: stage must be an object")
        observations = stage.get("observations")
        if not isinstance(observations, list) or len(observations) != 7:
            fail(f"{path}: stage {stage.get('id')!r} must have seven observations")
        for observation in observations:
            if not isinstance(observation, dict):
                fail(f"{path}: observation must be an object")
            if observation.get("wall_seconds", 0) <= 0:
                fail(f"{path}: observation has nonpositive wall time")
            if observation.get("maximum_rss_kib", 0) <= 0:
                fail(f"{path}: observation has nonpositive RSS")


def validate_research_cases(
    report: dict[str, Any], path: Path, expected_names: list[str]
) -> list[dict[str, Any]]:
    cases = report.get("cases")
    if not isinstance(cases, list) or not all(isinstance(case, dict) for case in cases):
        fail(f"{path}: cases must be an array of objects")
    typed_cases: list[dict[str, Any]] = cases
    require_equal(
        [case.get("case") for case in typed_cases], expected_names, f"{path} cases"
    )
    if any(case.get("valid") is not True for case in typed_cases):
        fail(f"{path}: a deterministic case is invalid")
    return typed_cases


def validate_bit_cost(path: Path, report: dict[str, Any]) -> None:
    require_equal(report.get("researchVersion"), "0.1.0", f"{path} research version")
    require_equal(report.get("warmups"), 1, f"{path} warmups")
    require_equal(report.get("measurementCount"), 7, f"{path} measurements")
    measurements = report.get("measurements")
    if not isinstance(measurements, list) or len(measurements) != 7:
        fail(f"{path}: expected seven measurements")
    if any(
        not isinstance(row, dict)
        or row.get("wall_ns", 0) <= 0
        or row.get("max_rss_kib", 0) <= 0
        for row in measurements
    ):
        fail(f"{path}: invalid measurement")
    cases = report.get("cases")
    if not isinstance(cases, list) or len(cases) != 13:
        fail(f"{path}: expected thirteen deterministic cases")
    operations: list[object] = []
    for case in cases:
        if not isinstance(case, dict) or case.get("valid") is not True:
            fail(f"{path}: invalid deterministic case")
        if case.get("cost", 1) > case.get("bound", 0):
            fail(f"{path}: modeled cost exceeds its bound")
        operations.append(case.get("operation"))
    require_equal(
        Counter(operations),
        Counter({"add": 3, "mul": 3, "divmod": 3, "xgcd": 4}),
        f"{path} operation corpus",
    )


def validate_kannan_bachem_v1(path: Path, report: dict[str, Any]) -> None:
    require_equal(
        report.get("profile"),
        "research-kannan-bachem-v0.1.0",
        f"{path} profile",
    )
    require_equal(report.get("research_version"), "0.1.0", f"{path} version")
    validate_policy(report, path)
    cases = validate_research_cases(
        report,
        path,
        ["hnf-prepared-3x3", "smith-repeat-2x2", "smith-injection-2x2"],
    )
    if any(case.get("bit_cost", 1) > case.get("bit_bound", 0) for case in cases):
        fail(f"{path}: modeled bit cost exceeds its theorem bound")
    validate_stages(
        report,
        path,
        ["prepared_hnf", "smith_repeat", "smith_injection", "end_to_end"],
    )


def profile_source_fingerprint(manifest: Path) -> tuple[str, int]:
    patterns = [
        line.strip()
        for line in manifest.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    files: set[Path] = set()
    for pattern in patterns:
        matches = [path for path in ROOT.glob(pattern) if path.is_file()]
        if not matches:
            fail(f"source-manifest pattern matched no files: {pattern}")
        files.update(matches)
    ordered = sorted(files, key=lambda path: path.relative_to(ROOT).as_posix())
    digest = hashlib.sha256()
    for file in ordered:
        relative = file.relative_to(ROOT).as_posix().encode("utf-8")
        content = file.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest(), len(ordered)


def validate_kannan_bachem_v2(path: Path, report: dict[str, Any]) -> None:
    require_equal(
        report.get("profile"),
        "research-kannan-bachem-v0.2.0-dev",
        f"{path} profile",
    )
    require_equal(report.get("research_version"), "0.2.0-dev", f"{path} version")
    validate_policy(report, path)
    cases = validate_research_cases(
        report,
        path,
        ["hnf-prepared-3x3", "smith-repeat-2x2", "smith-injection-2x2"],
    )
    for case in cases:
        if case.get("bit_cost", 1) > case.get("bit_bound", 0):
            fail(f"{path}: modeled bit cost exceeds its theorem bound")
        total = sum(
            int(case.get(field, -1))
            for field in (
                "additions",
                "multiplications",
                "xgcd_calls",
                "normalizations",
                "standalone_divmod_calls",
            )
        )
        require_equal(
            case.get("arithmetic_operation_total"),
            total,
            f"{path} {case.get('case')} macro-operation total",
        )
        if str(case.get("case", "")).startswith("smith-"):
            if int(case.get("output_encoding_bits", 0)) <= 0:
                fail(f"{path}: Smith output encoding length is missing")
    validate_stages(
        report,
        path,
        ["prepared_hnf", "smith_repeat", "smith_injection", "end_to_end"],
    )
    source = report.get("source")
    if not isinstance(source, dict):
        fail(f"{path}: source must be an object")
    require_equal(source.get("working_tree_clean"), True, f"{path} source clean")
    require_equal(
        source.get("tracked_patch_sha256"),
        hashlib.sha256(b"\n").hexdigest(),
        f"{path} tracked patch",
    )
    digest, file_count = profile_source_fingerprint(KANNAN_SOURCE_MANIFEST)
    require_equal(
        source.get("profile_source_sha256"),
        digest,
        f"{path} profile source SHA-256",
    )
    require_equal(
        source.get("profile_source_file_count"),
        file_count,
        f"{path} profile source file count",
    )
    revision = source.get("git_revision")
    if not isinstance(revision, str) or len(revision) != 40:
        fail(f"{path}: source revision is invalid")
    if (ROOT / ".git").exists():
        reachable = subprocess.run(
            ["git", "merge-base", "--is-ancestor", revision, "HEAD"],
            cwd=ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if reachable.returncode != 0:
            fail(f"{path}: recorded source revision is not an ancestor of HEAD")
    binary_digest = report.get("binary_sha256")
    if (
        not isinstance(binary_digest, str)
        or len(binary_digest) != 64
        or any(character not in "0123456789abcdef" for character in binary_digest)
    ):
        fail(f"{path}: binary fingerprint is invalid")


def validate_modular_hnf(path: Path, report: dict[str, Any]) -> None:
    require_equal(
        report.get("profile"),
        "research-modular-hnf-v0.1.0",
        f"{path} profile",
    )
    require_equal(report.get("research_version"), "0.1.0", f"{path} version")
    validate_policy(report, path)
    cases = validate_research_cases(
        report, path, ["scalar-1x1", "tall-2x1", "square-2x2"]
    )
    for case in cases:
        if case.get("operation_total", 1) > case.get("operation_bound", 0):
            fail(f"{path}: operation count exceeds its theorem bound")
        if case.get("modeled_bit_cost_bits", 1) > case.get(
            "modeled_bit_bound_bits", 0
        ):
            fail(f"{path}: modeled bit cost exceeds its theorem bound")
    validate_stages(report, path, ["scalar", "tall", "square", "end_to_end"])


def validate_lll(path: Path, report: dict[str, Any]) -> None:
    require_equal(
        report.get("profile"), "research-lll-v0.1.0", f"{path} profile"
    )
    require_equal(report.get("research_version"), "0.1.0", f"{path} version")
    validate_policy(report, path)
    cases = validate_research_cases(
        report,
        path,
        ["gauss-2x2", "dense-3x3", "dependent-3x3", "column-3x3"],
    )
    for case in cases:
        if case.get("kind") != "profiled-full-rank":
            continue
        if case.get("operation_total", 1) > case.get("operation_bound", 0):
            fail(f"{path}: operation count exceeds its theorem bound")
        if case.get("modeled_bit_cost", 1) > case.get("modeled_bit_bound", 0):
            fail(f"{path}: modeled bit cost exceeds its theorem bound")
    validate_stages(
        report, path, ["gauss", "dense", "dependent", "column", "end_to_end"]
    )


def validate_certificate_paths(path: Path, report: dict[str, Any]) -> None:
    expected_profile = path.stem
    require_equal(report.get("profile"), expected_profile, f"{path} profile")
    validate_policy(report, path)
    case = report.get("case")
    expected_case = {
        "name": "benchmark-small-2x3-int-snf",
        "rows": 2,
        "cols": 3,
        "nonzero_entries": 4,
        "maximum_input_integer_bits": 4,
        "maximum_cli_certificate_integer_bits": 4,
        "maximum_ffi_certificate_integer_bits": 4,
        "maximum_polynomial_degree": None,
        "polynomial_degree_status": "not applicable to Int profile",
    }
    require_equal(case, expected_case, f"{path} deterministic case")
    validate_stages(
        report,
        path,
        [
            "internal_lean",
            "flint_cli_generation",
            "flint_ffi_generation",
            "kernel_checker",
            "native_checker",
            "cli_generate_import_total",
            "ffi_generate_import_total",
        ],
    )


def validate_rational_canonical(path: Path, report: dict[str, Any]) -> None:
    require_equal(
        report.get("profile"), "v1.1.0-rational-canonical", f"{path} profile"
    )
    validate_policy(report, path)
    case = report.get("case")
    expected_case = {
        "name": "rational-jordan-2x2",
        "rows": 2,
        "cols": 2,
        "factor_degrees": [0, 2],
        "maximum_input_coefficient_bits": 2,
        "maximum_factor_coefficient_bits": 3,
        "companion_repetitions": 1000,
    }
    require_equal(case, expected_case, f"{path} deterministic case")
    validate_stages(
        report,
        path,
        ["invariant_generation", "companion_verification", "end_to_end"],
    )


def validate_module_profile(path: Path, report: dict[str, Any]) -> None:
    modules = report.get("modules")
    if not isinstance(modules, list):
        fail(f"{path}: modules must be an array")
    require_equal(
        [module.get("module") for module in modules if isinstance(module, dict)],
        [
            "NormalForms/Euclidean/PolynomialRat.lean",
            "NormalForms/Matrix/Hermite/Algorithm.lean",
            "NormalForms/Matrix/Smith/Algorithm.lean",
            "NormalForms/Certificate/Checker.lean",
        ],
        f"{path} module set",
    )
    if any(
        not isinstance(module, dict) or module.get("allocation_count", 0) <= 0
        for module in modules
    ):
        fail(f"{path}: invalid module allocation row")


def validate_native_polynomial(path: Path, report: dict[str, Any]) -> None:
    require_equal(
        report.get("benchmark"),
        "native-polynomial-certificate-corpus",
        f"{path} benchmark",
    )
    require_equal(report.get("version"), "0.2.2", f"{path} version")
    require_equal(
        report.get("coverage"),
        [
            "pivot improvement",
            "zero matrix",
            "constant full rank",
            "rank-deficient polynomial",
            "zero rows",
            "HNF and SNF transformation equations",
            "all stored inverse identities",
        ],
        f"{path} coverage",
    )
    protocol = report.get("protocol")
    if not isinstance(protocol, dict):
        fail(f"{path}: missing protocol")
    require_equal(protocol.get("warmups"), 1, f"{path} warmups")
    require_equal(protocol.get("measurements"), 7, f"{path} measurements")


def read_csv(path: Path) -> list[dict[str, str]]:
    try:
        with path.open(newline="", encoding="utf-8") as handle:
            reader = csv.DictReader(handle)
            rows = list(reader)
    except OSError as error:
        fail(f"{path}: cannot read CSV: {error}")
    if not rows or not reader.fieldnames or any(not name for name in reader.fieldnames):
        fail(f"{path}: invalid CSV header or empty data")
    return rows


def require_stage_counts(
    path: Path, rows: list[dict[str, str]], expected: dict[str, int]
) -> None:
    observed = Counter(row.get("stage") for row in rows)
    require_equal(observed, Counter(expected), f"{path} stage counts")


def validate_baselines() -> None:
    observed_json = {path.name for path in BASELINES.glob("*.json")}
    observed_csv = {path.name for path in BASELINES.glob("*.csv")}
    require_equal(observed_json, set(EXPECTED_JSON_BASELINES), "JSON baseline set")
    require_equal(observed_csv, set(EXPECTED_CSV_BASELINES), "CSV baseline set")
    require_equal(
        set(EXPECTED_BASELINE_SHA256) | EXTERNAL_CHECKSUM_BASELINES,
        observed_json | observed_csv,
        "fingerprinted baseline set",
    )
    for filename, expected_digest in EXPECTED_BASELINE_SHA256.items():
        path = BASELINES / filename
        observed_digest = hashlib.sha256(path.read_bytes()).hexdigest()
        require_equal(observed_digest, expected_digest, f"{path} SHA-256")
    checksum_lines = KANNAN_V2_CHECKSUM.read_text(encoding="utf-8").splitlines()
    checksums: dict[str, str] = {}
    for line in checksum_lines:
        digest, separator, filename = line.partition("  ")
        if not separator:
            fail(f"{KANNAN_V2_CHECKSUM}: malformed checksum line")
        checksums[filename] = digest
    require_equal(
        set(checksums), EXTERNAL_CHECKSUM_BASELINES, "Kannan v2 checksum files"
    )
    for filename, expected_digest in checksums.items():
        observed_digest = hashlib.sha256((BASELINES / filename).read_bytes()).hexdigest()
        require_equal(
            observed_digest, expected_digest, f"{BASELINES / filename} SHA-256"
        )

    reports: dict[str, dict[str, Any]] = {}
    for filename, schema in EXPECTED_JSON_BASELINES.items():
        path = BASELINES / filename
        report = load_json(path)
        require_equal(report.get("schema"), schema, f"{path} schema")
        reports[filename] = report

    validate_bit_cost(
        BASELINES / "research-bit-cost-v0.1.0.json",
        reports["research-bit-cost-v0.1.0.json"],
    )
    validate_kannan_bachem_v1(
        BASELINES / "research-kannan-bachem-v0.1.0.json",
        reports["research-kannan-bachem-v0.1.0.json"],
    )
    validate_kannan_bachem_v2(
        BASELINES / "research-kannan-bachem-v0.2.0-dev.json",
        reports["research-kannan-bachem-v0.2.0-dev.json"],
    )
    validate_lll(
        BASELINES / "research-lll-v0.1.0.json",
        reports["research-lll-v0.1.0.json"],
    )
    validate_modular_hnf(
        BASELINES / "research-modular-hnf-v0.1.0.json",
        reports["research-modular-hnf-v0.1.0.json"],
    )
    validate_native_polynomial(
        BASELINES / "v0.2.2-native-polynomial.json",
        reports["v0.2.2-native-polynomial.json"],
    )
    for filename in (
        "v0.3.1-certificate-paths.json",
        "v1.0.0-certificate-paths.json",
    ):
        validate_certificate_paths(BASELINES / filename, reports[filename])
    validate_module_profile(
        BASELINES / "v1.0.0-module-profile.json",
        reports["v1.0.0-module-profile.json"],
    )
    validate_rational_canonical(
        BASELINES / "v1.1.0-rational-canonical.json",
        reports["v1.1.0-rational-canonical.json"],
    )

    csv_rows: dict[str, list[dict[str, str]]] = {}
    for filename, expected_count in EXPECTED_CSV_BASELINES.items():
        path = BASELINES / filename
        rows = read_csv(path)
        require_equal(len(rows), expected_count, f"{path} row count")
        csv_rows[filename] = rows
    bit_rows = csv_rows["research-bit-cost-v0.1.0.csv"]
    require_equal(
        Counter(row.get("record") for row in bit_rows),
        Counter({"measurement": 7, "case": 13}),
        "bit-cost CSV records",
    )
    require_stage_counts(
        BASELINES / "research-kannan-bachem-v0.1.0.csv",
        csv_rows["research-kannan-bachem-v0.1.0.csv"],
        {
            "prepared_hnf": 7,
            "smith_repeat": 7,
            "smith_injection": 7,
            "end_to_end": 21,
        },
    )
    require_stage_counts(
        BASELINES / "research-kannan-bachem-v0.2.0-dev.csv",
        csv_rows["research-kannan-bachem-v0.2.0-dev.csv"],
        {
            "prepared_hnf": 7,
            "smith_repeat": 7,
            "smith_injection": 7,
            "end_to_end": 21,
        },
    )
    require_stage_counts(
        BASELINES / "research-modular-hnf-v0.1.0.csv",
        csv_rows["research-modular-hnf-v0.1.0.csv"],
        {"scalar": 7, "tall": 7, "square": 7, "end_to_end": 21},
    )
    require_stage_counts(
        BASELINES / "research-lll-v0.1.0.csv",
        csv_rows["research-lll-v0.1.0.csv"],
        {
            "gauss": 7,
            "dense": 7,
            "dependent": 7,
            "column": 7,
            "end_to_end": 28,
        },
    )
    certificate_stages = {
        "internal_lean": 7,
        "flint_cli_generation": 7,
        "flint_ffi_generation": 7,
        "kernel_checker": 7,
        "native_checker": 7,
        "cli_generate_import_total": 7,
        "ffi_generate_import_total": 7,
    }
    for filename in (
        "v0.3.1-certificate-paths.csv",
        "v1.0.0-certificate-paths.csv",
    ):
        require_stage_counts(BASELINES / filename, csv_rows[filename], certificate_stages)
    require_stage_counts(
        BASELINES / "v1.1.0-rational-canonical.csv",
        csv_rows["v1.1.0-rational-canonical.csv"],
        {"invariant_generation": 7, "companion_verification": 7, "end_to_end": 7},
    )


def validate_repository() -> None:
    lake = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    require_equal(lake.get("version"), "1.2.2", "Lake package version")
    requirements = {
        requirement.get("name"): requirement
        for requirement in lake.get("require", [])
        if isinstance(requirement, dict)
    }
    require_equal(
        requirements.get("mathlib", {}).get("rev"), "v4.32.0", "mathlib pin"
    )
    require_equal(
        requirements.get("HexLLLMathlib", {}).get("rev"),
        "c10d6681dee9a4f963c1035bcbe34fc3eb60a769",
        "HexLLLMathlib pin",
    )
    require_equal(
        (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "leanprover/lean4:v4.32.0",
        "Lean toolchain pin",
    )

    manifest = load_json(ROOT / "lake-manifest.json")
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        fail("lake-manifest.json: packages must be an array")
    package_by_name = {
        package.get("name"): package for package in packages if isinstance(package, dict)
    }
    require_equal(
        package_by_name.get("mathlib", {}).get("inputRev"),
        "v4.32.0",
        "manifest mathlib input revision",
    )
    require_equal(
        package_by_name.get("HexLLLMathlib", {}).get("rev"),
        "c10d6681dee9a4f963c1035bcbe34fc3eb60a769",
        "manifest HexLLLMathlib revision",
    )
    require_contains("NormalForms/CLI/Main.lean", '["1.2.2"]')
    require_contains("CHANGELOG.md", "## 1.2.2 - ")
    require_contains("docs/PUBLIC_API.md", "Version: 1.2.2")
    require_contains("docs/RATIONAL_CANONICAL_API.md", "Version: 1.1.0")
    require_contains("docs/HOMOLOGY_API.md", "Version: 1.2.2")
    require_contains("docs/BIT_COST_API.md", "research API 0.1.0")
    require_contains("docs/KANNAN_BACHEM_API.md", "Research version: 0.2.0-dev")
    require_contains("docs/MODULAR_HNF_API.md", "Research version: 0.1.0")
    require_contains("docs/LLL_API.md", "Research version: 0.1.0")
    mathlib_revision = package_by_name.get("mathlib", {}).get("rev")
    if not isinstance(mathlib_revision, str):
        fail("manifest mathlib resolved revision is missing")
    require_contains("patches/mathlib/README.md", mathlib_revision)
    for profile in (
        "core",
        "rational-canonical",
        "homology",
        "bit-cost",
        "kannan-bachem",
        "modular-hnf",
        "lll",
    ):
        if not (ROOT / "artifact" / profile / "Dockerfile").is_file():
            fail(f"artifact/{profile}/Dockerfile is missing")

    raw_certificate = (
        ROOT / "NormalForms" / "Certificate" / "Raw.lean"
    ).read_text(encoding="utf-8")
    if '"normalforms.cert/v1"' not in raw_certificate:
        fail("certificate source no longer contains the frozen v1 schema")
    corpus_root = ROOT / "Tests" / "Certificate" / "corpus"
    corpus = {path.name for path in corpus_root.glob("*.json")}
    require_equal(
        corpus,
        {"valid-medium-hnf.json", "valid-medium-snf.json"},
        "certificate fixture set",
    )
    for filename in sorted(corpus):
        certificate = load_json(corpus_root / filename)
        require_equal(
            certificate.get("schema"),
            "normalforms.cert/v1",
            f"{filename} certificate schema",
        )

    for profile in ("bit-cost", "modular-hnf", "lll"):
        require_equal(
            (ROOT / "artifact" / profile / "VERSION")
            .read_text(encoding="utf-8")
            .strip(),
            "0.1.0",
            f"{profile} artifact version",
        )
    require_equal(
        (ROOT / "artifact/kannan-bachem/VERSION")
        .read_text(encoding="utf-8")
        .strip(),
        "0.2.0-dev",
        "kannan-bachem artifact version",
    )
    if not (ROOT / "patches/mathlib/finite-matrix-presentation.patch").is_file():
        fail("standalone mathlib patch is missing")

    validate_baselines()
    print(
        "code evidence validated: "
        f"certificates={len(corpus)} "
        f"benchmark_json={len(EXPECTED_JSON_BASELINES)} "
        f"benchmark_csv={len(EXPECTED_CSV_BASELINES)}"
    )


def validate_audit_report(
    path: Path,
    schema: str,
    expected_count: int | None,
    allowlist: list[str],
    expected_observed: list[str] | None,
) -> None:
    report = load_json(path)
    require_equal(report.get("schema"), schema, f"{path} schema")
    require_equal(report.get("allowlist"), allowlist, f"{path} allowlist")
    declarations = report.get("declarations")
    if not isinstance(declarations, list):
        fail(f"{path}: declarations must be an array")
    if expected_count is not None:
        require_equal(len(declarations), expected_count, f"{path} declaration count")
    if "declarationCount" in report:
        require_equal(
            report.get("declarationCount"), len(declarations), f"{path} declared count"
        )
    observed = sorted(
        {
            axiom
            for declaration in declarations
            if isinstance(declaration, dict)
            for axiom in declaration.get("axioms", [])
        }
    )
    forbidden = sorted(set(observed) - set(allowlist))
    if forbidden:
        fail(f"{path}: forbidden axioms: {forbidden}")
    if expected_observed is not None:
        require_equal(observed, expected_observed, f"{path} observed axioms")


AUDIT_SPECS: dict[
    str, list[tuple[str, int | None, list[str], list[str] | None]]
] = {
    "core": [
        (
            "normalforms.axiom-audit/v1",
            535,
            SEMANTIC_ALLOWLIST,
            SEMANTIC_OBSERVED,
        ),
        ("normalforms.core-axiom-audit/v1", 12, STRICT_ALLOWLIST, None),
        ("normalforms.certificate-axiom-audit/v1", 23, STRICT_ALLOWLIST, None),
    ],
    "rational-canonical": [
        (
            "normalforms.rational-canonical-axiom-audit/v1",
            14,
            SEMANTIC_ALLOWLIST,
            SEMANTIC_OBSERVED,
        )
    ],
    "homology": [
        (
            "normalforms.homology-axiom-audit/v1",
            37,
            SEMANTIC_ALLOWLIST,
            SEMANTIC_OBSERVED,
        )
    ],
    "bit-cost": [
        (
            "normalforms.bit-cost-axiom-audit/v1",
            21,
            SEMANTIC_ALLOWLIST,
            SEMANTIC_OBSERVED,
        ),
        (
            "normalforms.bit-cost-axiom-audit/v1",
            34,
            SEMANTIC_ALLOWLIST,
            SEMANTIC_OBSERVED,
        ),
    ],
    "kannan-bachem": [
        (
            "normalforms.kannan-bachem-axiom-audit/v1",
            296,
            SEMANTIC_ALLOWLIST,
            SEMANTIC_OBSERVED,
        )
    ],
    "modular-hnf": [
        (
            "normalforms.modular-hnf-axiom-audit/v1",
            43,
            SEMANTIC_ALLOWLIST,
            SEMANTIC_OBSERVED,
        )
    ],
    "lll": [
        (
            "normalforms.lll-axiom-audit/v1",
            20,
            SEMANTIC_ALLOWLIST,
            SEMANTIC_OBSERVED,
        )
    ],
}

PUBLIC_API_COUNTS = {
    "rational-canonical": [("NormalForms/Tests/RationalCanonical/PublicApi.lean", 22)],
    "homology": [("NormalForms/Tests/Homology/PublicApi.lean", 53)],
    "bit-cost": [
        ("NormalForms/Tests/Research/BitCost/PublicApiV010.lean", 49),
        ("NormalForms/Tests/Research/BitCost/PublicApi.lean", 87),
    ],
    "kannan-bachem": [
        ("NormalForms/Tests/Research/KannanBachem/PublicApi.lean", 658)
    ],
    "modular-hnf": [
        ("NormalForms/Tests/Research/ModularHNF/PublicApi.lean", 157)
    ],
    "lll": [("NormalForms/Tests/Research/LLL/PublicApi.lean", 114)],
}


def validate_public_api(profile: str) -> None:
    for raw_path, expected_count in PUBLIC_API_COUNTS.get(profile, []):
        path = ROOT / raw_path
        count = sum(
            line.startswith("#check ")
            for line in path.read_text(encoding="utf-8").splitlines()
        )
        require_equal(count, expected_count, f"{raw_path} public declarations")


def parse_native_scalar(raw: str) -> object:
    if raw == "true":
        return True
    if raw == "false":
        return False
    if "," in raw:
        return [parse_native_scalar(value) for value in raw.split(",")]
    try:
        return int(raw)
    except ValueError:
        return raw


def parse_native_cases(profile: str, output: str) -> list[dict[str, object]]:
    if profile == "bit-cost":
        rows: list[dict[str, object]] = []
        for line in output.splitlines():
            if not line.startswith("operation="):
                continue
            row: dict[str, object] = {}
            for field in line.split():
                key, separator, raw = field.partition("=")
                if not separator:
                    fail(f"{profile}: malformed native field {field!r}")
                row[key] = parse_native_scalar(raw)
            rows.append(row)
        return rows

    rows = []
    current: dict[str, object] | None = None
    for line in output.splitlines():
        key, separator, raw = line.partition("=")
        if not separator:
            continue
        if key == "case":
            if current is not None:
                rows.append(current)
            current = {"case": raw}
        elif current is not None and key not in {"cases", "all_valid"}:
            current[key] = parse_native_scalar(raw)
    if current is not None:
        rows.append(current)
    return rows


def validate_rational_native(output: str) -> None:
    metrics: dict[str, object] = {}
    for line in output.splitlines():
        key, separator, raw = line.partition("=")
        if separator:
            metrics[key] = parse_native_scalar(raw)
    require_equal(metrics.get("valid"), True, "rational-canonical native result")
    baseline = load_json(BASELINES / "v1.1.0-rational-canonical.json")["case"]
    expected = {
        "factor_degrees": baseline["factor_degrees"],
        "maximum_input_coefficient_bits": baseline[
            "maximum_input_coefficient_bits"
        ],
        "maximum_factor_coefficient_bits": baseline[
            "maximum_factor_coefficient_bits"
        ],
        "companion_repetitions": baseline["companion_repetitions"],
    }
    observed = {key: metrics.get(key) for key in expected}
    require_equal(observed, expected, "rational-canonical deterministic metrics")


def validate_native(profile: str, path: Path | None) -> None:
    if profile == "core":
        if path is not None:
            fail(f"{profile}: unexpected native report")
        return
    if path is None:
        fail(f"{profile}: native report is required")
    output = path.read_text(encoding="utf-8")
    if profile == "rational-canonical":
        validate_rational_native(output)
    elif profile == "homology":
        if "cases=20\n" not in output or not output.endswith("valid=true\n"):
            fail("homology native summary is incomplete")
        require_equal(output.count(" valid=true "), 20, "homology native cases")
    elif profile == "bit-cost":
        require_equal(output.count("operation="), 13, "bit-cost operations")
        if "cases=13\n" not in output or not output.endswith("valid=true\n"):
            fail("bit-cost native summary is incomplete")
        require_equal(output.count("valid=true"), 14, "bit-cost native cases")
    elif profile in {"kannan-bachem", "modular-hnf"}:
        if "cases=3\n" not in output or not output.endswith("all_valid=true\n"):
            fail(f"{profile} native summary is incomplete")
        require_equal(output.count("valid=true"), 4, f"{profile} native cases")
    elif profile == "lll":
        if "cases=4\n" not in output or not output.endswith("all_valid=true\n"):
            fail("LLL native summary is incomplete")
        require_equal(output.count("valid=true"), 5, "LLL native cases")
    if profile in {"bit-cost", "kannan-bachem", "modular-hnf", "lll"}:
        baseline_name = {
            "bit-cost": "research-bit-cost-v0.1.0.json",
            "kannan-bachem": "research-kannan-bachem-v0.2.0-dev.json",
            "modular-hnf": "research-modular-hnf-v0.1.0.json",
            "lll": "research-lll-v0.1.0.json",
        }[profile]
        expected_cases = load_json(BASELINES / baseline_name)["cases"]
        observed_cases = parse_native_cases(profile, output)
        require_equal(
            observed_cases,
            expected_cases,
            f"{profile} deterministic native cases",
        )


def validate_profile(profile: str, axiom_paths: list[Path], native: Path | None) -> None:
    specs = AUDIT_SPECS[profile]
    require_equal(len(axiom_paths), len(specs), f"{profile} axiom report count")
    for path, (schema, count, allowlist, observed) in zip(
        axiom_paths, specs, strict=True
    ):
        validate_audit_report(path, schema, count, allowlist, observed)
    if profile == "bit-cost":
        archived = load_json(axiom_paths[0])
        require_equal(
            archived.get("profile"),
            "research-bit-cost-0.1.0",
            "bit-cost historical audit profile",
        )
    validate_public_api(profile)
    validate_native(profile, native)
    print(f"{profile} verifier reports validated")


def argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("repository")
    profile_parser = subparsers.add_parser("profile")
    profile_parser.add_argument("profile", choices=sorted(AUDIT_SPECS))
    profile_parser.add_argument("--axiom", action="append", type=Path, default=[])
    profile_parser.add_argument("--native", type=Path)
    return parser


def main() -> int:
    arguments = argument_parser().parse_args()
    try:
        if arguments.command == "repository":
            validate_repository()
        else:
            validate_profile(arguments.profile, arguments.axiom, arguments.native)
    except (OSError, tomllib.TOMLDecodeError, ValidationError) as error:
        print(f"code verification failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
