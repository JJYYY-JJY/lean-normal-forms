#!/usr/bin/env python3
"""Validate synchronized release metadata and committed evidence files."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
import re
import sys
import tomllib


ROOT = Path(__file__).resolve().parent.parent


def fail(message: str) -> None:
    raise RuntimeError(message)


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def require_contains(path: str, expected: str) -> None:
    if expected not in read(path):
        fail(f"{path} does not contain {expected!r}")


def load_json(path: Path) -> object:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(f"{path.relative_to(ROOT)} is not valid JSON: {error}")


def validate_csv(path: Path) -> None:
    with path.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    if not rows:
        fail(f"{path.relative_to(ROOT)} has no observations")
    if not all(rows[0].keys()):
        fail(f"{path.relative_to(ROOT)} has an empty column name")


def validate(version: str, require_release_materials: bool) -> None:
    lake = tomllib.loads(read("lakefile.toml"))
    if lake.get("version") != version:
        fail(f"lakefile.toml version is {lake.get('version')!r}, expected {version!r}")

    if read("lean-toolchain").strip() != "leanprover/lean4:v4.32.0":
        fail("lean-toolchain is not pinned to Lean 4.32.0")

    manifest = load_json(ROOT / "lake-manifest.json")
    if not isinstance(manifest, dict):
        fail("lake-manifest.json root is not an object")
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        fail("lake-manifest.json has no package list")
    mathlib = next(
        (package for package in packages if package.get("name") == "mathlib"),
        None,
    )
    if not isinstance(mathlib, dict):
        fail("lake-manifest.json has no mathlib package")
    if mathlib.get("inputRev") != "v4.32.0":
        fail("mathlib input revision is not v4.32.0")
    mathlib_revision = mathlib.get("rev")
    if not isinstance(mathlib_revision, str):
        fail("mathlib resolved revision is missing")

    require_contains("NormalForms/CLI/Main.lean", f'["{version}"]')
    require_contains("README.md", f"Version {version}")
    require_contains("docs/PUBLIC_API.md", f"Version: {version}")
    require_contains("artifact/README.md", f"Current {version} baseline")
    require_contains("CHANGELOG.md", f"## {version} - ")
    require_contains("CITATION.cff", f"version: {version}")
    require_contains("patches/mathlib/README.md", mathlib_revision)

    if version in {"1.1.0", "1.2.0", "1.2.1", "1.2.2"}:
        require_contains(
            "docs/RATIONAL_CANONICAL_API.md",
            "Version: 1.1.0",
        )
        if not (ROOT / "artifact/rational-canonical/Dockerfile").is_file():
            fail("rational-canonical artifact Dockerfile is missing")

    if version in {"1.2.0", "1.2.1", "1.2.2"}:
        require_contains(
            "docs/HOMOLOGY_API.md",
            f"Version: {version}",
        )
        if not (ROOT / "artifact/homology/Dockerfile").is_file():
            fail("homology artifact Dockerfile is missing")

    zenodo = load_json(ROOT / ".zenodo.json")
    if not isinstance(zenodo, dict) or zenodo.get("version") != version:
        fail(".zenodo.json version does not match Lake")

    raw_source = read("NormalForms/Certificate/Raw.lean")
    if '"normalforms.cert/v1"' not in raw_source:
        fail("certificate source does not contain the frozen schema identifier")
    require_contains("docs/CERTIFICATE_SCHEMA_V1.md", "`normalforms.cert/v1`")

    certificate_files = sorted((ROOT / "Tests/Certificate/corpus").glob("*.json"))
    if not certificate_files:
        fail("certificate corpus is empty")
    for path in certificate_files:
        certificate = load_json(path)
        if not isinstance(certificate, dict):
            fail(f"{path.relative_to(ROOT)} root is not an object")
        if certificate.get("schema") != "normalforms.cert/v1":
            fail(f"{path.relative_to(ROOT)} has a non-v1 schema")

    benchmark_json = sorted((ROOT / "benchmarks/baselines").glob("*.json"))
    benchmark_csv = sorted((ROOT / "benchmarks/baselines").glob("*.csv"))
    if not benchmark_json or not benchmark_csv:
        fail("benchmark baseline JSON/CSV files are missing")
    for path in benchmark_json:
        benchmark = load_json(path)
        if not isinstance(benchmark, dict):
            fail(f"{path.relative_to(ROOT)} root is not an object")
        schema = benchmark.get("schema")
        if schema not in {
            "normalforms.benchmark/v1",
            "normalforms.module-profile/v1",
            "normalforms.bit-cost-benchmark/v1",
            "normalforms.kannan-bachem-benchmark/v1",
            "normalforms.modular-hnf-benchmark/v1",
            "normalforms.lll-benchmark/v1",
        }:
            fail(f"{path.relative_to(ROOT)} has an unknown benchmark schema")
        if schema == "normalforms.module-profile/v1":
            modules = benchmark.get("modules")
            if not isinstance(modules, list) or not modules:
                fail(f"{path.relative_to(ROOT)} has no profiled modules")
            for module in modules:
                if (
                    not isinstance(module, dict)
                    or not isinstance(module.get("module"), str)
                    or not isinstance(module.get("allocation_count"), int)
                    or module["allocation_count"] <= 0
                ):
                    fail(f"{path.relative_to(ROOT)} has an invalid module row")
        if schema == "normalforms.bit-cost-benchmark/v1":
            if benchmark.get("researchVersion") != "0.1.0":
                fail(f"{path.relative_to(ROOT)} has the wrong research version")
            if benchmark.get("warmups") != 1:
                fail(f"{path.relative_to(ROOT)} has the wrong warmup count")
            if benchmark.get("measurementCount") != 7:
                fail(f"{path.relative_to(ROOT)} has the wrong measurement count")
            measurements = benchmark.get("measurements")
            if not isinstance(measurements, list) or len(measurements) != 7:
                fail(f"{path.relative_to(ROOT)} has invalid measurements")
            for measurement in measurements:
                if (
                    not isinstance(measurement, dict)
                    or not isinstance(measurement.get("wall_ns"), int)
                    or measurement["wall_ns"] <= 0
                    or not isinstance(measurement.get("max_rss_kib"), int)
                    or measurement["max_rss_kib"] <= 0
                ):
                    fail(f"{path.relative_to(ROOT)} has an invalid measurement")
            cases = benchmark.get("cases")
            if not isinstance(cases, list) or len(cases) != 13:
                fail(f"{path.relative_to(ROOT)} has invalid bit-cost cases")
            operations: list[str] = []
            for case in cases:
                if (
                    not isinstance(case, dict)
                    or not isinstance(case.get("operation"), str)
                    or case.get("valid") is not True
                    or not isinstance(case.get("cost"), int)
                    or not isinstance(case.get("bound"), int)
                    or case["cost"] > case["bound"]
                ):
                    fail(f"{path.relative_to(ROOT)} has an invalid bit-cost case")
                operations.append(case["operation"])
            if (
                operations.count("add") != 3
                or operations.count("mul") != 3
                or operations.count("divmod") != 3
                or operations.count("xgcd") != 4
            ):
                fail(f"{path.relative_to(ROOT)} has the wrong bit-cost corpus")
        if schema == "normalforms.kannan-bachem-benchmark/v1":
            if benchmark.get("profile") != "research-kannan-bachem-v0.1.0":
                fail(f"{path.relative_to(ROOT)} has the wrong research profile")
            if benchmark.get("research_version") != "0.1.0":
                fail(f"{path.relative_to(ROOT)} has the wrong research version")
            policy = benchmark.get("policy")
            if (
                not isinstance(policy, dict)
                or policy.get("warmups") != 1
                or policy.get("measurements") != 7
            ):
                fail(f"{path.relative_to(ROOT)} has the wrong benchmark policy")
            cases = benchmark.get("cases")
            if not isinstance(cases, list) or len(cases) != 3:
                fail(f"{path.relative_to(ROOT)} has the wrong fixed corpus")
            for case in cases:
                if (
                    not isinstance(case, dict)
                    or case.get("valid") is not True
                    or not isinstance(case.get("bit_cost"), int)
                    or not isinstance(case.get("bit_bound"), int)
                    or case["bit_cost"] > case["bit_bound"]
                ):
                    fail(f"{path.relative_to(ROOT)} has an invalid research case")
            stages = benchmark.get("stages")
            if not isinstance(stages, list) or len(stages) != 4:
                fail(f"{path.relative_to(ROOT)} has the wrong stage count")
            for stage in stages:
                observations = (
                    stage.get("observations") if isinstance(stage, dict) else None
                )
                if not isinstance(observations, list) or len(observations) != 7:
                    fail(f"{path.relative_to(ROOT)} has invalid observations")
        if schema == "normalforms.modular-hnf-benchmark/v1":
            if benchmark.get("profile") != "research-modular-hnf-v0.1.0":
                fail(f"{path.relative_to(ROOT)} has the wrong research profile")
            if benchmark.get("research_version") != "0.1.0":
                fail(f"{path.relative_to(ROOT)} has the wrong research version")
            policy = benchmark.get("policy")
            if (
                not isinstance(policy, dict)
                or policy.get("warmups") != 1
                or policy.get("measurements") != 7
            ):
                fail(f"{path.relative_to(ROOT)} has the wrong benchmark policy")
            cases = benchmark.get("cases")
            if not isinstance(cases, list) or len(cases) != 3:
                fail(f"{path.relative_to(ROOT)} has the wrong fixed corpus")
            for case in cases:
                if (
                    not isinstance(case, dict)
                    or case.get("valid") is not True
                    or not isinstance(case.get("operation_total"), int)
                    or not isinstance(case.get("operation_bound"), int)
                    or case["operation_total"] > case["operation_bound"]
                    or not isinstance(case.get("modeled_bit_cost_bits"), int)
                    or not isinstance(case.get("modeled_bit_bound_bits"), int)
                    or case["modeled_bit_cost_bits"]
                    > case["modeled_bit_bound_bits"]
                ):
                    fail(f"{path.relative_to(ROOT)} has an invalid modular case")
            stages = benchmark.get("stages")
            if not isinstance(stages, list) or len(stages) != 4:
                fail(f"{path.relative_to(ROOT)} has the wrong stage count")
            for stage in stages:
                observations = (
                    stage.get("observations") if isinstance(stage, dict) else None
                )
                if not isinstance(observations, list) or len(observations) != 7:
                    fail(f"{path.relative_to(ROOT)} has invalid observations")
        if schema == "normalforms.lll-benchmark/v1":
            if benchmark.get("profile") != "research-lll-v0.1.0":
                fail(f"{path.relative_to(ROOT)} has the wrong research profile")
            if benchmark.get("research_version") != "0.1.0":
                fail(f"{path.relative_to(ROOT)} has the wrong research version")
            policy = benchmark.get("policy")
            if (
                not isinstance(policy, dict)
                or policy.get("warmups") != 1
                or policy.get("measurements") != 7
            ):
                fail(f"{path.relative_to(ROOT)} has the wrong benchmark policy")
            cases = benchmark.get("cases")
            if not isinstance(cases, list) or len(cases) != 4:
                fail(f"{path.relative_to(ROOT)} has the wrong fixed corpus")
            if any(
                not isinstance(case, dict) or case.get("valid") is not True
                for case in cases
            ):
                fail(f"{path.relative_to(ROOT)} has an invalid research case")
            for case in cases:
                if case.get("kind") == "profiled-full-rank" and (
                    not isinstance(case.get("operation_total"), int)
                    or not isinstance(case.get("operation_bound"), int)
                    or case["operation_total"] > case["operation_bound"]
                    or not isinstance(case.get("modeled_bit_cost"), int)
                    or not isinstance(case.get("modeled_bit_bound"), int)
                    or case["modeled_bit_cost"] > case["modeled_bit_bound"]
                ):
                    fail(f"{path.relative_to(ROOT)} has an invalid LLL profile")
            stages = benchmark.get("stages")
            if not isinstance(stages, list) or len(stages) != 5:
                fail(f"{path.relative_to(ROOT)} has the wrong stage count")
            for stage in stages:
                observations = (
                    stage.get("observations") if isinstance(stage, dict) else None
                )
                if not isinstance(observations, list) or len(observations) != 7:
                    fail(f"{path.relative_to(ROOT)} has invalid observations")
    for path in benchmark_csv:
        validate_csv(path)

    if version in {"1.1.0", "1.2.0", "1.2.1", "1.2.2"}:
        rational_baseline = load_json(
            ROOT
            / "benchmarks"
            / "baselines"
            / "v1.1.0-rational-canonical.json"
        )
        if (
            not isinstance(rational_baseline, dict)
            or rational_baseline.get("profile")
            != "v1.1.0-rational-canonical"
        ):
            fail("rational-canonical benchmark baseline is missing or invalid")
        case = rational_baseline.get("case")
        if not isinstance(case, dict) or case.get("factor_degrees") != [0, 2]:
            fail("rational-canonical factor-degree baseline is invalid")

    bit_cost_version = read("artifact/bit-cost/VERSION").strip()
    if bit_cost_version != "0.1.0":
        fail("bit-cost artifact version is inconsistent")
    require_contains("docs/BIT_COST_API.md", "research API 0.1.0")
    bit_cost_metadata = load_json(
        ROOT / "release/research-bit-cost-v0.1.0/zenodo.json"
    )
    if (
        not isinstance(bit_cost_metadata, dict)
        or bit_cost_metadata.get("version") != "research-bit-cost-0.1.0"
    ):
        fail("bit-cost archival metadata is missing or inconsistent")
    bit_cost_csv = ROOT / "benchmarks/baselines/research-bit-cost-v0.1.0.csv"
    if not bit_cost_csv.is_file():
        fail("bit-cost benchmark CSV is missing")
    with bit_cost_csv.open(newline="", encoding="utf-8") as handle:
        bit_cost_rows = list(csv.DictReader(handle))
    if (
        len(bit_cost_rows) != 20
        or sum(row.get("record") == "measurement" for row in bit_cost_rows) != 7
        or sum(row.get("record") == "case" for row in bit_cost_rows) != 13
    ):
        fail("bit-cost benchmark CSV has the wrong shape")

    kannan_version = read("artifact/kannan-bachem/VERSION").strip()
    if kannan_version != "0.1.0":
        fail("Kannan--Bachem artifact version is inconsistent")
    require_contains("docs/KANNAN_BACHEM_API.md", "Research version: 0.1.0")
    kannan_metadata = load_json(
        ROOT / "release/research-kannan-bachem-v0.1.0/zenodo.json"
    )
    if (
        not isinstance(kannan_metadata, dict)
        or kannan_metadata.get("version")
        != "research-kannan-bachem-0.1.0"
    ):
        fail("Kannan--Bachem archival metadata is missing or inconsistent")
    kannan_json = ROOT / "benchmarks/baselines/research-kannan-bachem-v0.1.0.json"
    kannan_csv = ROOT / "benchmarks/baselines/research-kannan-bachem-v0.1.0.csv"
    if not kannan_json.is_file() or not kannan_csv.is_file():
        fail("Kannan--Bachem benchmark baseline is missing")
    with kannan_csv.open(newline="", encoding="utf-8") as handle:
        kannan_rows = list(csv.DictReader(handle))
    stage_counts = {
        stage: sum(row.get("stage") == stage for row in kannan_rows)
        for stage in (
            "prepared_hnf",
            "smith_repeat",
            "smith_injection",
            "end_to_end",
        )
    }
    if stage_counts != {
        "prepared_hnf": 7,
        "smith_repeat": 7,
        "smith_injection": 7,
        "end_to_end": 21,
    }:
        fail("Kannan--Bachem benchmark CSV has the wrong shape")
    if not (ROOT / "artifact/kannan-bachem/Dockerfile").is_file():
        fail("Kannan--Bachem artifact Dockerfile is missing")

    modular_version = read("artifact/modular-hnf/VERSION").strip()
    if modular_version != "0.1.0":
        fail("modular-HNF artifact version is inconsistent")
    require_contains("docs/MODULAR_HNF_API.md", "Research version: 0.1.0")
    modular_metadata = load_json(
        ROOT / "release/research-modular-hnf-v0.1.0/zenodo.json"
    )
    if (
        not isinstance(modular_metadata, dict)
        or modular_metadata.get("version")
        != "research-modular-hnf-0.1.0"
    ):
        fail("modular-HNF archival metadata is missing or inconsistent")
    modular_json = ROOT / "benchmarks/baselines/research-modular-hnf-v0.1.0.json"
    modular_csv = ROOT / "benchmarks/baselines/research-modular-hnf-v0.1.0.csv"
    if not modular_json.is_file() or not modular_csv.is_file():
        fail("modular-HNF benchmark baseline is missing")
    with modular_csv.open(newline="", encoding="utf-8") as handle:
        modular_rows = list(csv.DictReader(handle))
    modular_stage_counts = {
        stage: sum(row.get("stage") == stage for row in modular_rows)
        for stage in ("scalar", "tall", "square", "end_to_end")
    }
    if modular_stage_counts != {
        "scalar": 7,
        "tall": 7,
        "square": 7,
        "end_to_end": 21,
    }:
        fail("modular-HNF benchmark CSV has the wrong shape")
    if not (ROOT / "artifact/modular-hnf/Dockerfile").is_file():
        fail("modular-HNF artifact Dockerfile is missing")

    lll_version = read("artifact/lll/VERSION").strip()
    if lll_version != "0.1.0":
        fail("LLL artifact version is inconsistent")
    require_contains("docs/LLL_API.md", "Research version: 0.1.0")
    lll_metadata = load_json(
        ROOT / "release/research-lll-v0.1.0/zenodo.json"
    )
    if (
        not isinstance(lll_metadata, dict)
        or lll_metadata.get("version") != "research-lll-0.1.0"
    ):
        fail("LLL archival metadata is missing or inconsistent")
    lll_json = ROOT / "benchmarks/baselines/research-lll-v0.1.0.json"
    lll_csv = ROOT / "benchmarks/baselines/research-lll-v0.1.0.csv"
    if not lll_json.is_file() or not lll_csv.is_file():
        fail("LLL benchmark baseline is missing")
    with lll_csv.open(newline="", encoding="utf-8") as handle:
        lll_rows = list(csv.DictReader(handle))
    lll_stage_counts = {
        stage: sum(row.get("stage") == stage for row in lll_rows)
        for stage in ("gauss", "dense", "dependent", "column", "end_to_end")
    }
    if lll_stage_counts != {
        "gauss": 7,
        "dense": 7,
        "dependent": 7,
        "column": 7,
        "end_to_end": 28,
    }:
        fail("LLL benchmark CSV has the wrong shape")
    if not (ROOT / "artifact/lll/Dockerfile").is_file():
        fail("LLL artifact Dockerfile is missing")

    cff_version = re.search(r"(?m)^version:\s*(\S+)\s*$", read("CITATION.cff"))
    if cff_version is None or cff_version.group(1) != version:
        fail("CITATION.cff version field is missing or inconsistent")

    if require_release_materials:
        release_root = ROOT / "release" / f"v{version}"
        notes = release_root / "RELEASE_NOTES.md"
        metadata = release_root / "zenodo.json"
        if not notes.is_file():
            fail(f"{notes.relative_to(ROOT)} is missing")
        release_zenodo = load_json(metadata)
        if not isinstance(release_zenodo, dict):
            fail(f"{metadata.relative_to(ROOT)} root is not an object")
        if release_zenodo.get("version") != version:
            fail(f"{metadata.relative_to(ROOT)} version is inconsistent")
        if release_zenodo != zenodo:
            fail("release Zenodo metadata differs from .zenodo.json")
        if not (ROOT / "artifact/core/Dockerfile").is_file():
            fail("artifact/core/Dockerfile is missing")

    print(
        "release metadata validated: "
        f"version={version} certificates={len(certificate_files)} "
        f"benchmark_json={len(benchmark_json)} benchmark_csv={len(benchmark_csv)} "
        f"mathlib={mathlib_revision}"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--version")
    parser.add_argument("--require-release-materials", action="store_true")
    args = parser.parse_args()

    version = args.version
    if version is None:
        lake = tomllib.loads(read("lakefile.toml"))
        value = lake.get("version")
        if not isinstance(value, str):
            parser.error("lakefile.toml does not contain a string version")
        version = value

    try:
        validate(version, args.require_release_materials)
    except RuntimeError as error:
        print(f"release metadata validation failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
