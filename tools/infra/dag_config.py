#!/usr/bin/env python3
from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tools.infra.artifacts import load_json_dict
from tools.pathing import normalize_user_path, repo_root


DEFAULT_DAG_TOOLCHAIN_FILE = "dag-toolchain.json"
LOCAL_DAG_TOOLCHAIN_FILE = "dag-toolchain.local.json"


@dataclass(frozen=True)
class DagBuildConfig:
    build_target: str
    import_root: str
    namespace_filter: str
    run_mode: str


@dataclass(frozen=True)
class DagAuthoritativeArtifacts:
    index_dir: Path
    graph_out: Path
    structure_out: Path


@dataclass(frozen=True)
class DagDerivedReports:
    coverage_report_json: Path
    report_sequence: tuple[tuple[str, ...], ...]


@dataclass(frozen=True)
class DagCoveragePolicy:
    require_full_coverage: bool
    max_missing_decl_files: int


@dataclass(frozen=True)
class DagLeakagePolicy:
    report_sidecar: Path
    warn_only: bool


@dataclass(frozen=True)
class DagPolicies:
    coverage: DagCoveragePolicy
    leakage: DagLeakagePolicy


@dataclass(frozen=True)
class DagToolchainConfig:
    config_path: Path
    schema_version: int
    build: DagBuildConfig
    authoritative_artifacts: DagAuthoritativeArtifacts
    derived_reports: DagDerivedReports
    policies: DagPolicies


def _require_str(raw: dict[str, Any], key: str) -> str:
    value = raw.get(key)
    if not isinstance(value, str) or not value:
        raise ValueError(f"dag config field `{key}` must be a non-empty string")
    return value


def _require_int(raw: dict[str, Any], key: str) -> int:
    value = raw.get(key)
    if not isinstance(value, int):
        raise ValueError(f"dag config field `{key}` must be an integer")
    return value


def _require_dict(raw: dict[str, Any], key: str) -> dict[str, Any]:
    value = raw.get(key)
    if not isinstance(value, dict):
        raise ValueError(f"dag config field `{key}` must be an object")
    return value


def _resolve_repo_path(root: Path, raw: str) -> Path:
    path = Path(raw)
    if path.is_absolute():
        return path
    return (root / path).resolve()


def resolve_dag_toolchain_path(config: str | Path | None = None) -> Path:
    root = repo_root()
    if config is not None:
        raw = str(config)
    else:
        raw = os.environ.get("DAG_TOOLCHAIN_CONFIG")
    if raw:
        return normalize_user_path(raw, root / DEFAULT_DAG_TOOLCHAIN_FILE)
    local_path = root / LOCAL_DAG_TOOLCHAIN_FILE
    if local_path.exists():
        return local_path
    return root / DEFAULT_DAG_TOOLCHAIN_FILE


def repo_display_path(path: Path, root: Path | None = None) -> str:
    root_path = root or repo_root()
    try:
        return str(path.relative_to(root_path))
    except ValueError:
        return str(path)


def load_dag_toolchain_config(config: str | Path | None = None) -> DagToolchainConfig:
    root = repo_root()
    config_path = resolve_dag_toolchain_path(config)
    raw = load_json_dict(config_path)

    build_raw = _require_dict(raw, "build")
    authoritative_artifacts_raw = _require_dict(raw, "authoritativeArtifacts")
    derived_reports_raw = _require_dict(raw, "derivedReports")
    policies_raw = _require_dict(raw, "policies")
    coverage_policy_raw = _require_dict(policies_raw, "coverage")
    leakage_policy_raw = _require_dict(policies_raw, "leakage")
    report_sequence_raw = derived_reports_raw.get("reportSequence", [])
    if not isinstance(report_sequence_raw, list):
        raise ValueError("dag config field `derivedReports.reportSequence` must be a list")

    report_sequence: list[tuple[str, ...]] = []
    for i, step in enumerate(report_sequence_raw):
        if not isinstance(step, list) or not step or not all(isinstance(arg, str) and arg for arg in step):
            raise ValueError(f"dag config field `derivedReports.reportSequence[{i}]` must be a non-empty string list")
        report_sequence.append(tuple(step))

    run_mode = _require_str(build_raw, "runMode")
    if run_mode not in {"exe", "run"}:
        raise ValueError("dag config field `build.runMode` must be `exe` or `run`")

    return DagToolchainConfig(
        config_path=config_path.resolve(),
        schema_version=_require_int(raw, "schemaVersion"),
        build=DagBuildConfig(
            build_target=_require_str(build_raw, "buildTarget"),
            import_root=_require_str(build_raw, "importRoot"),
            namespace_filter=_require_str(build_raw, "namespaceFilter"),
            run_mode=run_mode,
        ),
        authoritative_artifacts=DagAuthoritativeArtifacts(
            index_dir=_resolve_repo_path(root, _require_str(authoritative_artifacts_raw, "indexDir")),
            graph_out=_resolve_repo_path(root, _require_str(authoritative_artifacts_raw, "graphOut")),
            structure_out=_resolve_repo_path(root, _require_str(authoritative_artifacts_raw, "structureOut")),
        ),
        derived_reports=DagDerivedReports(
            coverage_report_json=_resolve_repo_path(root, _require_str(derived_reports_raw, "coverageReportJson")),
            report_sequence=tuple(report_sequence),
        ),
        policies=DagPolicies(
            coverage=DagCoveragePolicy(
                require_full_coverage=bool(coverage_policy_raw.get("requireFullCoverage", False)),
                max_missing_decl_files=int(coverage_policy_raw.get("maxMissingDeclFiles", 0)),
            ),
            leakage=DagLeakagePolicy(
                report_sidecar=_resolve_repo_path(root, _require_str(leakage_policy_raw, "reportSidecar")),
                warn_only=bool(leakage_policy_raw.get("warnOnly", True)),
            ),
        ),
    )
