"""Tests for tools/infra/dag_config.py — DAG toolchain config loading and resolution."""
from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from tools.infra.dag_config import (
    DagBuildConfig,
    DagToolchainConfig,
    load_dag_toolchain_config,
    repo_display_path,
    resolve_dag_toolchain_path,
)


REPO_ROOT = Path(__file__).resolve().parents[2]


def _write_minimal_config(path: Path, *, schema_version: int = 2) -> None:
    """Write a valid minimal dag-toolchain.json for tests."""
    config = {
        "schemaVersion": schema_version,
        "build": {
            "buildTarget": "InfoGeometry.All",
            "importRoot": "InfoGeometry.All",
            "namespaceFilter": "InfoGeometry",
            "runMode": "exe",
        },
        "authoritativeArtifacts": {
            "indexDir": "artifacts/dag/index",
            "graphOut": "artifacts/dag/full_graph.json",
            "structureOut": "artifacts/dag/structural-topology.json",
        },
        "derivedReports": {
            "coverageReportJson": "reports/dag/true-root-order.json",
            "reportSequence": [
                ["tools/infra/generate_theorem_surface_index.py"],
            ],
        },
        "policies": {
            "coverage": {
                "requireFullCoverage": False,
                "maxMissingDeclFiles": 10,
            },
            "leakage": {
                "reportSidecar": "artifacts/dag/index/edge-leakage.json",
                "warnOnly": True,
            },
        },
    }
    path.write_text(json.dumps(config), encoding="utf-8")


# ---------------------------------------------------------------------------
# load_dag_toolchain_config — loads actual repo config
# ---------------------------------------------------------------------------

def test_load_actual_config_returns_correct_build_target() -> None:
    config = load_dag_toolchain_config()
    assert config.build.build_target == "InfoGeometry.All"


def test_load_actual_config_report_sequence_is_non_empty() -> None:
    config = load_dag_toolchain_config()
    assert len(config.derived_reports.report_sequence) > 0


def test_load_actual_config_schema_version_is_2() -> None:
    config = load_dag_toolchain_config()
    assert config.schema_version == 2


def test_load_actual_config_authoritative_artifacts_are_paths() -> None:
    config = load_dag_toolchain_config()
    assert isinstance(config.authoritative_artifacts.index_dir, Path)
    assert isinstance(config.authoritative_artifacts.graph_out, Path)


def test_load_actual_config_policies_present() -> None:
    config = load_dag_toolchain_config()
    assert isinstance(config.policies.coverage.require_full_coverage, bool)
    assert isinstance(config.policies.coverage.max_missing_decl_files, int)


# ---------------------------------------------------------------------------
# load_dag_toolchain_config — from tmp file
# ---------------------------------------------------------------------------

def test_load_config_from_explicit_path(tmp_path: Path) -> None:
    p = tmp_path / "dag-toolchain.json"
    _write_minimal_config(p)
    config = load_dag_toolchain_config(p)
    assert config.build.build_target == "InfoGeometry.All"
    assert config.build.import_root == "InfoGeometry.All"
    assert config.build.namespace_filter == "InfoGeometry"
    assert config.build.run_mode == "exe"


def test_load_config_report_sequence_is_tuple_of_tuples(tmp_path: Path) -> None:
    p = tmp_path / "dag-toolchain.json"
    _write_minimal_config(p)
    config = load_dag_toolchain_config(p)
    seq = config.derived_reports.report_sequence
    assert isinstance(seq, tuple)
    assert isinstance(seq[0], tuple)


def test_load_config_paths_resolve_under_repo_root(tmp_path: Path) -> None:
    p = tmp_path / "dag-toolchain.json"
    _write_minimal_config(p)
    config = load_dag_toolchain_config(p)
    # All artifact paths should be absolute
    assert config.authoritative_artifacts.index_dir.is_absolute()
    assert config.authoritative_artifacts.graph_out.is_absolute()


def test_load_config_raises_on_missing_field(tmp_path: Path) -> None:
    # build section is present but empty → missing buildTarget inside it
    p = tmp_path / "bad-config.json"
    build = {"importRoot": "X", "namespaceFilter": "X", "runMode": "exe"}  # missing buildTarget
    p.write_text(json.dumps({"schemaVersion": 2, "build": build,
                             "authoritativeArtifacts": {"indexDir": "a", "graphOut": "b", "structureOut": "c"},
                             "derivedReports": {"coverageReportJson": "r", "reportSequence": []},
                             "policies": {}}), encoding="utf-8")
    with pytest.raises(ValueError):
        load_dag_toolchain_config(p)


def test_load_config_raises_on_missing_build_section(tmp_path: Path) -> None:
    p = tmp_path / "bad-config.json"
    p.write_text(json.dumps({"schemaVersion": 2}), encoding="utf-8")
    with pytest.raises(ValueError):
        load_dag_toolchain_config(p)


# ---------------------------------------------------------------------------
# resolve_dag_toolchain_path
# ---------------------------------------------------------------------------

def test_resolve_toolchain_path_explicit(tmp_path: Path) -> None:
    p = tmp_path / "custom.json"
    p.touch()
    result = resolve_dag_toolchain_path(str(p))
    assert result == p


def test_resolve_toolchain_path_env_var(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    p = tmp_path / "env.json"
    p.touch()
    monkeypatch.setenv("DAG_TOOLCHAIN_CONFIG", str(p))
    result = resolve_dag_toolchain_path(None)
    assert result == p


def test_resolve_toolchain_path_default_fallback() -> None:
    result = resolve_dag_toolchain_path(None)
    # Should resolve to either local or default dag-toolchain.json in repo root
    assert result.name in ("dag-toolchain.json", "dag-toolchain.local.json")
    assert result.parent == REPO_ROOT


# ---------------------------------------------------------------------------
# repo_display_path
# ---------------------------------------------------------------------------

def test_repo_display_path_relative_to_root() -> None:
    path = REPO_ROOT / "artifacts" / "dag" / "graph.json"
    display = repo_display_path(path, REPO_ROOT)
    assert display == "artifacts/dag/graph.json"


def test_repo_display_path_outside_root(tmp_path: Path) -> None:
    path = tmp_path / "external" / "file.json"
    display = repo_display_path(path, REPO_ROOT)
    assert "external" in display
    assert display == str(path)


def test_repo_display_path_uses_repo_root_default() -> None:
    path = REPO_ROOT / "dag-toolchain.json"
    display = repo_display_path(path)
    assert display == "dag-toolchain.json"
