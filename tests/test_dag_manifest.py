"""Tests for tools/infra/dag_manifest.py — manifest building helpers."""
from __future__ import annotations

from pathlib import Path

import pytest

from tools.infra.dag_manifest import (
    MANIFEST_SCHEMA_VERSION,
    _coverage_summary,
    _file_info,
)

REPO_ROOT = Path(__file__).resolve().parents[1]


# ---------------------------------------------------------------------------
# _file_info
# ---------------------------------------------------------------------------

def test_file_info_missing_file(tmp_path: Path) -> None:
    p = tmp_path / "no_such_file.json"
    info = _file_info(p, tmp_path)
    assert info["exists"] is False
    assert "mtime" not in info
    assert "sizeBytes" not in info


def test_file_info_existing_file(tmp_path: Path) -> None:
    p = tmp_path / "report.json"
    p.write_text('{"x": 1}', encoding="utf-8")
    info = _file_info(p, tmp_path)
    assert info["exists"] is True
    assert "mtime" in info
    assert "sizeBytes" in info
    assert info["sizeBytes"] == p.stat().st_size


def test_file_info_path_is_relative_to_root(tmp_path: Path) -> None:
    sub = tmp_path / "subdir"
    sub.mkdir()
    p = sub / "graph.json"
    p.write_text("{}", encoding="utf-8")
    info = _file_info(p, tmp_path)
    assert info["path"] == "subdir/graph.json"


def test_file_info_empty_file(tmp_path: Path) -> None:
    p = tmp_path / "empty.json"
    p.write_text("", encoding="utf-8")
    info = _file_info(p, tmp_path)
    assert info["exists"] is True
    assert info["sizeBytes"] == 0


# ---------------------------------------------------------------------------
# _coverage_summary
# ---------------------------------------------------------------------------

def test_coverage_summary_from_summary_graph_coverage() -> None:
    report = {"summary": {"graph_coverage": {"total": 100, "covered": 80}}}
    result = _coverage_summary(report)
    assert result == {"total": 100, "covered": 80}


def test_coverage_summary_from_top_level_coverage() -> None:
    report = {"coverage": {"total": 50, "missing": 5}}
    result = _coverage_summary(report)
    assert result == {"total": 50, "missing": 5}


def test_coverage_summary_empty_report() -> None:
    result = _coverage_summary({})
    assert result == {}


def test_coverage_summary_none_summary() -> None:
    result = _coverage_summary({"summary": None})
    assert result == {}


def test_coverage_summary_summary_without_graph_coverage_key() -> None:
    report = {"summary": {"other_metric": 42}}
    result = _coverage_summary(report)
    assert result == {}


def test_coverage_summary_non_dict_coverage_returns_empty() -> None:
    report = {"coverage": "some string"}
    result = _coverage_summary(report)
    assert result == {}


# ---------------------------------------------------------------------------
# MANIFEST_SCHEMA_VERSION constant
# ---------------------------------------------------------------------------

def test_manifest_schema_version_is_integer() -> None:
    assert isinstance(MANIFEST_SCHEMA_VERSION, int)
    assert MANIFEST_SCHEMA_VERSION >= 1
