"""Tests for tools/infra/dag_status.py — status formatting and timestamp parsing helpers."""
from __future__ import annotations

from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

from tools.infra.dag_status import (
    extract_graph_coverage,
    file_mtime,
    format_age,
    format_sync,
    parse_iso_timestamp,
    timing_summary,
    top_label,
)


# ---------------------------------------------------------------------------
# parse_iso_timestamp
# ---------------------------------------------------------------------------

def test_parse_iso_timestamp_valid_utc() -> None:
    result = parse_iso_timestamp("2026-01-15T10:30:00+00:00")
    assert result is not None
    assert result.year == 2026
    assert result.month == 1


def test_parse_iso_timestamp_valid_local() -> None:
    result = parse_iso_timestamp("2026-05-09T12:00:00")
    assert result is not None
    assert result.day == 9


def test_parse_iso_timestamp_none_input() -> None:
    assert parse_iso_timestamp(None) is None


def test_parse_iso_timestamp_empty_string() -> None:
    assert parse_iso_timestamp("") is None


def test_parse_iso_timestamp_invalid_string() -> None:
    assert parse_iso_timestamp("not-a-date") is None


def test_parse_iso_timestamp_integer_input() -> None:
    assert parse_iso_timestamp(12345) is None


# ---------------------------------------------------------------------------
# format_age
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("seconds, expected", [
    (0, "0s"),
    (30, "30s"),
    (61, "1m 1s"),
    (3601, "1h 0m"),
    (3660, "1h 1m"),
    (86401, "1d 0h"),
    (90061, "1d 1h"),
])
def test_format_age(seconds: int, expected: str) -> None:
    assert format_age(timedelta(seconds=seconds)) == expected


def test_format_age_large_days() -> None:
    result = format_age(timedelta(days=10, hours=3))
    assert result.startswith("10d")


# ---------------------------------------------------------------------------
# format_sync
# ---------------------------------------------------------------------------

def test_format_sync_in_sync_zero() -> None:
    assert format_sync(0.0) == "in sync"


def test_format_sync_within_tolerance() -> None:
    assert format_sync(299.0) == "in sync"
    assert format_sync(-299.0) == "in sync"


def test_format_sync_newer() -> None:
    result = format_sync(3601.0)
    assert "newer" in result


def test_format_sync_older() -> None:
    result = format_sync(-3601.0)
    assert "older" in result


def test_format_sync_custom_tolerance() -> None:
    assert format_sync(100.0, tolerance_seconds=200) == "in sync"
    assert "newer" in format_sync(201.0, tolerance_seconds=200)


# ---------------------------------------------------------------------------
# file_mtime
# ---------------------------------------------------------------------------

def test_file_mtime_returns_none_for_missing_file(tmp_path: Path) -> None:
    assert file_mtime(tmp_path / "no_such_file.txt") is None


def test_file_mtime_returns_datetime_for_existing_file(tmp_path: Path) -> None:
    p = tmp_path / "existing.txt"
    p.write_text("content", encoding="utf-8")
    result = file_mtime(p)
    assert result is not None
    assert isinstance(result, datetime)
    # Should be timezone-aware UTC
    assert result.tzinfo is not None


# ---------------------------------------------------------------------------
# extract_graph_coverage
# ---------------------------------------------------------------------------

def test_extract_graph_coverage_from_summary_key() -> None:
    report = {"summary": {"graph_coverage": {"total": 100, "covered": 80}}}
    result = extract_graph_coverage(report)
    assert result == {"total": 100, "covered": 80}


def test_extract_graph_coverage_from_top_level_coverage() -> None:
    report = {"coverage": {"total": 50, "missing": 5}}
    result = extract_graph_coverage(report)
    assert result == {"total": 50, "missing": 5}


def test_extract_graph_coverage_empty_report() -> None:
    assert extract_graph_coverage({}) == {}


def test_extract_graph_coverage_none_summary() -> None:
    assert extract_graph_coverage({"summary": None}) == {}


def test_extract_graph_coverage_summary_without_graph_coverage() -> None:
    report = {"summary": {"other_key": 42}}
    assert extract_graph_coverage(report) == {}


# ---------------------------------------------------------------------------
# top_label
# ---------------------------------------------------------------------------

def test_top_label_returns_dash_for_empty() -> None:
    assert top_label([]) == "-"


def test_top_label_returns_dash_for_none() -> None:
    assert top_label(None) == "-"


def test_top_label_returns_label_with_count() -> None:
    rows = [{"label": "InfoGeometry.OperatorAlgebra", "count": 42}]
    result = top_label(rows)
    assert result == "InfoGeometry.OperatorAlgebra (42)"


def test_top_label_uses_first_row() -> None:
    rows = [
        {"label": "first", "count": 10},
        {"label": "second", "count": 5},
    ]
    assert top_label(rows) == "first (10)"


# ---------------------------------------------------------------------------
# timing_summary
# ---------------------------------------------------------------------------

def test_timing_summary_empty() -> None:
    assert timing_summary([]) == "-"


def test_timing_summary_single_row() -> None:
    rows = [{"label": "generate_theorem_surface_index.py", "elapsed_ms": 1200}]
    result = timing_summary(rows)
    assert "generate_theorem_surface_index.py" in result
    assert "1.2s" in result


def test_timing_summary_multiple_rows_joined_with_semicolon() -> None:
    rows = [
        {"label": "step_a", "elapsed_ms": 100},
        {"label": "step_b", "elapsed_ms": 200},
    ]
    result = timing_summary(rows)
    assert " " in result or ";" in result
    assert "step_a" in result
    assert "step_b" in result


def test_timing_summary_list_label() -> None:
    rows = [{"label": ["tools/infra", "generate.py"], "elapsed_ms": 50}]
    result = timing_summary(rows)
    assert "tools/infra generate.py" in result
