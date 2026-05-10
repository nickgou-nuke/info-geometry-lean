"""Tests for tools/infra/timings.py — indexer timing log parsing and payload building."""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path

import pytest

from tools.infra.timings import (
    INDEXER_TIMING_LOG_NAME,
    INDEXER_TIMING_JSON_NAME,
    INDEXER_TIMING_SCHEMA_VERSION,
    build_indexer_timing_payload,
    format_elapsed_ms,
    indexer_timing_json_path,
    indexer_timing_log_path,
    load_indexer_timing,
    parse_indexer_timing_log,
    timing_matches_meta,
    top_timing_rows,
    write_indexer_timing_sidecar,
)


# ---------------------------------------------------------------------------
# path helpers
# ---------------------------------------------------------------------------

def test_indexer_timing_log_path(tmp_path: Path) -> None:
    assert indexer_timing_log_path(tmp_path) == tmp_path / INDEXER_TIMING_LOG_NAME


def test_indexer_timing_json_path(tmp_path: Path) -> None:
    assert indexer_timing_json_path(tmp_path) == tmp_path / INDEXER_TIMING_JSON_NAME


# ---------------------------------------------------------------------------
# parse_indexer_timing_log
# ---------------------------------------------------------------------------

def _write_timing_log(path: Path, lines: list[str]) -> None:
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def test_parse_timing_log_returns_none_when_missing(tmp_path: Path) -> None:
    result = parse_indexer_timing_log(tmp_path / "no_log.log")
    assert result is None


def test_parse_timing_log_returns_none_on_empty_log(tmp_path: Path) -> None:
    log = tmp_path / "empty.log"
    log.write_text("", encoding="utf-8")
    assert parse_indexer_timing_log(log) is None


def test_parse_timing_log_single_stage(tmp_path: Path) -> None:
    log = tmp_path / INDEXER_TIMING_LOG_NAME
    _write_timing_log(log, [
        "[Indexer timing] parse declarations: 120 ms",
        "[Indexer timing] total runIndexer: 500 ms",
    ])
    result = parse_indexer_timing_log(log)
    assert result is not None
    assert result["total_ms"] == 500
    assert result["import_modules_ms"] is None
    assert len(result["stages"]) == 1
    assert result["stages"][0] == {"label": "parse declarations", "elapsed_ms": 120}


def test_parse_timing_log_import_modules(tmp_path: Path) -> None:
    log = tmp_path / INDEXER_TIMING_LOG_NAME
    _write_timing_log(log, [
        "[Indexer timing] importModules (phase 1): 3000 ms",
        "[Indexer timing] total runIndexer: 4000 ms",
    ])
    result = parse_indexer_timing_log(log)
    assert result is not None
    assert result["import_modules_ms"] == 3000
    assert result["stages"] == []


def test_parse_timing_log_multiple_stages(tmp_path: Path) -> None:
    log = tmp_path / INDEXER_TIMING_LOG_NAME
    _write_timing_log(log, [
        "[Indexer timing] stage A: 10 ms",
        "[Indexer timing] stage B: 20 ms",
        "[Indexer timing] stage C: 30 ms",
        "[Indexer timing] total runIndexer: 100 ms",
    ])
    result = parse_indexer_timing_log(log)
    assert result is not None
    assert len(result["stages"]) == 3
    assert result["total_ms"] == 100


def test_parse_timing_log_ignores_non_matching_lines(tmp_path: Path) -> None:
    log = tmp_path / INDEXER_TIMING_LOG_NAME
    _write_timing_log(log, [
        "INFO: starting indexer",
        "[Indexer timing] step: 50 ms",
        "DEBUG: some other line",
    ])
    result = parse_indexer_timing_log(log)
    assert result is not None
    assert len(result["stages"]) == 1


# ---------------------------------------------------------------------------
# build_indexer_timing_payload
# ---------------------------------------------------------------------------

def test_build_payload_returns_none_when_log_missing(tmp_path: Path) -> None:
    result = build_indexer_timing_payload(
        log_path=tmp_path / "missing.log",
        meta={"oleanHash": "abc"},
    )
    assert result is None


def test_build_payload_includes_schema_version(tmp_path: Path) -> None:
    log = tmp_path / INDEXER_TIMING_LOG_NAME
    _write_timing_log(log, ["[Indexer timing] phase: 10 ms", "[Indexer timing] total runIndexer: 50 ms"])
    result = build_indexer_timing_payload(log_path=log, meta={"oleanHash": "h123"})
    assert result is not None
    assert result["schemaVersion"] == INDEXER_TIMING_SCHEMA_VERSION
    assert result["oleanHash"] == "h123"
    assert result["total_ms"] == 50
    assert "recordedAt" in result


def test_build_payload_with_none_meta(tmp_path: Path) -> None:
    log = tmp_path / INDEXER_TIMING_LOG_NAME
    _write_timing_log(log, ["[Indexer timing] total runIndexer: 10 ms"])
    result = build_indexer_timing_payload(log_path=log, meta=None)
    assert result is not None
    assert result["oleanHash"] == ""


# ---------------------------------------------------------------------------
# write_indexer_timing_sidecar / load_indexer_timing
# ---------------------------------------------------------------------------

def test_write_and_load_timing_sidecar(tmp_path: Path) -> None:
    log = tmp_path / INDEXER_TIMING_LOG_NAME
    _write_timing_log(log, [
        "[Indexer timing] stage X: 42 ms",
        "[Indexer timing] total runIndexer: 200 ms",
    ])
    meta = {"oleanHash": "hash_test", "schemaVersion": INDEXER_TIMING_SCHEMA_VERSION}
    sidecar_path = write_indexer_timing_sidecar(tmp_path, meta)
    assert sidecar_path is not None
    assert sidecar_path.exists()
    loaded = load_indexer_timing(tmp_path)
    assert loaded is not None
    assert loaded["total_ms"] == 200


def test_load_indexer_timing_returns_none_when_missing(tmp_path: Path) -> None:
    result = load_indexer_timing(tmp_path)
    assert result is None


# ---------------------------------------------------------------------------
# format_elapsed_ms
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("raw, expected", [
    (0, "0ms"),
    (1, "1ms"),
    (999, "999ms"),
    (1000, "1.0s"),
    (1500, "1.5s"),
    (60000, "1m 0.0s"),
    (None, "-"),
    ("not_a_number", "-"),
])
def test_format_elapsed_ms(raw, expected: str) -> None:
    assert format_elapsed_ms(raw) == expected


# ---------------------------------------------------------------------------
# top_timing_rows
# ---------------------------------------------------------------------------

def test_top_timing_rows_returns_empty_for_none() -> None:
    assert top_timing_rows(None) == []


def test_top_timing_rows_returns_empty_for_no_stages() -> None:
    assert top_timing_rows({"stages": []}) == []


def test_top_timing_rows_returns_top_3_by_elapsed() -> None:
    payload = {
        "stages": [
            {"label": "a", "elapsed_ms": 10},
            {"label": "b", "elapsed_ms": 300},
            {"label": "c", "elapsed_ms": 50},
            {"label": "d", "elapsed_ms": 200},
            {"label": "e", "elapsed_ms": 1},
        ]
    }
    rows = top_timing_rows(payload, limit=3)
    assert len(rows) == 3
    assert rows[0]["label"] == "b"
    assert rows[1]["label"] == "d"


def test_top_timing_rows_custom_limit(tmp_path: Path) -> None:
    payload = {
        "stages": [
            {"label": str(i), "elapsed_ms": i * 10}
            for i in range(10)
        ]
    }
    rows = top_timing_rows(payload, limit=5)
    assert len(rows) == 5


# ---------------------------------------------------------------------------
# timing_matches_meta
# ---------------------------------------------------------------------------

def test_timing_matches_meta_none_payload() -> None:
    assert timing_matches_meta(None, {"oleanHash": "x"}) is None


def test_timing_matches_meta_none_meta() -> None:
    assert timing_matches_meta({"oleanHash": "x"}, None) is None


def test_timing_matches_meta_true_when_hash_and_timestamp_match() -> None:
    payload = {"oleanHash": "abc", "artifactTimestamp": "2026-01-01T00:00:00+00:00"}
    meta = {"oleanHash": "abc", "timestamp": "2026-01-01T00:00:00+00:00"}
    result = timing_matches_meta(payload, meta)
    assert result is True


def test_timing_matches_meta_false_when_hash_differs() -> None:
    payload = {"oleanHash": "abc", "artifactTimestamp": "2026-01-01T00:00:00+00:00"}
    meta = {"oleanHash": "xyz", "timestamp": "2026-01-01T00:00:00+00:00"}
    result = timing_matches_meta(payload, meta)
    assert result is False
