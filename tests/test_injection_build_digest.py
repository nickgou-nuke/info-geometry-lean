"""Tests for tools/infra/injection_build_digest.py — packet digest helper utilities."""
from __future__ import annotations

import pytest

from tools.infra.injection_build_digest import (
    as_list,
    format_sources_md,
    latest_history_time,
    normalize_sources,
)


# ---------------------------------------------------------------------------
# normalize_sources
# ---------------------------------------------------------------------------

def test_normalize_sources_empty_packet() -> None:
    result = normalize_sources({})
    assert result == []


def test_normalize_sources_empty_sources_list() -> None:
    packet = {"research": {"sources": []}}
    result = normalize_sources(packet)
    assert result == []


def test_normalize_sources_dict_entries() -> None:
    packet = {
        "research": {
            "sources": [
                {"kind": "paper", "ref": "arXiv:1706.03762", "title": "Attention Is All You Need", "date": "2017"},
                {"kind": "book", "ref": "doi:10.1007/b97779", "title": "Matrix Analysis"},
            ]
        }
    }
    result = normalize_sources(packet)
    assert len(result) == 2
    assert result[0]["kind"] == "paper"
    assert result[0]["ref"] == "arXiv:1706.03762"
    assert result[0]["title"] == "Attention Is All You Need"
    assert result[1]["kind"] == "book"


def test_normalize_sources_plain_string_entries() -> None:
    packet = {"research": {"sources": ["https://example.com/paper.pdf", "https://mathlib.org"]}}
    result = normalize_sources(packet)
    assert len(result) == 2
    assert all(r["kind"] == "source" for r in result)
    assert result[0]["ref"] == "https://example.com/paper.pdf"


def test_normalize_sources_skips_empty_refs() -> None:
    packet = {
        "research": {
            "sources": [
                {"kind": "paper", "ref": ""},
                {"kind": "book", "ref": "valid-ref"},
                "",  # empty string
            ]
        }
    }
    result = normalize_sources(packet)
    assert len(result) == 1
    assert result[0]["ref"] == "valid-ref"


def test_normalize_sources_mixed_types() -> None:
    packet = {
        "research": {
            "sources": [
                {"ref": "doi:xxx", "kind": "paper"},
                "plain-url",
                None,  # str(None) == "None" → ref="None" (non-empty) → included
                42,    # str(42) == "42" → ref="42" (non-empty) → included
            ]
        }
    }
    result = normalize_sources(packet)
    # All four entries produce non-empty refs; None and 42 become "None" and "42"
    assert len(result) == 4
    refs = [r["ref"] for r in result]
    assert "doi:xxx" in refs
    assert "plain-url" in refs


# ---------------------------------------------------------------------------
# format_sources_md
# ---------------------------------------------------------------------------

def test_format_sources_md_empty_sources() -> None:
    md, keys = format_sources_md([])
    assert "no sources" in md.lower()
    assert keys == []


def test_format_sources_md_single_source() -> None:
    sources = [{"kind": "paper", "ref": "arXiv:1706.03762", "title": "", "date": ""}]
    md, keys = format_sources_md(sources)
    assert keys == ["S1"]
    assert "[S1]" in md
    assert "PAPER" in md
    assert "arXiv:1706.03762" in md


def test_format_sources_md_with_title_and_date() -> None:
    sources = [{"kind": "book", "ref": "doi:xxx", "title": "Matrix Analysis", "date": "1985"}]
    md, keys = format_sources_md(sources)
    assert "Matrix Analysis" in md
    assert "1985" in md


def test_format_sources_md_multiple_sources() -> None:
    sources = [
        {"kind": "paper", "ref": "ref1", "title": "", "date": ""},
        {"kind": "web", "ref": "https://example.com", "title": "Example", "date": ""},
    ]
    md, keys = format_sources_md(sources)
    assert len(keys) == 2
    assert keys == ["S1", "S2"]
    assert "[S1]" in md
    assert "[S2]" in md


def test_format_sources_md_returns_multiline_string() -> None:
    sources = [
        {"kind": "a", "ref": "r1", "title": "", "date": ""},
        {"kind": "b", "ref": "r2", "title": "", "date": ""},
    ]
    md, _ = format_sources_md(sources)
    lines = md.strip().split("\n")
    assert len(lines) == 2


# ---------------------------------------------------------------------------
# as_list
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("input_val, expected", [
    ([], []),
    (["a", "b", "c"], ["a", "b", "c"]),
    ("single string", ["single string"]),
    ("", []),
    (None, []),
    (42, []),
    (["x", "", "  "], ["x"]),
])
def test_as_list(input_val, expected: list) -> None:
    assert as_list(input_val) == expected


# ---------------------------------------------------------------------------
# latest_history_time
# ---------------------------------------------------------------------------

def test_latest_history_time_empty_history() -> None:
    assert latest_history_time({}, "fallback") == "fallback"


def test_latest_history_time_single_event() -> None:
    packet = {"history": [{"at": "2026-01-15T10:00:00+00:00", "event": "created"}]}
    result = latest_history_time(packet, "fallback")
    assert result == "2026-01-15T10:00:00+00:00"


def test_latest_history_time_returns_latest_of_multiple() -> None:
    packet = {
        "history": [
            {"at": "2026-01-01T00:00:00+00:00"},
            {"at": "2026-03-15T12:00:00+00:00"},
            {"at": "2026-02-10T08:00:00+00:00"},
        ]
    }
    result = latest_history_time(packet, "fallback")
    # max() on ISO strings gives chronologically latest (lexicographic == chronological for UTC)
    assert result == "2026-03-15T12:00:00+00:00"


def test_latest_history_time_skips_entries_without_at() -> None:
    packet = {
        "history": [
            {"event": "no timestamp here"},
            {"at": "2026-01-05T00:00:00+00:00"},
        ]
    }
    result = latest_history_time(packet, "fallback")
    assert result == "2026-01-05T00:00:00+00:00"


def test_latest_history_time_all_empty_falls_back() -> None:
    packet = {"history": [{"event": "no time"}]}
    assert latest_history_time(packet, "default-ts") == "default-ts"
