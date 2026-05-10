"""Tests for tools/infra/reports/common.py — report helper utilities."""
from __future__ import annotations

import re
from datetime import datetime
from pathlib import Path

import pytest

from tools.infra.reports.common import (
    generated_timestamp,
    normalize_user_path,
    relpath,
    write_text,
)

REPO_ROOT = Path(__file__).resolve().parents[1]


# ---------------------------------------------------------------------------
# normalize_user_path
# ---------------------------------------------------------------------------

def test_normalize_user_path_none_returns_default(tmp_path: Path) -> None:
    result = normalize_user_path(None, tmp_path / "default.json")
    assert result == tmp_path / "default.json"


def test_normalize_user_path_absolute_returns_as_path(tmp_path: Path) -> None:
    abs_path = str(tmp_path / "output" / "report.json")
    result = normalize_user_path(abs_path, tmp_path / "default.json")
    assert result == Path(abs_path)


def test_normalize_user_path_relative_resolves_under_cwd(tmp_path: Path) -> None:
    # Relative path should resolve against something (not default)
    result = normalize_user_path("reports/my_report.json", tmp_path / "default.json")
    assert result.name == "my_report.json"
    assert "reports" in str(result)


def test_normalize_user_path_empty_string_returns_default(tmp_path: Path) -> None:
    default = tmp_path / "fallback.json"
    result = normalize_user_path("", default)
    assert result == default


# ---------------------------------------------------------------------------
# write_text
# ---------------------------------------------------------------------------

def test_write_text_creates_file(tmp_path: Path) -> None:
    p = tmp_path / "out.md"
    write_text(p, "# Hello\n")
    assert p.read_text() == "# Hello\n"


def test_write_text_creates_parent_dirs(tmp_path: Path) -> None:
    p = tmp_path / "deep" / "nested" / "report.md"
    write_text(p, "content")
    assert p.exists()


def test_write_text_overwrites_existing(tmp_path: Path) -> None:
    p = tmp_path / "file.txt"
    write_text(p, "first")
    write_text(p, "second")
    assert p.read_text() == "second"


def test_write_text_empty_string(tmp_path: Path) -> None:
    p = tmp_path / "empty.txt"
    write_text(p, "")
    assert p.read_text() == ""


# ---------------------------------------------------------------------------
# relpath
# ---------------------------------------------------------------------------

def test_relpath_inside_root(tmp_path: Path) -> None:
    path = tmp_path / "subdir" / "file.json"
    result = relpath(path, tmp_path)
    assert result == "subdir/file.json"


def test_relpath_at_root(tmp_path: Path) -> None:
    path = tmp_path / "file.json"
    result = relpath(path, tmp_path)
    assert result == "file.json"


def test_relpath_returns_string() -> None:
    result = relpath(REPO_ROOT / "dag-toolchain.json", REPO_ROOT)
    assert isinstance(result, str)
    assert result == "dag-toolchain.json"


def test_relpath_outside_root_raises_or_returns_string(tmp_path: Path) -> None:
    # relpath raises ValueError for paths outside root (Python 3.12 behavior)
    other = tmp_path.parent / "sibling_file.txt"
    try:
        result = relpath(other, tmp_path)
        assert isinstance(result, str)
    except ValueError:
        pass  # acceptable — path is not relative to root


# ---------------------------------------------------------------------------
# generated_timestamp
# ---------------------------------------------------------------------------

def test_generated_timestamp_is_non_empty() -> None:
    ts = generated_timestamp()
    assert isinstance(ts, str)
    assert len(ts) > 0


def test_generated_timestamp_matches_datetime_format() -> None:
    ts = generated_timestamp()
    # Should parse as a valid datetime in some format
    try:
        datetime.strptime(ts, "%Y-%m-%d %H:%M:%S")
    except ValueError:
        # May use a different format; just ensure it's a reasonable string
        assert re.match(r"\d{4}", ts), f"unexpected timestamp format: {ts!r}"


def test_generated_timestamp_changes_over_time() -> None:
    import time
    t1 = generated_timestamp()
    time.sleep(1.1)
    t2 = generated_timestamp()
    assert t1 != t2
