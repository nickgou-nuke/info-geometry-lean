"""Tests for tools/infra/representation_depth_io.py — depth index I/O."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools.infra.representation_depth_io import (
    interval_label,
    load_depth_index,
    rel_repo_path,
)

REPO_ROOT = Path(__file__).resolve().parents[1]


# ---------------------------------------------------------------------------
# interval_label
# ---------------------------------------------------------------------------

def test_interval_label_from_dict() -> None:
    row = {"source_depth": 2, "target_depth": 5}
    assert interval_label(row) == "2\u21925"


def test_interval_label_from_ints() -> None:
    assert interval_label(0, 3) == "0\u21923"


def test_interval_label_same_depth() -> None:
    assert interval_label(4, 4) == "4\u21924"


def test_interval_label_large_values() -> None:
    assert interval_label(10, 100) == "10\u2192100"


def test_interval_label_float_in_dict_coerces_to_int() -> None:
    row = {"source_depth": 2.0, "target_depth": 5.0}
    assert interval_label(row) == "2\u21925"


# ---------------------------------------------------------------------------
# rel_repo_path
# ---------------------------------------------------------------------------

def test_rel_repo_path_absolute_inside_repo() -> None:
    path = REPO_ROOT / "tools" / "infra" / "artifacts.py"
    result = rel_repo_path(path, REPO_ROOT)
    assert result == "tools/infra/artifacts.py"


def test_rel_repo_path_relative_string() -> None:
    result = rel_repo_path("tools/infra/artifacts.py", REPO_ROOT)
    assert result == "tools/infra/artifacts.py"


def test_rel_repo_path_returns_string() -> None:
    result = rel_repo_path(REPO_ROOT / "dag-toolchain.json", REPO_ROOT)
    assert isinstance(result, str)
    assert result == "dag-toolchain.json"


def test_rel_repo_path_uses_repo_root_default() -> None:
    # Should not raise even without explicit root
    result = rel_repo_path("tools/infra/timings.py")
    assert isinstance(result, str)
    assert "timings.py" in result


# ---------------------------------------------------------------------------
# load_depth_index
# ---------------------------------------------------------------------------

def _write_depth_index(path: Path, *, files: list[dict] | None = None, extra: dict | None = None) -> None:
    payload: dict = {
        "schemaVersion": 1,
        "files": files or [],
    }
    if extra:
        payload.update(extra)
    path.write_text(json.dumps(payload), encoding="utf-8")


def test_load_depth_index_empty_files(tmp_path: Path) -> None:
    p = tmp_path / "depth.json"
    _write_depth_index(p, files=[])
    result, meta = load_depth_index(p)
    assert result == {}
    assert isinstance(meta, dict)


def test_load_depth_index_single_entry(tmp_path: Path) -> None:
    p = tmp_path / "depth.json"
    _write_depth_index(p, files=[{
        "file": "lean/InfoGeometry/Canonical/Drazin.lean",
        "kind": "owner",
        "source_depth": 2,
        "target_depth": 5,
        "notes": "",
    }])
    result, meta = load_depth_index(p)
    assert "lean/InfoGeometry/Canonical/Drazin.lean" in result
    entry = result["lean/InfoGeometry/Canonical/Drazin.lean"]
    assert entry["source_depth"] == 2
    assert entry["target_depth"] == 5
    assert entry["kind"] == "owner"


def test_load_depth_index_multiple_entries(tmp_path: Path) -> None:
    p = tmp_path / "depth.json"
    files = [
        {"file": f"lean/M{i}.lean", "kind": "tagged", "source_depth": i, "target_depth": i + 1, "notes": ""}
        for i in range(5)
    ]
    _write_depth_index(p, files=files)
    result, _ = load_depth_index(p)
    assert len(result) == 5


def test_load_depth_index_skips_invalid_rows(tmp_path: Path) -> None:
    p = tmp_path / "depth.json"
    payload = {
        "schemaVersion": 1,
        "files": [
            None,
            "not_a_dict",
            {"file": "", "source_depth": 1, "target_depth": 2},  # empty file path → skipped
            {"file": "lean/Valid.lean", "source_depth": 3, "target_depth": 4, "kind": "owner", "notes": ""},
        ],
    }
    p.write_text(json.dumps(payload), encoding="utf-8")
    result, _ = load_depth_index(p)
    # Only the valid entry with non-empty file should be present
    assert len(result) == 1
    assert "lean/Valid.lean" in result


def test_load_depth_index_returns_full_payload_as_meta(tmp_path: Path) -> None:
    p = tmp_path / "depth.json"
    _write_depth_index(p, files=[], extra={"generated_at": "2026-01-01"})
    _, meta = load_depth_index(p)
    assert meta.get("generated_at") == "2026-01-01"
    assert meta.get("schemaVersion") == 1
