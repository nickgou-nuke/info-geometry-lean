"""Tests for tools/infra/artifacts.py — JSON loading, meta matching, and index helpers."""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path

import pytest

from tools.infra.artifacts import (
    EXPECTED_INDEXER_SCHEMA_VERSION,
    find_missing_decl_source_files,
    load_decl_index_meta,
    load_json_dict,
    meta_matches_decl_refresh,
    normalize_repo_output,
    should_skip_decl_refresh,
    stamp_decl_index_meta,
)


# ---------------------------------------------------------------------------
# normalize_repo_output
# ---------------------------------------------------------------------------

def test_normalize_repo_output_absolute_path_unchanged(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    abs_path = tmp_path / "somewhere" / "file.json"
    result = normalize_repo_output(root, abs_path)
    assert result == abs_path


def test_normalize_repo_output_relative_resolves_under_root(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    result = normalize_repo_output(root, "artifacts/dag/graph.json")
    assert result == (root / "artifacts/dag/graph.json").resolve()


def test_normalize_repo_output_str_input(tmp_path: Path) -> None:
    result = normalize_repo_output(tmp_path, "out.json")
    assert result == (tmp_path / "out.json").resolve()


# ---------------------------------------------------------------------------
# load_json_dict
# ---------------------------------------------------------------------------

def test_load_json_dict_returns_dict(tmp_path: Path) -> None:
    p = tmp_path / "data.json"
    p.write_text(json.dumps({"key": "val", "num": 42}), encoding="utf-8")
    result = load_json_dict(p)
    assert result == {"key": "val", "num": 42}


def test_load_json_dict_array_returns_empty(tmp_path: Path) -> None:
    p = tmp_path / "list.json"
    p.write_text(json.dumps([1, 2, 3]), encoding="utf-8")
    result = load_json_dict(p)
    assert result == {}


def test_load_json_dict_empty_object(tmp_path: Path) -> None:
    p = tmp_path / "empty.json"
    p.write_text("{}", encoding="utf-8")
    assert load_json_dict(p) == {}


# ---------------------------------------------------------------------------
# load_decl_index_meta
# ---------------------------------------------------------------------------

def test_load_decl_index_meta_returns_none_when_missing(tmp_path: Path) -> None:
    result = load_decl_index_meta(tmp_path / "no_such_meta.json")
    assert result is None


def test_load_decl_index_meta_returns_dict(tmp_path: Path) -> None:
    meta = {"oleanHash": "abc123", "importRoot": "InfoGeometry.All"}
    p = tmp_path / "meta.json"
    p.write_text(json.dumps(meta), encoding="utf-8")
    result = load_decl_index_meta(p)
    assert result == meta


def test_load_decl_index_meta_returns_none_on_corrupt(tmp_path: Path) -> None:
    p = tmp_path / "bad.json"
    p.write_text("not json{{", encoding="utf-8")
    result = load_decl_index_meta(p)
    assert result is None


# ---------------------------------------------------------------------------
# meta_matches_decl_refresh
# ---------------------------------------------------------------------------

def _good_meta(
    *,
    olean_hash: str = "hash_abc",
    source_hash: str = "",
    import_root: str = "InfoGeometry.All",
    namespace: str = "InfoGeometry",
    schema_version: int = EXPECTED_INDEXER_SCHEMA_VERSION,
) -> dict:
    meta: dict = {
        "oleanHash": olean_hash,
        "importRoot": import_root,
        "nsFilter": namespace,
        "schemaVersion": schema_version,
    }
    if source_hash:
        meta["sourceHash"] = source_hash
    return meta


def test_meta_matches_exact_match() -> None:
    meta = _good_meta()
    assert meta_matches_decl_refresh(
        meta,
        current_hash="hash_abc",
        import_root="InfoGeometry.All",
        namespace="InfoGeometry",
    )


def test_meta_matches_false_when_hash_differs() -> None:
    meta = _good_meta()
    assert not meta_matches_decl_refresh(
        meta,
        current_hash="different_hash",
        import_root="InfoGeometry.All",
        namespace="InfoGeometry",
    )


def test_meta_matches_false_when_import_root_differs() -> None:
    meta = _good_meta()
    assert not meta_matches_decl_refresh(
        meta,
        current_hash="hash_abc",
        import_root="OtherRoot",
        namespace="InfoGeometry",
    )


def test_meta_matches_false_when_namespace_differs() -> None:
    meta = _good_meta()
    assert not meta_matches_decl_refresh(
        meta,
        current_hash="hash_abc",
        import_root="InfoGeometry.All",
        namespace="OtherNS",
    )


def test_meta_matches_false_when_schema_version_differs() -> None:
    meta = _good_meta(schema_version=99)
    assert not meta_matches_decl_refresh(
        meta,
        current_hash="hash_abc",
        import_root="InfoGeometry.All",
        namespace="InfoGeometry",
    )


def test_meta_matches_false_when_source_hash_differs() -> None:
    meta = _good_meta(source_hash="src_abc")
    assert not meta_matches_decl_refresh(
        meta,
        current_hash="hash_abc",
        current_source_hash="src_different",
        import_root="InfoGeometry.All",
        namespace="InfoGeometry",
    )


def test_meta_matches_true_when_source_hash_matches() -> None:
    meta = _good_meta(source_hash="src_abc")
    assert meta_matches_decl_refresh(
        meta,
        current_hash="hash_abc",
        current_source_hash="src_abc",
        import_root="InfoGeometry.All",
        namespace="InfoGeometry",
    )


def test_meta_matches_false_on_none_meta() -> None:
    assert not meta_matches_decl_refresh(
        None,
        current_hash="hash_abc",
        import_root="InfoGeometry.All",
        namespace="InfoGeometry",
    )


def test_meta_matches_false_on_empty_hash() -> None:
    meta = _good_meta()
    assert not meta_matches_decl_refresh(
        meta,
        current_hash="",
        import_root="InfoGeometry.All",
        namespace="InfoGeometry",
    )


# ---------------------------------------------------------------------------
# should_skip_decl_refresh
# ---------------------------------------------------------------------------

def test_should_skip_returns_true_when_meta_matches(tmp_path: Path) -> None:
    meta_path = tmp_path / "meta.json"
    meta_path.write_text(
        json.dumps(_good_meta()),
        encoding="utf-8",
    )
    assert should_skip_decl_refresh(
        meta_path,
        current_hash="hash_abc",
        import_root="InfoGeometry.All",
        namespace="InfoGeometry",
    )


def test_should_skip_returns_false_when_meta_missing(tmp_path: Path) -> None:
    assert not should_skip_decl_refresh(
        tmp_path / "no_meta.json",
        current_hash="hash_abc",
        import_root="InfoGeometry.All",
        namespace="InfoGeometry",
    )


def test_should_skip_returns_false_when_hash_changes(tmp_path: Path) -> None:
    meta_path = tmp_path / "meta.json"
    meta_path.write_text(json.dumps(_good_meta()), encoding="utf-8")
    assert not should_skip_decl_refresh(
        meta_path,
        current_hash="new_hash",
        import_root="InfoGeometry.All",
        namespace="InfoGeometry",
    )


# ---------------------------------------------------------------------------
# stamp_decl_index_meta
# ---------------------------------------------------------------------------

def test_stamp_writes_meta_json(tmp_path: Path) -> None:
    index_dir = tmp_path / "index"
    index_dir.mkdir()
    meta_path = index_dir / "meta.json"
    # stamp requires the meta file to exist first
    meta_path.write_text(
        json.dumps({"schemaVersion": EXPECTED_INDEXER_SCHEMA_VERSION,
                    "importRoot": "InfoGeometry.All",
                    "nsFilter": "InfoGeometry",
                    "oleanHash": ""}),
        encoding="utf-8",
    )
    stamp_decl_index_meta(meta_path, olean_hash="stamped_hash")
    data = json.loads(meta_path.read_text())
    assert data["oleanHash"] == "stamped_hash"
    assert "timestamp" in data


def test_stamp_creates_no_file_when_meta_missing(tmp_path: Path) -> None:
    # stamp_decl_index_meta returns None if meta_path doesn't exist
    meta_path = tmp_path / "does" / "not" / "exist" / "meta.json"
    result = stamp_decl_index_meta(meta_path, olean_hash="h")
    assert result is None


# ---------------------------------------------------------------------------
# find_missing_decl_source_files
# ---------------------------------------------------------------------------

def test_find_missing_decl_source_files_empty_index(tmp_path: Path) -> None:
    # No decls.jsonl at all → empty result
    index_dir = tmp_path / "index"
    index_dir.mkdir()
    result = find_missing_decl_source_files(index_dir)
    assert result == []


def test_find_missing_decl_source_files_all_present(tmp_path: Path) -> None:
    index_dir = tmp_path / "index"
    index_dir.mkdir()
    lean_file = tmp_path / "lean" / "Foo.lean"
    lean_file.parent.mkdir(parents=True)
    lean_file.write_text("-- ok", encoding="utf-8")
    # decls.jsonl: one JSON row per declaration
    (index_dir / "decls.jsonl").write_text(
        json.dumps({"name": "Foo.bar", "file": str(lean_file), "line": 1}) + "\n",
        encoding="utf-8",
    )
    result = find_missing_decl_source_files(index_dir)
    assert result == []


def test_find_missing_decl_source_files_missing_file(tmp_path: Path) -> None:
    index_dir = tmp_path / "index"
    index_dir.mkdir()
    missing_file = str(tmp_path / "lean" / "Missing.lean")
    (index_dir / "decls.jsonl").write_text(
        json.dumps({"name": "Bar.baz", "file": missing_file, "line": 1}) + "\n",
        encoding="utf-8",
    )
    result = find_missing_decl_source_files(index_dir)
    assert len(result) >= 1
    assert missing_file in result
