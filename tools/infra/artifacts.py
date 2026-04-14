#!/usr/bin/env python3
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


EXPECTED_INDEXER_SCHEMA_VERSION = 3


def normalize_repo_output(root: Path, raw: str | Path) -> Path:
    path = raw if isinstance(raw, Path) else Path(raw)
    if path.is_absolute():
        return path
    return (root / path).resolve()


def load_json_dict(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    return raw if isinstance(raw, dict) else {}


def load_decl_index_meta(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    try:
        return load_json_dict(path)
    except Exception:
        return None


def meta_matches_decl_refresh(
    meta: dict[str, Any] | None,
    *,
    current_hash: str,
    current_source_hash: str = "",
    import_root: str,
    namespace: str,
    schema_version: int = EXPECTED_INDEXER_SCHEMA_VERSION,
) -> bool:
    if not current_hash or not meta:
        return False
    if current_source_hash and meta.get("sourceHash") != current_source_hash:
        return False
    return (
        meta.get("oleanHash") == current_hash
        and meta.get("importRoot") == import_root
        and meta.get("nsFilter") == namespace
        and meta.get("schemaVersion") == schema_version
    )


def should_skip_decl_refresh(
    meta_path: Path,
    *,
    current_hash: str,
    current_source_hash: str = "",
    import_root: str,
    namespace: str,
    schema_version: int = EXPECTED_INDEXER_SCHEMA_VERSION,
) -> bool:
    return meta_matches_decl_refresh(
        load_decl_index_meta(meta_path),
        current_hash=current_hash,
        current_source_hash=current_source_hash,
        import_root=import_root,
        namespace=namespace,
        schema_version=schema_version,
    )


def stamp_decl_index_meta(
    meta_path: Path,
    *,
    olean_hash: str = "",
    source_hash: str = "",
    timestamp: datetime | None = None,
) -> dict[str, Any] | None:
    meta = load_decl_index_meta(meta_path)
    if meta is None:
        return None
    meta["timestamp"] = (timestamp or datetime.now(timezone.utc)).isoformat()
    if olean_hash:
        meta["oleanHash"] = olean_hash
    if source_hash:
        meta["sourceHash"] = source_hash
    meta_path.write_text(json.dumps(meta, indent=2) + "\n", encoding="utf-8")
    return meta


def find_missing_decl_source_files(index_dir: Path, *, limit: int = 8) -> list[str]:
    """
    Return up to `limit` source-file paths referenced by decls.jsonl that do not exist.

    This detects stale declaration exports after source renames/deletes when an
    incremental skip would otherwise leave old rows in place.
    """
    decls_path = index_dir / "decls.jsonl"
    if not decls_path.exists():
        return []

    missing: list[str] = []
    seen: set[str] = set()
    with decls_path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            if len(missing) >= limit:
                break
            raw = raw.strip()
            if not raw:
                continue
            try:
                row = json.loads(raw)
            except json.JSONDecodeError:
                continue
            if not isinstance(row, dict):
                continue
            file_raw = row.get("file")
            if not isinstance(file_raw, str) or not file_raw:
                continue
            if file_raw in seen:
                continue
            seen.add(file_raw)
            if not Path(file_raw).exists():
                missing.append(file_raw)
    return missing
