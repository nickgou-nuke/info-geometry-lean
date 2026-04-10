#!/usr/bin/env python3
from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


INDEXER_TIMING_SCHEMA_VERSION = 1
REPORT_TIMING_SCHEMA_VERSION = 1

INDEXER_TIMING_LOG_NAME = "indexer-timing.log"
INDEXER_TIMING_JSON_NAME = "indexer-timing.json"
REPORT_TIMING_JSON_NAME = "report-timing.json"

_INDEXER_TIMING_LINE_RE = re.compile(r"^\[Indexer timing\] (?P<label>.+): (?P<elapsed_ms>\d+) ms$")


def indexer_timing_log_path(index_dir: Path) -> Path:
    return index_dir / INDEXER_TIMING_LOG_NAME


def indexer_timing_json_path(index_dir: Path) -> Path:
    return index_dir / INDEXER_TIMING_JSON_NAME


def report_timing_json_path(root: Path) -> Path:
    return root / "artifacts" / "dag" / REPORT_TIMING_JSON_NAME


def parse_indexer_timing_log(log_path: Path) -> dict[str, Any] | None:
    if not log_path.exists():
        return None
    import_modules_ms: int | None = None
    total_ms: int | None = None
    stages: list[dict[str, Any]] = []
    for raw_line in log_path.read_text(encoding="utf-8").splitlines():
        match = _INDEXER_TIMING_LINE_RE.match(raw_line.strip())
        if not match:
            continue
        label = match.group("label")
        elapsed_ms = int(match.group("elapsed_ms"))
        if label.startswith("importModules"):
            import_modules_ms = elapsed_ms
            continue
        if label == "total runIndexer":
            total_ms = elapsed_ms
            continue
        stages.append({"label": label, "elapsed_ms": elapsed_ms})
    if import_modules_ms is None and total_ms is None and not stages:
        return None
    return {
        "import_modules_ms": import_modules_ms,
        "stages": stages,
        "total_ms": total_ms,
    }


def build_indexer_timing_payload(
    *,
    log_path: Path,
    meta: dict[str, Any] | None,
) -> dict[str, Any] | None:
    parsed = parse_indexer_timing_log(log_path)
    if parsed is None:
        return None
    meta = meta or {}
    return {
        "schemaVersion": INDEXER_TIMING_SCHEMA_VERSION,
        "artifactTimestamp": meta.get("timestamp", ""),
        "oleanHash": meta.get("oleanHash", ""),
        "artifactSchemaVersion": meta.get("schemaVersion"),
        "recordedAt": datetime.now(timezone.utc).isoformat(),
        "sourceLog": log_path.name,
        "importModules_ms": parsed.get("import_modules_ms"),
        "stageCount": len(parsed.get("stages", [])),
        "stages": parsed.get("stages", []),
        "total_ms": parsed.get("total_ms"),
    }


def write_indexer_timing_sidecar(index_dir: Path, meta: dict[str, Any] | None) -> Path | None:
    log_path = indexer_timing_log_path(index_dir)
    payload = build_indexer_timing_payload(log_path=log_path, meta=meta)
    if payload is None:
        return None
    out_path = indexer_timing_json_path(index_dir)
    out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return out_path


def load_indexer_timing(index_dir: Path) -> dict[str, Any] | None:
    json_path = indexer_timing_json_path(index_dir)
    if json_path.exists():
        try:
            raw = json.loads(json_path.read_text(encoding="utf-8"))
        except Exception:
            raw = None
        if isinstance(raw, dict):
            return raw
    return build_indexer_timing_payload(log_path=indexer_timing_log_path(index_dir), meta={})


def write_report_timing_sidecar(
    path: Path,
    *,
    config_path: Path,
    meta: dict[str, Any] | None,
    steps: list[dict[str, Any]],
    total_ms: int,
    status: str,
) -> Path:
    meta = meta or {}
    payload = {
        "schemaVersion": REPORT_TIMING_SCHEMA_VERSION,
        "artifactTimestamp": meta.get("timestamp", ""),
        "oleanHash": meta.get("oleanHash", ""),
        "artifactSchemaVersion": meta.get("schemaVersion"),
        "recordedAt": datetime.now(timezone.utc).isoformat(),
        "configPath": str(config_path),
        "stepCount": len(steps),
        "steps": steps,
        "total_ms": total_ms,
        "status": status,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return path


def load_report_timing(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None
    return raw if isinstance(raw, dict) else None


def format_elapsed_ms(raw_ms: Any) -> str:
    if not isinstance(raw_ms, int):
        return "-"
    if raw_ms >= 60_000:
        minutes, ms = divmod(raw_ms, 60_000)
        seconds = ms / 1000
        return f"{minutes}m {seconds:.1f}s"
    if raw_ms >= 1000:
        return f"{raw_ms / 1000:.1f}s"
    return f"{raw_ms}ms"


def top_timing_rows(payload: dict[str, Any] | None, limit: int = 3) -> list[dict[str, Any]]:
    if not isinstance(payload, dict):
        return []
    raw_rows = payload.get("stages")
    if not isinstance(raw_rows, list):
        raw_rows = payload.get("steps")
    if not isinstance(raw_rows, list):
        return []
    rows = [row for row in raw_rows if isinstance(row, dict) and isinstance(row.get("elapsed_ms"), int)]
    return sorted(rows, key=lambda row: row["elapsed_ms"], reverse=True)[:limit]


def timing_matches_meta(payload: dict[str, Any] | None, meta: dict[str, Any] | None) -> bool | None:
    if not isinstance(payload, dict) or not isinstance(meta, dict) or not meta:
        return None
    payload_timestamp = payload.get("artifactTimestamp")
    meta_timestamp = meta.get("timestamp")
    payload_hash = payload.get("oleanHash")
    meta_hash = meta.get("oleanHash")
    if not payload_timestamp or not meta_timestamp or not payload_hash or not meta_hash:
        return None
    return payload_timestamp == meta_timestamp and payload_hash == meta_hash
