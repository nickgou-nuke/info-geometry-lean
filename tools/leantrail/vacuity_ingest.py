#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
import sys
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from leantrail.backend.models import GraphSnapshot
from tools.leantrail.adapters import load_snapshot, save_snapshot


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return f"sha256:{h.hexdigest()}"


def _iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for line_no, raw in enumerate(handle, start=1):
            s = raw.strip()
            if not s:
                continue
            try:
                obj = json.loads(s)
            except Exception as exc:
                raise ValueError(f"Invalid JSONL at {path}:{line_no}: {exc}") from exc
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def _deep_merge(dst: dict[str, Any], src: dict[str, Any]) -> dict[str, Any]:
    out = dict(dst)
    for key, value in src.items():
        if isinstance(value, dict) and isinstance(out.get(key), dict):
            out[key] = _deep_merge(out[key], value)
        else:
            out[key] = value
    return out


def _target_name(row: dict[str, Any]) -> str:
    for key in ("target", "name", "decl", "declName"):
        value = str(row.get(key, "")).strip()
        if value:
            return value
    return ""


def ingest_vacuity(snapshot_path: Path, audit_path: Path, out_path: Path) -> dict[str, Any]:
    snapshot: GraphSnapshot = load_snapshot(snapshot_path)
    audit_rows = _iter_jsonl(audit_path)
    audit_by_target = {_target_name(row): row for row in audit_rows if _target_name(row)}

    touched = 0
    missing: list[str] = []
    for node in snapshot.nodes:
        row = audit_by_target.get(node.id) or audit_by_target.get(node.name)
        if row is None:
            continue
        attrs = node.attrs if isinstance(node.attrs, dict) else {}
        incoming_attrs = row.get("attrs", {}) if isinstance(row.get("attrs", {}), dict) else {}
        attrs = _deep_merge(attrs, incoming_attrs)
        attrs.setdefault("vacuity_ingest", {})
        attrs["vacuity_ingest"] = _deep_merge(
            attrs["vacuity_ingest"],
            {
                "audit_row_present": True,
                "certificate_ref": row.get("certificate_ref", ""),
                "audit_hash": row.get("audit_hash", ""),
            },
        )
        node.attrs = attrs
        touched += 1

    node_ids = {n.id for n in snapshot.nodes} | {n.name for n in snapshot.nodes}
    for target in sorted(audit_by_target):
        if target not in node_ids:
            missing.append(target)

    meta = dict(snapshot.metadata)
    leantrail_meta = dict(meta.get("leantrail", {})) if isinstance(meta.get("leantrail"), dict) else {}
    leantrail_meta["vacuity_ingest"] = {
        "source_snapshot": str(snapshot_path),
        "source_audit": str(audit_path),
        "source_audit_hash": _sha256_file(audit_path) if audit_path.exists() else "",
        "rows": len(audit_rows),
        "merged_nodes": touched,
        "missing_targets": len(missing),
    }
    meta["leantrail"] = leantrail_meta
    snapshot.metadata = meta

    save_snapshot(snapshot, out_path)
    return {
        "ok": True,
        "snapshot": str(snapshot_path),
        "audit": str(audit_path),
        "out": str(out_path),
        "rows": len(audit_rows),
        "merged_nodes": touched,
        "missing_targets": missing[:200],
        "missing_target_count": len(missing),
    }


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Merge Lean vacuity biopsy rows into a LeanTrail snapshot attrs payload.")
    p.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.json")
    p.add_argument("--audit", default="artifacts/leantrail/vacuity_audit.jsonl")
    p.add_argument("--out", default="artifacts/leantrail/graph_snapshot.vacuity.json")
    p.add_argument("--json-out", default="artifacts/leantrail/vacuity_ingest_report.json")
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    report = ingest_vacuity(Path(args.snapshot).resolve(), Path(args.audit).resolve(), Path(args.out).resolve())
    report_path = Path(args.json_out).resolve()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(f"Vacuity ingest merged {report['merged_nodes']} node(s); output: {report['out']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
