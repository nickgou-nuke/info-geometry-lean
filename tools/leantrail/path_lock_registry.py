#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from leantrail.backend.models import GraphSnapshot
from leantrail.backend.store import GraphStore
from tools.leantrail.adapters import import_arango_json, load_snapshot


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _snapshot_from_path(path: Path, fmt: str) -> GraphSnapshot:
    if fmt == "snapshot":
        return load_snapshot(path)
    if fmt == "arango-json":
        return import_arango_json(path)
    raise ValueError(f"Unsupported snapshot format: {fmt}")


def _path_id(
    src: str,
    dst: str,
    edges: list[dict[str, Any]],
    state: str,
) -> str:
    seed = json.dumps(
        {
            "src": src,
            "dst": dst,
            "state": state,
            "edges": [{"src": e.get("src"), "dst": e.get("dst"), "kind": e.get("kind")} for e in edges],
        },
        sort_keys=True,
        ensure_ascii=True,
    )
    digest = hashlib.sha1(seed.encode("utf-8")).hexdigest()
    return f"pl_{digest[:24]}"


def _load_registry(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            s = line.strip()
            if not s:
                continue
            try:
                row = json.loads(s)
            except Exception:
                continue
            if isinstance(row, dict):
                rows.append(row)
    return rows


def _row_fingerprint(row: dict[str, Any]) -> str:
    state = str(row.get("state", "")).strip()
    src = str(row.get("src", "")).strip()
    dst = str(row.get("dst", "")).strip()
    edges = row.get("edges")
    if not isinstance(edges, list):
        edges = []
    return _path_id(src, dst, edges, state)


def _write_registry(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")


def run_registry_update(
    *,
    snapshot: GraphSnapshot,
    registry_path: Path,
    src: str,
    dst: str,
    state: str,
    lawful_only: bool,
    state_policy: str,
    proof_ref: str,
    strict_sha: str,
    conformance_sha: str,
    path_id_override: str | None,
) -> dict[str, Any]:
    store = GraphStore(snapshot)
    path = store.shortest_path_with_state_policy(
        src=src,
        dst=dst,
        lawful_only=lawful_only,
        state_policy=state_policy,
    )
    if not path.get("found"):
        raise ValueError(
            f"No path found from {src} to {dst} (lawful_only={lawful_only}, state_policy={state_policy})."
        )

    node_src = store.node_by_id.get(src)
    node_dst = store.node_by_id.get(dst)
    src_endpoint = (
        str((node_src.attrs or {}).get("path_endpoint", "")).strip() if node_src and isinstance(node_src.attrs, dict) else ""
    ) or "unknown"
    dst_endpoint = (
        str((node_dst.attrs or {}).get("path_endpoint", "")).strip() if node_dst and isinstance(node_dst.attrs, dict) else ""
    ) or "unknown"

    edges = path.get("edges", [])
    if not isinstance(edges, list):
        edges = []

    row: dict[str, Any] = {
        "path_id": path_id_override or _path_id(src, dst, edges, state),
        "created_at": _utc_now(),
        "state": state,
        "bind_state": "closed" if state == "locked" else "open",
        "src": src,
        "dst": dst,
        "src_endpoint": src_endpoint,
        "dst_endpoint": dst_endpoint,
        "lawful_only": lawful_only,
        "state_policy": state_policy,
        "proof_ref": proof_ref,
        "strict_sha": strict_sha,
        "conformance_sha": conformance_sha,
        "node_path": path.get("path", []),
        "edges": [
            {"src": e.get("src", ""), "dst": e.get("dst", ""), "kind": e.get("kind", "")}
            for e in edges
            if isinstance(e, dict)
        ],
    }

    rows = _load_registry(registry_path)
    fp = _row_fingerprint(row)
    existing_fps = {_row_fingerprint(r) for r in rows}
    if fp not in existing_fps:
        rows.append(row)
    _write_registry(registry_path, rows)

    return {
        "created_at": _utc_now(),
        "registry_path": str(registry_path),
        "path_id": row["path_id"],
        "state": state,
        "added": fp not in existing_fps,
        "edge_count": len(row["edges"]),
        "src_endpoint": src_endpoint,
        "dst_endpoint": dst_endpoint,
        "rows_total": len(rows),
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Bind/lock path records for LeanTrail edge-state traversal policies."
    )
    parser.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.json")
    parser.add_argument(
        "--snapshot-format",
        choices=["snapshot", "arango-json"],
        default="snapshot",
    )
    parser.add_argument("--src", required=True)
    parser.add_argument("--dst", required=True)
    parser.add_argument("--state", choices=["bound", "locked"], default="locked")
    parser.add_argument("--lawful-only", action="store_true")
    parser.add_argument(
        "--state-policy",
        choices=["any", "exclude-failed", "locked-only"],
        default="exclude-failed",
        help="Traversal filter used when constructing the path record.",
    )
    parser.add_argument("--proof-ref", default="")
    parser.add_argument("--strict-sha", default="")
    parser.add_argument("--conformance-sha", default="")
    parser.add_argument("--path-id", default=None)
    parser.add_argument(
        "--registry-out",
        default="artifacts/leantrail/path_locks.jsonl",
        help="Registry JSONL where path records are stored.",
    )
    parser.add_argument(
        "--json-out",
        default="artifacts/leantrail/path_lock_report.json",
        help="Write compact operation report JSON here.",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    snapshot = _snapshot_from_path(Path(args.snapshot).resolve(), str(args.snapshot_format))
    report = run_registry_update(
        snapshot=snapshot,
        registry_path=Path(args.registry_out).resolve(),
        src=str(args.src),
        dst=str(args.dst),
        state=str(args.state),
        lawful_only=bool(args.lawful_only),
        state_policy=str(args.state_policy),
        proof_ref=str(args.proof_ref),
        strict_sha=str(args.strict_sha),
        conformance_sha=str(args.conformance_sha),
        path_id_override=(str(args.path_id).strip() or None) if args.path_id is not None else None,
    )

    json_out = Path(args.json_out).resolve()
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(
        "Path registry updated:",
        report["registry_path"],
        f"(path_id={report['path_id']}, state={report['state']}, added={report['added']})",
    )
    print(f"Report written: {json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
