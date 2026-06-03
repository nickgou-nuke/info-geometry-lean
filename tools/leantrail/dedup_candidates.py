from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from leantrail.backend.models import GraphSnapshot
from leantrail.backend.store import GraphStore


def _render_text(payload: dict) -> str:
    lines: list[str] = []
    summary = payload.get("summary", {}) if isinstance(payload, dict) else {}
    lines.append(f"status={payload.get('status', 'active')}")
    lines.append(
        "summary: active={active} suppressed={suppressed} none={none}".format(
            active=summary.get("active", 0),
            suppressed=summary.get("suppressed", 0),
            none=summary.get("none", 0),
        )
    )
    lines.append("")
    for idx, row in enumerate(payload.get("results", []), start=1):
        node = row.get("node", {}) if isinstance(row, dict) else {}
        dedup = row.get("structural_dedup", {}) if isinstance(row, dict) else {}
        lines.append(f"[{idx}] {node.get('name', '')}")
        lines.append(f"  module: {node.get('module', '')}")
        lines.append(f"  dedup_status: {row.get('dedup_status', '')}")
        lines.append(f"  relation_subtype: {dedup.get('relation_subtype', '')}")
        lines.append(f"  recommended_action: {dedup.get('recommended_action', '')}")
        lines.append(f"  family_id: {dedup.get('family_id', '')}")
        lines.append(f"  member_count: {dedup.get('member_count', '')}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Inspect LeanTrail structural dedup candidates from a snapshot.")
    parser.add_argument("--repo-root", default=".", help="Repository root used for relative paths.")
    parser.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.json", help="Snapshot JSON path.")
    parser.add_argument("--status", default="active", choices=["active", "suppressed", "all", "none"], help="Dedup status filter.")
    parser.add_argument("--limit", type=int, default=50, help="Maximum rows to return.")
    parser.add_argument("--format", default="json", choices=["json", "text"], help="Output format.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path(args.repo_root).resolve()
    snapshot_path = (repo_root / args.snapshot).resolve() if not Path(args.snapshot).is_absolute() else Path(args.snapshot)
    payload = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot = GraphSnapshot.from_dict(payload)
    store = GraphStore(snapshot)
    result = store.dedup_candidates(status=args.status, limit=args.limit)
    if args.format == "text":
        sys.stdout.write(_render_text(result))
    else:
        sys.stdout.write(json.dumps(result, indent=2, ensure_ascii=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
