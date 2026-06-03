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


def _as_dict(value: object) -> dict[str, object]:
    return value if isinstance(value, dict) else {}


def _as_list(value: object) -> list[object]:
    return value if isinstance(value, list) else []


def render_text(payload: dict[str, object]) -> str:
    node = _as_dict(payload.get("node"))
    if not node:
        return ""
    attrs = _as_dict(node.get("attrs"))
    incoming = _as_list(payload.get("incoming"))
    outgoing = _as_list(payload.get("outgoing"))
    lines = [
        f"name={node.get('name', '')}",
        f"kind={node.get('kind', '')} module={node.get('module', '')} line={node.get('line', '')}",
        f"file={node.get('file', '')}",
        f"decl_kind={attrs.get('decl_kind', '')}",
        f"path_endpoint={attrs.get('path_endpoint', '')}",
        f"incoming_edges={len(incoming)} outgoing_edges={len(outgoing)}",
    ]
    if incoming:
        lines.append("incoming:")
        for idx, edge in enumerate(incoming[:10], start=1):
            if not isinstance(edge, dict):
                continue
            lines.append(f"[{idx}] {edge.get('src', '')} -[{edge.get('kind', '')}]-> {edge.get('dst', '')}")
    if outgoing:
        lines.append("outgoing:")
        for idx, edge in enumerate(outgoing[:10], start=1):
            if not isinstance(edge, dict):
                continue
            lines.append(f"[{idx}] {edge.get('src', '')} -[{edge.get('kind', '')}]-> {edge.get('dst', '')}")
    return "\n".join(lines).rstrip() + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Exact declaration lookup from an authoritative LeanTrail snapshot.")
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.json")
    parser.add_argument("--name", required=True)
    parser.add_argument("--format", default="json", choices=["json", "text"])
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path(args.repo_root).resolve()
    snapshot_path = (repo_root / args.snapshot).resolve() if not Path(args.snapshot).is_absolute() else Path(args.snapshot)
    payload = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot = GraphSnapshot.from_dict(payload)
    store = GraphStore(snapshot)
    result = store.get_decl(args.name)
    if result is None:
        raise SystemExit(f"declaration not found: {args.name}")
    if args.format == "text":
        sys.stdout.write(render_text(result))
    else:
        sys.stdout.write(json.dumps(result, indent=2, ensure_ascii=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
