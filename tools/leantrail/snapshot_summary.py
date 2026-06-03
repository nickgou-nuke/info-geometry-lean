from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from leantrail.backend.models import GraphSnapshot


def _sorted_counter(counter: Counter[str]) -> dict[str, int]:
    return {key: counter[key] for key in sorted(counter)}


def _as_dict(value: object) -> dict[str, object]:
    return value if isinstance(value, dict) else {}


def build_summary(snapshot: GraphSnapshot) -> dict[str, object]:
    node_kind_counts: Counter[str] = Counter(node.kind for node in snapshot.nodes)
    edge_kind_counts: Counter[str] = Counter(edge.kind for edge in snapshot.edges)
    module_counts: Counter[str] = Counter(node.module for node in snapshot.nodes if node.module)
    metadata = _as_dict(snapshot.metadata)
    counts = _as_dict(metadata.get("counts"))
    dag_meta = _as_dict(metadata.get("dag_meta"))
    return {
        "metadata": {
            "created_at": metadata.get("created_at"),
            "source": metadata.get("source"),
            "commit_sha": metadata.get("commit_sha"),
            "toolchain": metadata.get("toolchain"),
            "artifact_version": metadata.get("artifact_version"),
            "dag_meta": dag_meta,
        },
        "counts": {
            "nodes": len(snapshot.nodes),
            "edges": len(snapshot.edges),
            "metadata_nodes": counts.get("nodes"),
            "metadata_edges": counts.get("edges"),
            "depth_rows": counts.get("depth_rows"),
            "path_endpoints": counts.get("path_endpoints"),
            "failed_transition_edges": counts.get("failed_transition_edges"),
            "locked_edges": counts.get("locked_edges"),
            "duplicate_edges_removed": counts.get("duplicate_edges_removed"),
        },
        "node_kind_counts": _sorted_counter(node_kind_counts),
        "edge_kind_counts": _sorted_counter(edge_kind_counts),
        "top_modules": [
            {"module": module, "count": count}
            for module, count in module_counts.most_common(10)
        ],
    }


def _fmt_counts(mapping: object) -> str:
    data = mapping if isinstance(mapping, dict) else {}
    if not data:
        return ""
    return ", ".join(f"{key}={value}" for key, value in data.items())


def render_text(summary: dict[str, object]) -> str:
    metadata = _as_dict(summary.get("metadata"))
    counts = _as_dict(summary.get("counts"))
    node_kind_counts = _as_dict(summary.get("node_kind_counts"))
    edge_kind_counts = _as_dict(summary.get("edge_kind_counts"))
    top_modules_obj = summary.get("top_modules")
    top_modules = top_modules_obj if isinstance(top_modules_obj, list) else []
    lines = [
        f"commit_sha={metadata.get('commit_sha', '')}",
        f"toolchain={metadata.get('toolchain', '')}",
        f"artifact_version={metadata.get('artifact_version', '')}",
        f"nodes={counts.get('nodes', 0)} edges={counts.get('edges', 0)}",
    ]
    if counts.get("path_endpoints"):
        lines.append(f"path_endpoints: {_fmt_counts(counts.get('path_endpoints'))}")
    lines.append(f"node_kinds: {_fmt_counts(node_kind_counts)}")
    lines.append(f"edge_kinds: {_fmt_counts(edge_kind_counts)}")
    if top_modules:
        lines.append("")
        lines.append("top_modules:")
        for idx, row in enumerate(top_modules, start=1):
            if not isinstance(row, dict):
                continue
            lines.append(f"[{idx}] {row.get('module', '')} count={row.get('count', 0)}")
    return "\n".join(lines).rstrip() + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Summarize an authoritative LeanTrail compiler-produced snapshot.")
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.json")
    parser.add_argument("--format", default="json", choices=["json", "text"])
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path(args.repo_root).resolve()
    snapshot_path = (repo_root / args.snapshot).resolve() if not Path(args.snapshot).is_absolute() else Path(args.snapshot)
    payload = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot = GraphSnapshot.from_dict(payload)
    summary = build_summary(snapshot)
    if args.format == "text":
        sys.stdout.write(render_text(summary))
    else:
        sys.stdout.write(json.dumps(summary, indent=2, ensure_ascii=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
