#!/usr/bin/env python3
"""Report L0-L5 representation-layer counts and cross-layer raw edges."""

from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
from typing import Any


# [lossless-compact] read_jsonl folded into igf.common.json_io.read_jsonl
from igf.common.json_io import read_jsonl


def layer_of(row: dict[str, Any]) -> str | None:
    attrs = row.get("attrs") if isinstance(row.get("attrs"), dict) else {}
    layer = row.get("rep_layer") or attrs.get("rep_layer")
    return str(layer) if layer else None


def report(input_dir: Path) -> dict[str, Any]:
    nodes = read_jsonl(input_dir / "ig_nodes.jsonl")
    edges = read_jsonl(input_dir / "ig_edges.jsonl")
    by_key = {str(row.get("_key")): row for row in nodes}
    by_name = {str(row.get("name") or row.get("raw_name")): row for row in nodes}
    layer_counts: collections.Counter[str] = collections.Counter()
    cross_layer_edges: collections.Counter[str] = collections.Counter()

    for row in nodes:
        if layer := layer_of(row):
            layer_counts[layer] += 1

    for edge in edges:
        src_name = str(edge.get("src") or "")
        dst_name = str(edge.get("dst") or "")
        src_key = str(edge.get("_from") or "").split("/", 1)[-1]
        dst_key = str(edge.get("_to") or "").split("/", 1)[-1]
        src = by_name.get(src_name) or by_key.get(src_key)
        dst = by_name.get(dst_name) or by_key.get(dst_key)
        src_layer = layer_of(src or {})
        dst_layer = layer_of(dst or {})
        if src_layer and dst_layer:
            cross_layer_edges[f"{src_layer}->{dst_layer}"] += 1

    return {
        "schema": "info_geometry.rep_layer_report.v1",
        "input_dir": str(input_dir),
        "node_count": len(nodes),
        "edge_count": len(edges),
        "layer_counts": dict(sorted(layer_counts.items())),
        "cross_layer_edges": dict(sorted(cross_layer_edges.items())),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--json-out", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = report(args.input_dir.resolve())
    text = json.dumps(payload, indent=2, ensure_ascii=True) + "\n"
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
