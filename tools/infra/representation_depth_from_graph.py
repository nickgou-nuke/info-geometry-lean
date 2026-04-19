#!/usr/bin/env python3
"""Derive representation-depth rows from materialized graph artifacts.

This is the fast query/report path for the L0-L5 layer contract. Lean remains
the source of the `@[rep_depth ...]` tags and raw dependency export; this tool
derives direct/closure depth summaries from the already materialized graph rows
that are also ingested into ArangoDB.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from pathlib import Path
from typing import Any


DEPTH_SLUGS = {
    0: "count",
    1: "projective",
    2: "operator",
    3: "krein",
    4: "transport",
    5: "thermo",
}


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if line:
                row = json.loads(line)
                if not isinstance(row, dict):
                    raise ValueError(f"{path}: expected JSON object rows")
                rows.append(row)
    return rows


def as_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        try:
            return int(value)
        except ValueError:
            return None
    return None


def node_name(row: dict[str, Any]) -> str:
    return str(row.get("name") or row.get("raw_name") or "")


def node_depth_nat(row: dict[str, Any]) -> int | None:
    attrs = row.get("attrs") if isinstance(row.get("attrs"), dict) else {}
    return as_int(row.get("rep_depth_nat")) or as_int(row.get("rep_depth")) or as_int(attrs.get("rep_depth_nat"))


def node_depth_slug(row: dict[str, Any], depth_nat: int) -> str:
    attrs = row.get("attrs") if isinstance(row.get("attrs"), dict) else {}
    return str(row.get("rep_depth_slug") or attrs.get("rep_depth_slug") or DEPTH_SLUGS.get(depth_nat, f"L{depth_nat}"))


def node_is_capstone(row: dict[str, Any]) -> bool:
    attrs = row.get("attrs") if isinstance(row.get("attrs"), dict) else {}
    labels = row.get("labels") if isinstance(row.get("labels"), list) else []
    decl = row.get("decl") if isinstance(row.get("decl"), dict) else {}
    attr_values = []
    raw_attrs = decl.get("attrs")
    if isinstance(raw_attrs, list):
        attr_values.extend(str(item) for item in raw_attrs)
    attr_values.extend(str(item) for item in labels)
    attr_values.extend(str(item) for item in attrs.values())
    return any(item == "capstone" or item.endswith(":capstone") or "capstone" == item.rsplit(":", 1)[-1] for item in attr_values)


def edge_src_dst(edge: dict[str, Any], key_to_name: dict[str, str]) -> tuple[str, str] | None:
    src = str(edge.get("src") or "")
    dst = str(edge.get("dst") or "")
    if src and dst:
        return src, dst
    raw_from = str(edge.get("_from") or "")
    raw_to = str(edge.get("_to") or "")
    if "/" in raw_from and "/" in raw_to:
        src_key = raw_from.split("/", 1)[1]
        dst_key = raw_to.split("/", 1)[1]
        src = key_to_name.get(src_key, "")
        dst = key_to_name.get(dst_key, "")
        if src and dst:
            return src, dst
    return None


def sorted_unique(values: list[Any]) -> list[Any]:
    return sorted(set(values), key=lambda item: str(item))


def lower_depths(target_depth_nat: int, depths: list[int]) -> list[int]:
    return sorted(d for d in set(depths) if d < target_depth_nat)


def nearest_lower_depth(target_depth_nat: int, depths: list[int]) -> int | None:
    lowers = lower_depths(target_depth_nat, depths)
    return lowers[-1] if lowers else None


def shallowest_lower_depth(target_depth_nat: int, depths: list[int]) -> int | None:
    lowers = lower_depths(target_depth_nat, depths)
    return lowers[0] if lowers else None


def reaches_prev(target_depth_nat: int, depths: list[int]) -> bool:
    return target_depth_nat > 0 and (target_depth_nat - 1) in set(depths)


def reaches_below_prev(target_depth_nat: int, depths: list[int]) -> bool:
    return any(d + 1 < target_depth_nat for d in depths)


def reaches_above(target_depth_nat: int, depths: list[int]) -> bool:
    return any(target_depth_nat < d for d in depths)


def judgment_label(capstone: bool, target_depth_nat: int, direct_depths: list[int]) -> str:
    if reaches_above(target_depth_nat, direct_depths):
        return "regression"
    if capstone:
        return "capstone_coherence"
    nearest = nearest_lower_depth(target_depth_nat, direct_depths)
    if nearest is None:
        return "vertical"
    if reaches_below_prev(target_depth_nat, direct_depths):
        return "wormhole"
    if nearest + 1 == target_depth_nat:
        return "primitive_translator"
    return "wormhole"


def closure_from(adjacency: dict[str, list[str]], root: str) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    queue: deque[str] = deque(adjacency.get(root, []))
    while queue:
        current = queue.popleft()
        if current == root or current in seen:
            continue
        seen.add(current)
        out.append(current)
        queue.extend(adjacency.get(current, []))
    return sorted_unique(out)


def build_report(nodes: list[dict[str, Any]], edges: list[dict[str, Any]]) -> dict[str, Any]:
    key_to_name = {str(row.get("_key")): node_name(row) for row in nodes if row.get("_key") and node_name(row)}
    by_name = {node_name(row): row for row in nodes if node_name(row)}

    tagged_depth: dict[str, int] = {}
    tagged_slug: dict[str, str] = {}
    for name, row in by_name.items():
        depth_nat = node_depth_nat(row)
        if depth_nat is None:
            continue
        tagged_depth[name] = depth_nat
        tagged_slug[name] = node_depth_slug(row, depth_nat)

    adjacency: dict[str, list[str]] = {}
    for edge in edges:
        pair = edge_src_dst(edge, key_to_name)
        if pair is None:
            continue
        src, dst = pair
        adjacency.setdefault(src, []).append(dst)
    adjacency = {src: sorted_unique(dsts) for src, dsts in adjacency.items()}

    declarations: list[dict[str, Any]] = []
    for name in sorted(tagged_depth):
        row = by_name[name]
        target_depth = tagged_depth[name]
        direct_tagged = [dst for dst in adjacency.get(name, []) if dst in tagged_depth]
        closure_tagged = [dst for dst in closure_from(adjacency, name) if dst in tagged_depth]
        direct_depths = sorted_unique([tagged_depth[dst] for dst in direct_tagged])
        closure_depths = sorted_unique([tagged_depth[dst] for dst in closure_tagged])
        nearest_direct = nearest_lower_depth(target_depth, direct_depths)
        nearest_closure = nearest_lower_depth(target_depth, closure_depths)
        shallowest_direct = shallowest_lower_depth(target_depth, direct_depths)
        shallowest_closure = shallowest_lower_depth(target_depth, closure_depths)
        capstone = node_is_capstone(row)
        declarations.append(
            {
                "name": name,
                "module": str(row.get("module") or ""),
                "kind": str(row.get("kind") or ""),
                "depth": tagged_slug[name],
                "depthNat": target_depth,
                "sourceDepthNat": min(direct_depths + [target_depth]),
                "effectiveSourceDepthNat": nearest_direct if nearest_direct is not None else target_depth,
                "targetDepthNat": target_depth,
                "directTaggedDepCount": len(direct_tagged),
                "closureTaggedDepCount": len(closure_tagged),
                "directTaggedDeps": sorted_unique(direct_tagged),
                "closureTaggedDeps": sorted_unique(closure_tagged),
                "directDepDepthNats": direct_depths,
                "closureDepDepthNats": closure_depths,
                "minDirectDepth": min(direct_depths) if direct_depths else None,
                "maxDirectDepth": max(direct_depths) if direct_depths else None,
                "minClosureDepth": min(closure_depths) if closure_depths else None,
                "maxClosureDepth": max(closure_depths) if closure_depths else None,
                "nearestLowerDirectDepth": nearest_direct,
                "shallowestLowerDirectDepth": shallowest_direct,
                "nearestLowerClosureDepth": nearest_closure,
                "shallowestLowerClosureDepth": shallowest_closure,
                "reachesPrevDirect": reaches_prev(target_depth, direct_depths),
                "reachesBelowPrevDirect": reaches_below_prev(target_depth, direct_depths),
                "reachesAboveDirect": reaches_above(target_depth, direct_depths),
                "reachesPrevClosure": reaches_prev(target_depth, closure_depths),
                "reachesBelowPrevClosure": reaches_below_prev(target_depth, closure_depths),
                "reachesAboveClosure": reaches_above(target_depth, closure_depths),
                "judgment": judgment_label(capstone, target_depth, direct_depths),
                "capstone": capstone,
            }
        )

    return {
        "schema": "info_geometry.representation_depth_from_graph.v1",
        "count": len(declarations),
        "declarations": declarations,
    }


def report_from_dir(input_dir: Path) -> dict[str, Any]:
    nodes_path = input_dir / "ig_nodes.jsonl"
    edges_path = input_dir / "ig_edges.jsonl"
    if not nodes_path.exists() or not edges_path.exists():
        raise FileNotFoundError(f"expected {nodes_path} and {edges_path}")
    return build_report(read_jsonl(nodes_path), read_jsonl(edges_path))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--json-out", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = report_from_dir(args.input_dir.resolve())
    text = json.dumps(payload, indent=2, ensure_ascii=True, sort_keys=True) + "\n"
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
