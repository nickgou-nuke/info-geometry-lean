#!/usr/bin/env python3
"""Audit how faithful the current Arango graph is to local graph artifacts.

The existing `ig_nodes`/`ig_edges` collections are a retrieval projection. This
tool makes that explicit by reporting local snapshot counts, known edge leakage,
available expression-graph artifacts, and optional live Arango collection counts.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

from tools.infra.arango_env import (
    DEFAULT_ARANGO_DATABASE,
    DEFAULT_ARANGO_ENDPOINT,
    arango_database,
    arango_endpoint,
    load_repo_arango_env,
)

DEFAULT_ARANGO = DEFAULT_ARANGO_ENDPOINT
DEFAULT_DB = DEFAULT_ARANGO_DATABASE


def count_jsonl(path: Path) -> int | None:
    if not path.exists():
        return None
    count = 0
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                count += 1
    return count


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def arango_collection_count(base_url: str, db: str, collection: str) -> int | None:
    url = f"{base_url.rstrip('/')}/_db/{db}/_api/collection/{collection}/count"
    request = urllib.request.Request(url, method="GET", headers={"Accept": "application/json"})
    
    username = os.environ.get("ARANGO_USER") or os.environ.get("ARANGO_USERNAME")
    password = os.environ.get("ARANGO_PASS") or os.environ.get("ARANGO_PASSWORD")
    if username and password is not None:
        token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
        request.add_header("Authorization", f"Basic {token}")

    try:
        with urllib.request.urlopen(request, timeout=5) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, OSError, json.JSONDecodeError):
        return None
    count = payload.get("count")
    return count if isinstance(count, int) else None


def build_report(args: argparse.Namespace) -> dict[str, Any]:
    repo = args.repo_root.resolve()
    leantrail_nodes = repo / "artifacts/leantrail/arango/ig_nodes.jsonl"
    leantrail_edges = repo / "artifacts/leantrail/arango/ig_edges.jsonl"
    dag_decls = repo / "artifacts/dag/index/decls.jsonl"
    dag_edges = repo / "artifacts/dag/index/edges.jsonl"
    edge_leakage_path = repo / "artifacts/dag/index/edge-leakage.json"
    expr_smoke_nodes = repo / "artifacts/expr-graph/arango-infogeometry-smoke/ig_nodes.jsonl"
    expr_smoke_edges = repo / "artifacts/expr-graph/arango-infogeometry-smoke/ig_edges.jsonl"

    leakage = load_json(edge_leakage_path) or {}
    local_counts = {
        "leantrail_arango_nodes": count_jsonl(leantrail_nodes),
        "leantrail_arango_edges": count_jsonl(leantrail_edges),
        "dag_decl_index_rows": count_jsonl(dag_decls),
        "dag_decl_edge_rows": count_jsonl(dag_edges),
        "expr_graph_smoke_nodes": count_jsonl(expr_smoke_nodes),
        "expr_graph_smoke_edges": count_jsonl(expr_smoke_edges),
    }
    live_counts = {
        "ig_nodes": arango_collection_count(args.arango_url, args.arango_db, args.nodes_collection),
        "ig_edges": arango_collection_count(args.arango_url, args.arango_db, args.edges_collection),
    }

    lossy_boundaries = [
        "Indexer filters generated/unstable names before the DAG index is exported.",
        "Indexer drops edges whose endpoints are outside the filtered node set; see edge-leakage.json.",
        "Block export separates primary and auxiliary declarations.",
        "LeanTrail Arango JSONL stores snapshot graph nodes/edges, not every raw expression node.",
        "Current gravity retrieval defaults to declarations with source excerpts.",
        "Expression graph artifacts currently appear as smoke exports, not the canonical Arango graph.",
    ]

    return {
        "schema": "info_geometry.arango_fidelity_audit.v1",
        "repo_root": str(repo),
        "arango": {
            "url": args.arango_url,
            "database": args.arango_db,
            "nodes_collection": args.nodes_collection,
            "edges_collection": args.edges_collection,
            "live_counts": live_counts,
        },
        "local_counts": local_counts,
        "edge_leakage": {
            "path": str(edge_leakage_path),
            "total_edges": leakage.get("totalEdges"),
            "kept_edges": leakage.get("keptEdges"),
            "dropped_edges": leakage.get("droppedEdges"),
            "src_outside_filtered_set": leakage.get("srcOutsideFilteredSet"),
            "dst_outside_module_edges": leakage.get("dstOutsideModuleEdges"),
            "dst_inside_module_generated_edges": leakage.get("dstInsideModuleGeneratedEdges"),
            "dst_inside_module_stable_edges": leakage.get("dstInsideModuleStableEdges"),
            "dst_unknown_edges": leakage.get("dstUnknownEdges"),
        },
        "lossy_boundaries": lossy_boundaries,
        "faithful_graph_target": {
            "raw_layer_policy": "LOSSLESS",
            "base_layer": "raw_infotree_*",
            "keep_projection": ["ig_nodes", "ig_edges"],
            "add_raw_collections": [
                "raw_infotree_roots",
                "raw_infotree_nodes",
                "raw_infotree_edges",
                "raw_infotree_contexts",
                "raw_infotree_payloads",
                "raw_decl_nodes",
                "raw_expr_nodes",
                "raw_expr_edges",
                "raw_decl_expr_edges",
                "raw_info_edges",
                "raw_edge_leakage",
            ],
            "rule": "The raw InfoTree layer must be preserved losslessly first; hydration, aliases, and retrieval projections are overlays. Never use absence from ig_edges as proof of absence from the Lean info tree.",
        },
    }


def parse_args() -> argparse.Namespace:
    load_repo_arango_env(Path.cwd())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--arango-url", default=arango_endpoint(DEFAULT_ARANGO))
    parser.add_argument("--arango-db", default=arango_database(DEFAULT_DB))
    parser.add_argument("--nodes-collection", default="ig_nodes")
    parser.add_argument("--edges-collection", default="ig_edges")
    parser.add_argument("--json-out", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    report = build_report(args)
    text = json.dumps(report, indent=2, ensure_ascii=False)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n", encoding="utf-8")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
