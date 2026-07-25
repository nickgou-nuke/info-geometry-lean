#!/usr/bin/env python3
"""ArangoDB Root-to-Leaf Conductive Path Topology & Interconnection Engine

Identifies foundational root declarations (out-degree 0 in dependency graph)
and top-level leaf theorems (in-degree 0), and computes full conductive path
interconnections down to roots and up to leaves across the compiled codebase.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.infra.arango_dag_algorithms import run_aql
from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.arango_raw_infotree_ingest import ArangoTarget


def arango_target(repo_root: Path) -> ArangoTarget:
    load_repo_arango_env(repo_root)
    return ArangoTarget(
        endpoint=arango_endpoint().rstrip("/"),
        database=arango_database(),
        username=arango_username(),
        password=arango_password(),
    )


def check_and_refresh_stale_arango(target: ArangoTarget, repo_root: Path) -> None:
    """Checks if ArangoDB decls/edges are empty or stale and refreshes them if needed."""
    try:
        decl_count = run_aql(target, "RETURN LENGTH(decls)")[0]
    except Exception:
        decl_count = 0

    if decl_count < 1000:
        print("⚠️ ArangoDB graph is empty or stale. Running canonical streaming graph refresh...")
        cmd = [
            sys.executable,
            str(repo_root / "tools/infra/refresh_decl_graph.py"),
            "--stream",
            "--run-mode", "exe",
            "--skip-prebuild",
            "--import-root", "InfoGeometry.All",
            "--namespace", "InfoGeometry",
            "--arango-db", arango_database(),
        ]
        subprocess.run(cmd, cwd=repo_root, check=True)
        print("✅ Graph streaming refresh complete.")


def compute_root_leaf_topology(target: ArangoTarget, sample_limit: int = 100) -> dict[str, Any]:
    print("🔍 Analyzing ArangoDB declaration graph roots and leaves...")
    
    total_decls = run_aql(target, "RETURN LENGTH(decls)")[0]
    total_edges = run_aql(target, "RETURN LENGTH(edges)")[0]
    
    print(f"📊 Total Graph Size: {total_decls} vertices, {total_edges} edges")

    # Find Root Declarations (out-degree 0 in dependency graph: base definitions & primitives)
    roots_query = """
    FOR d IN decls
      LET out_edges = (
        FOR e IN edges
          FILTER e._from == d._id
          LIMIT 1
          RETURN 1
      )
      FILTER LENGTH(out_edges) == 0
      LIMIT @limit
      RETURN {name: d.name, kind: d.kind, module: d.module, id: d._id}
    """
    roots = run_aql(target, roots_query, {"limit": sample_limit})
    
    # Find Leaf Declarations (in-degree 0 in dependency graph: top-level capstone theorems)
    leaves_query = """
    FOR d IN decls
      LET in_edges = (
        FOR e IN edges
          FILTER e._to == d._id
          LIMIT 1
          RETURN 1
      )
      FILTER LENGTH(in_edges) == 0
      LIMIT @limit
      RETURN {name: d.name, kind: d.kind, module: d.module, id: d._id}
    """
    leaves = run_aql(target, leaves_query, {"limit": sample_limit})

    # Interconnect: Trace conductive paths from sample leaves down to foundational roots
    print("⚡ Tracing conductive paths down to roots and up to leaves...")
    leaf_root_paths = []
    if leaves:
        sample_leaf = leaves[0]
        path_query = """
        FOR v, e, p IN 1..4 OUTBOUND @start_id edges
          LIMIT 20
          RETURN {
            path_length: LENGTH(p.edges),
            nodes: p.vertices[*].name,
            leaf: @leaf_name
          }
        """
        leaf_root_paths = run_aql(target, path_query, {
            "start_id": sample_leaf["id"],
            "leaf_name": sample_leaf["name"],
        })

    # Find Top Value-Shape-Hash Equivalence Classes (Conductive Wires)
    wires_query = """
    FOR d IN decls
      FILTER d.valueFingerprint != null
      COLLECT hash = d.valueFingerprint.shapeHash INTO members
      FILTER hash != null AND LENGTH(members) > 1
      SORT LENGTH(members) DESC
      LIMIT 20
      RETURN {
        shapeHash: hash,
        count: LENGTH(members),
        declarations: members[*].d.name
      }
    """
    conductive_wires = run_aql(target, wires_query)

    report = {
        "summary": {
            "total_declarations": total_decls,
            "total_edges": total_edges,
            "sampled_roots_count": len(roots),
            "sampled_leaves_count": len(leaves),
            "conductive_wire_clusters": len(conductive_wires),
        },
        "sampled_roots": roots,
        "sampled_leaves": leaves,
        "interconnection_paths": leaf_root_paths,
        "conductive_wire_clusters": conductive_wires,
    }
    
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="Root-to-Leaf Interconnection Topology Engine")
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/dag/root_to_leaf_topology.json"))
    parser.add_argument("--sample-limit", type=int, default=100)
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    target = arango_target(repo_root)

    check_and_refresh_stale_arango(target, repo_root)

    report = compute_root_leaf_topology(target, sample_limit=args.sample_limit)

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2))
    print(f"✅ Interconnection topology report saved to {args.json_out}")


if __name__ == "__main__":
    main()
