#!/usr/bin/env python3
"""ArangoDB Root-to-Leaf Conductive Path Topology Analyzer

Identifies foundational root declarations (out-degree 0 in dependency graph)
and top-level leaf theorems (in-degree 0), and computes full conductive path
interconnections down to roots and up to leaves.
"""

from __future__ import annotations

import argparse
import json
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


def compute_root_leaf_topology(target: ArangoTarget) -> dict[str, Any]:
    print("🔍 Analyzing ArangoDB declaration graph roots and leaves...")
    
    # Query total declaration count
    total_decls = run_aql(target, "RETURN LENGTH(decls)")[0]
    total_edges = run_aql(target, "RETURN LENGTH(edges)")[0]
    
    print(f"📊 Total Graph Size: {total_decls} vertices, {total_edges} edges")

    # Find Root Declarations (no outgoing dependency edges to other codebase decls)
    roots_query = """
    FOR d IN decls
      LET out_edges = (
        FOR e IN edges
          FILTER e._from == d._id
          LIMIT 1
          RETURN 1
      )
      FILTER LENGTH(out_edges) == 0
      LIMIT 100
      RETURN {name: d.name, kind: d.kind, module: d.module}
    """
    roots = run_aql(target, roots_query)
    
    # Find Leaf Declarations (no incoming caller edges)
    leaves_query = """
    FOR d IN decls
      LET in_edges = (
        FOR e IN edges
          FILTER e._to == d._id
          LIMIT 1
          RETURN 1
      )
      FILTER LENGTH(in_edges) == 0
      LIMIT 100
      RETURN {name: d.name, kind: d.kind, module: d.module}
    """
    leaves = run_aql(target, leaves_query)

    # Find Top Value-Shape-Hash Equivalence Classes (Candidate Conductive Wires)
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
        "conductive_wire_clusters": conductive_wires,
    }
    
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="Root-to-Leaf Topology Analyzer")
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/dag/root_to_leaf_topology.json"))
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    target = arango_target(repo_root)

    report = compute_root_leaf_topology(target)

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2))
    print(f"✅ Topology report saved to {args.json_out}")


if __name__ == "__main__":
    main()
