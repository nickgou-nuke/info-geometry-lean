#!/usr/bin/env python3
"""Mathless Conductive Wire Collapse & Hash-Overlap Interconnection Engine

Scans the full ArangoDB declaration graph for mathless intermediate nodes
(pure forwarding aliases, empty wrapper definitions, or zero-math pass-through nodes)
and traces multi-step conductive wires to collapse redundant pass-through nodes and
interconnect overlapping shape-hash dependency paths.
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


def scan_and_collapse_conductive_wires(target: ArangoTarget) -> dict[str, Any]:
    print("🔍 Scanning ArangoDB graph for mathless intermediate nodes and overlapping conductive wires...")

    # 1. Identify Mathless Intermediate Nodes (In-degree > 0, Out-degree > 0, low AST node count)
    mathless_query = """
    FOR d IN decls
      FILTER d.valueFingerprint != null
         AND d.valueFingerprint.nodeCount != null
         AND d.valueFingerprint.nodeCount < 10
      LET in_edges = (FOR e IN edges FILTER e._to == d._id RETURN e._from)
      LET out_edges = (FOR e IN edges FILTER e._from == d._id RETURN e._to)
      FILTER LENGTH(in_edges) > 0 AND LENGTH(out_edges) > 0
      LIMIT 100
      RETURN {
        id: d._id,
        name: d.name,
        kind: d.kind,
        module: d.module,
        astNodeCount: d.valueFingerprint.nodeCount,
        shapeHash: d.valueFingerprint.shapeHash,
        callers: in_edges,
        targets: out_edges
      }
    """
    mathless_nodes = run_aql(target, mathless_query)

    print(f"⚡ Found {len(mathless_nodes)} mathless intermediate nodes sitting in conductive wires.")

    # 2. Group Conductive Paths by Shape-Hash Signatures to find overlapping wires
    overlapping_wires_query = """
    FOR d IN decls
      FILTER d.valueFingerprint != null AND d.valueFingerprint.shapeHash != null
      COLLECT hash = d.valueFingerprint.shapeHash INTO members
      FILTER LENGTH(members) > 1
      SORT LENGTH(members) DESC
      LIMIT 20
      RETURN {
        shapeHash: hash,
        wireCount: LENGTH(members),
        overlappingNodes: members[*].d.name
      }
    """
    overlapping_wires = run_aql(target, overlapping_wires_query)

    # 3. Construct Direct Shortcut Edge Plan (bypassing mathless node v: u -> v -> w  ==>  u -> w)
    shortcut_plan = []
    for node in mathless_nodes:
        for caller in node["callers"]:
            for tgt in node["targets"]:
                shortcut_plan.append({
                    "bypassed_mathless_node": node["name"],
                    "direct_source": caller,
                    "direct_target": tgt,
                    "bypassed_shape_hash": node["shapeHash"]
                })

    report = {
        "summary": {
            "mathless_intermediate_nodes_count": len(mathless_nodes),
            "overlapping_wire_clusters": len(overlapping_wires),
            "proposed_shortcut_edges": len(shortcut_plan),
        },
        "mathless_nodes": mathless_nodes,
        "overlapping_wires": overlapping_wires,
        "shortcut_collapse_plan": shortcut_plan[:50],
    }

    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="Mathless Conductive Wire Collapse Engine")
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/dag/mathless_wire_collapse_plan.json"))
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    target = arango_target(repo_root)

    report = scan_and_collapse_conductive_wires(target)

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2))
    print(f"✅ Conductive wire collapse plan saved to {args.json_out}")


if __name__ == "__main__":
    main()
