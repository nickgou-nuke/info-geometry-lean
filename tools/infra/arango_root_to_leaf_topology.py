#!/usr/bin/env python3
"""ArangoDB Root-to-Leaf Conductive Path Topology & Interconnection Engine

Identifies foundational root declarations (out-degree 0 in dependency graph)
and top-level leaf theorems (in-degree 0), and computes full conductive path
interconnections down to roots and up to leaves across the compiled codebase.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from igf.graph.decl_schema import (
    STRUCTURAL_FINGERPRINT_VERSION,
    TERM_DIGEST_VERSION,
)
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


def check_and_refresh_stale_arango(target: ArangoTarget, repo_root: Path) -> tuple[str, str]:
    """Select the current content-addressed generation, creating it if absent."""
    print("🔄 Resolving the current immutable Arango declaration generation...")
    cmd = [
        sys.executable,
        str(repo_root / "tools/infra/refresh_decl_graph.py"),
        "--stream",
        "--run-mode", "exe",
        "--import-root", "InfoGeometry.All",
        "--namespace", "InfoGeometry",
        "--arango-db", arango_database(),
    ]
    proc = subprocess.run(cmd, cwd=repo_root, text=True, capture_output=True)
    if proc.stdout:
        print(proc.stdout, end="")
    if proc.stderr:
        print(proc.stderr, file=sys.stderr, end="")
    match = re.search(r"immutable generation: ([A-Za-z0-9_-]+)", proc.stdout)
    if proc.returncode not in (0, 2) or match is None:
        raise RuntimeError("immutable declaration graph stream failed or did not report its generation ID")
    generation_id = match.group(1)
    receipts = run_aql(
        target,
        "FOR g IN decl_graph_generations FILTER g._key == @id && g.status == 'complete' RETURN g",
        {"id": generation_id},
    )
    if not receipts:
        raise RuntimeError(f"declaration graph generation {generation_id} has no complete receipt")
    receipt = receipts[0]
    if receipt.get("importRoot") != "InfoGeometry.All" or receipt.get("namespace") != "InfoGeometry":
        raise RuntimeError(f"declaration graph generation {generation_id} has an unexpected import scope")
    if receipt.get("declarationCount", 0) <= 0 or receipt.get("validEdgeCount") != receipt.get("emittedEdgeCount"):
        raise RuntimeError(f"declaration graph generation {generation_id} failed count validation")
    decl_collection = receipt.get("declCollection")
    edge_collection = receipt.get("edgeCollection")
    if not decl_collection or not edge_collection:
        raise RuntimeError(f"declaration graph generation {generation_id} has incomplete collection metadata")
    print(f"✅ Using completed declaration graph generation {generation_id}.")
    return decl_collection, edge_collection


def duplicate_candidate_query() -> str:
    """Group only matching type/value pairs within one fingerprint version.

    These remain source-review candidates, not equivalence classes. In
    particular, open-term digests cannot establish a closed declaration match.
    """
    return f"""
    FOR d IN @@decls
      LET hasDigests = d.typeDigest.algorithmVersion == "{TERM_DIGEST_VERSION}"
          AND d.valueDigest.algorithmVersion == "{TERM_DIGEST_VERSION}"
      LET closedDigests = hasDigests AND d.typeDigest.openTerm == false
          AND d.valueDigest.openTerm == false
      LET legacyPair = !hasDigests
          AND d.typeFingerprint.algorithmVersion == "{STRUCTURAL_FINGERPRINT_VERSION}"
          AND d.valueFingerprint.algorithmVersion == "{STRUCTURAL_FINGERPRINT_VERSION}"
      FILTER closedDigests OR legacyPair
      LET version = closedDigests ? "{TERM_DIGEST_VERSION}" : "{STRUCTURAL_FINGERPRINT_VERSION}"
      LET typeHash = closedDigests ? d.typeDigest.digest : d.canonicalTypeHash
      LET valueHash = closedDigests ? d.valueDigest.digest : d.canonicalValueHash
      FILTER typeHash != null AND valueHash != null
      COLLECT algorithmVersion = version, typeFingerprint = typeHash,
              valueFingerprint = valueHash INTO members
      FILTER LENGTH(members) > 1
      SORT LENGTH(members) DESC, algorithmVersion, typeFingerprint, valueFingerprint
      LIMIT 20
      RETURN {{
        algorithmVersion, typeFingerprint, valueFingerprint,
        count: LENGTH(members),
        declarations: SORTED(members[*].d.name)
      }}
    """


def compute_root_leaf_topology(
    target: ArangoTarget,
    sample_limit: int = 100,
    decl_collection: str = "decls",
    edge_collection: str = "edges",
) -> dict[str, Any]:
    print("🔍 Analyzing ArangoDB declaration graph roots and leaves...")

    collection_bindings = {"@decls": decl_collection, "@edges": edge_collection}
    total_decls = run_aql(target, "RETURN LENGTH(@@decls)", {"@decls": decl_collection})[0]
    total_edges = run_aql(target, "RETURN LENGTH(@@edges)", {"@edges": edge_collection})[0]

    print(f"📊 Total Graph Size: {total_decls} vertices, {total_edges} edges")

    # Find Root Declarations (out-degree 0 in dependency graph: base definitions & primitives)
    roots_query = """
    FOR d IN @@decls
      LET out_edges = (
        FOR e IN @@edges
          FILTER e._from == d._id
          LIMIT 1
          RETURN 1
      )
      FILTER LENGTH(out_edges) == 0
      LIMIT @limit
      RETURN {name: d.name, kind: d.kind, module: d.module, id: d._id}
    """
    roots = run_aql(target, roots_query, {**collection_bindings, "limit": sample_limit})
    
    # Find Leaf Declarations (in-degree 0 in dependency graph: top-level capstone theorems)
    leaves_query = """
    FOR d IN @@decls
      LET in_edges = (
        FOR e IN @@edges
          FILTER e._to == d._id
          LIMIT 1
          RETURN 1
      )
      FILTER LENGTH(in_edges) == 0
      LIMIT @limit
      RETURN {name: d.name, kind: d.kind, module: d.module, id: d._id}
    """
    leaves = run_aql(target, leaves_query, {**collection_bindings, "limit": sample_limit})

    # Interconnect: Trace conductive paths from sample leaves down to foundational roots
    print("⚡ Tracing conductive paths down to roots and up to leaves...")
    leaf_root_paths = []
    if leaves:
        sample_leaf = leaves[0]
        path_query = """
        FOR v, e, p IN 1..4 OUTBOUND @start_id @@edges
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
            "@edges": edge_collection,
        })

    conductive_wires = run_aql(target, duplicate_candidate_query(), {"@decls": decl_collection})

    report = {
        "summary": {
            "total_declarations": total_decls,
            "total_edges": total_edges,
            "declaration_collection": decl_collection,
            "edge_collection": edge_collection,
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

    decl_collection, edge_collection = check_and_refresh_stale_arango(target, repo_root)

    report = compute_root_leaf_topology(
        target,
        sample_limit=args.sample_limit,
        decl_collection=decl_collection,
        edge_collection=edge_collection,
    )

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2))
    print(f"✅ Interconnection topology report saved to {args.json_out}")


if __name__ == "__main__":
    main()
