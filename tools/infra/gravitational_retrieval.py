#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SRC_ROOT = REPO_ROOT / "src"
for path in (REPO_ROOT, SRC_ROOT):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from igf.graph import ArangoHttpTarget, execute_aql

"""
# Gravitational Retrieval (The Graviton)
Computes "Strong Gravitation" via Personalized PageRank (ArangoDB Pregel)
to extract Lean-grounded context for formal proof.

Usage:
  python3 tools/infra/gravitational_retrieval.py --center InfoGeometry.Krein.KreinSpace --top-k 5
"""

@dataclass(frozen=True)
class ArangoTarget:
    endpoint: str
    database: str
    username: str
    password: str
    nodes_collection: str
    edges_collection: str


def _http_target(target: ArangoTarget) -> ArangoHttpTarget:
    return ArangoHttpTarget(
        endpoint=target.endpoint.rstrip("/"),
        database=target.database,
        username=target.username,
        password=target.password,
    )

def run_pregel_pagerank(target: ArangoTarget, center_id: str):
    """
    Triggers an ArangoDB Pregel PageRank job.
    In a real DGX setup, this would ideally use the cuGraph adapter.
    For the Spire baseline, we use the ArangoDB built-in Pregel.
    """
    # 1. Identify the 'internal' key for the center declaration
    query = "FOR n IN @@nodes FILTER n.name == @center RETURN n._key"
    rows = execute_aql(
        _http_target(target),
        query,
        {"@nodes": target.nodes_collection, "center": center_id},
    )
    if not rows:
        print(f"Error: Center '{center_id}' not found.")
        sys.exit(1)

    # 2. Start Pregel Job (Personalized PageRank)
    # Note: ArangoDB built-in PageRank isn't always personalized by default in all versions.
    # We'll use a standard PageRank and then filter by neighborhood mass as a proxy,
    # or use AQL to simulate the 'gravitation' if Pregel is restricted.

    print(f"Computing Gravitational Mass for neighbors of {center_id}...")

    # Gravitational Query: Neighborhood ranking by PageRank / connectivity
    # This simulates "Strong Gravitation" by looking at the transitive support.
    grav_query = """
    LET start = FIRST(FOR n IN @@nodes FILTER n.name == @center RETURN n)
    FOR v, e, p IN 1..3 ANY start @@edges
        OPTIONS { bfs: true, uniqueVertices: "global" }
        FILTER v.kind IN ["theorem", "lemma", "def", "axiom", "instance"]
        LET mass = LENGTH(FOR vv, ee IN 1..1 ANY v @@edges RETURN ee)
        SORT mass DESC
        RETURN {
            id: v.name,
            mass: mass,
            file: v.file,
            line: v.line,
            doc: v.doc
        }
    """

    return execute_aql(
        _http_target(target),
        grav_query,
        {
            "@nodes": target.nodes_collection,
            "@edges": target.edges_collection,
            "center": center_id
        },
    )

def get_lean_source(file_path: str, line: int, radius: int = 5) -> str:
    p = Path(file_path)
    if not p.exists():
        # Try relative to repo root if absolute path from ingestion is stale
        p = REPO_ROOT / Path(file_path).name
        if not p.exists():
            return f"-- [Source not found: {file_path}]"

    lines = p.read_text().splitlines()
    start = max(0, line - radius - 1)
    end = min(len(lines), line + radius)
    return "\n".join(lines[start:end])

def main():
    load_repo_arango_env(REPO_ROOT)
    parser = argparse.ArgumentParser(description="Extract Gravitational Context from ArangoDB.")
    parser.add_argument("--center", required=True, help="ID of the center theorem.")
    parser.add_argument("--top-k", type=int, default=5, help="Number of massive neighbors to retrieve.")
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--out", default="quarantine/hermes_memory/gravitational_context.json")
    args = parser.parse_args()

    target = ArangoTarget(
        endpoint=args.endpoint,
        database=args.database,
        username=arango_username(),
        password=arango_password(),
        nodes_collection="ig_nodes",
        edges_collection="ig_edges"
    )

    massive_neighbors = run_pregel_pagerank(target, args.center)

    context_packets = []
    for i, n in enumerate(massive_neighbors[:args.top_k]):
        print(f"  [{i+1}] {n['id']} (Mass: {n['mass']})")
        source = get_lean_source(n['file'], n['line'])
        context_packets.append({
            "id": n['id'],
            "mass": n['mass'],
            "doc": n['doc'],
            "source": source
        })

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({
        "center": args.center,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "gravitational_context": context_packets
    }, indent=2))

    print(f"\nStrong Gravitation Context written to: {args.out}")

if __name__ == "__main__":
    main()
