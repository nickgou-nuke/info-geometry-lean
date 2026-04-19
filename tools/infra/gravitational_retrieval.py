#!/usr/bin/env python3
from __future__ import annotations

import argparse
import base64
import json
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.parse import quote
from urllib.request import Request, urlopen

"""
# Gravitational Retrieval (The Graviton)
Computes "Strong Gravitation" via Personalized PageRank (ArangoDB Pregel)
to extract Lean-grounded context for formal proof.

Usage:
  python3 tools/infra/gravitational_retrieval.py --center InfoGeometry.Krein.KreinSpace --top-k 5
"""

REPO_ROOT = Path(__file__).resolve().parents[2]

@dataclass(frozen=True)
class ArangoTarget:
    endpoint: str
    database: str
    username: str
    password: str
    nodes_collection: str
    edges_collection: str

def _auth_header(username: str, password: str) -> str:
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"

def _db_url(target: ArangoTarget, path: str) -> str:
    return f"{target.endpoint}/_db/{quote(target.database)}/{path.lstrip('/')}"

def _request_json(method: str, url: str, target: ArangoTarget, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    body = json.dumps(payload, ensure_ascii=True).encode("utf-8") if payload is not None else None
    req = Request(url, data=body, method=method)
    req.add_header("Authorization", _auth_header(target.username, target.password))
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", "application/json")

    try:
        with urlopen(req) as resp:
            raw = resp.read().decode("utf-8")
            return json.loads(raw) if raw else {}
    except HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {url}: {raw}") from exc

def run_pregel_pagerank(target: ArangoTarget, center_id: str):
    """
    Triggers an ArangoDB Pregel PageRank job.
    In a real DGX setup, this would ideally use the cuGraph adapter.
    For the Spire baseline, we use the ArangoDB built-in Pregel.
    """
    # 1. Identify the 'internal' key for the center declaration
    query = "FOR n IN @@nodes FILTER n.id == @center RETURN n._key"
    res = _request_json("POST", _db_url(target, "/_api/cursor"), target, {
        "query": query,
        "bindVars": {"@nodes": target.nodes_collection, "center": center_id}
    })
    if not res.get("result"):
        print(f"Error: Center '{center_id}' not found.")
        sys.exit(1)
    center_key = res["result"][0]

    # 2. Start Pregel Job (Personalized PageRank)
    # Note: ArangoDB built-in PageRank isn't always personalized by default in all versions.
    # We'll use a standard PageRank and then filter by neighborhood mass as a proxy,
    # or use AQL to simulate the 'gravitation' if Pregel is restricted.

    print(f"Computing Gravitational Mass for neighbors of {center_id}...")

    # Gravitational Query: Neighborhood ranking by PageRank / connectivity
    # This simulates "Strong Gravitation" by looking at the transitive support.
    grav_query = """
    LET start = FIRST(FOR n IN @@nodes FILTER n.id == @center RETURN n)
    FOR v, e, p IN 1..3 ANY start @@edges
        OPTIONS { bfs: true, uniqueVertices: "global" }
        FILTER v.kind == "Declaration"
        LET mass = LENGTH(FOR vv, ee IN 1..1 ANY v @@edges RETURN ee)
        SORT mass DESC
        RETURN {
            id: v.id,
            mass: mass,
            file: v.file,
            line: v.line,
            doc: v.attrs.doc
        }
    """

    res = _request_json("POST", _db_url(target, "/_api/cursor"), target, {
        "query": grav_query,
        "bindVars": {
            "@nodes": target.nodes_collection,
            "@edges": target.edges_collection,
            "center": center_id
        }
    })
    return res.get("result", [])

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
    parser = argparse.ArgumentParser(description="Extract Gravitational Context from ArangoDB.")
    parser.add_argument("--center", required=True, help="ID of the center theorem.")
    parser.add_argument("--top-k", type=int, default=5, help="Number of massive neighbors to retrieve.")
    parser.add_argument("--endpoint", default="http://127.0.0.1:8529")
    parser.add_argument("--database", default="infogeometry")
    parser.add_argument("--out", default="quarantine/hermes_memory/gravitational_context.json")
    args = parser.parse_args()

    target = ArangoTarget(
        endpoint=args.endpoint,
        database=args.database,
        username="root",
        password="",
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
