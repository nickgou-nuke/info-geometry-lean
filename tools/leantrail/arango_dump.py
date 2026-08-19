#!/usr/bin/env python3
"""
ArangoDB DAG graph dump -> JSON for visualisation and structural queries.

Connects to the leantrail ArangoDB instance, reads the declaration graph
collections, and exports a ForceGraph-compatible node-link JSON.

Supports AQL-powered causal cone extraction: given a seed node, follows
dependency edges to compute its downstream/upstream cone.

Usage:
  # Full graph dump
  python3 tools/leantrail/arango_dump.py                       \
    --endpoint http://localhost:8530                            \
    --database LeanAST                                          \
    --collection Theorems                                       \
    --edges ProofSteps                                          \
    --out artifacts/leantrail/dag_graph.json

  # Causal cone extraction
  python3 tools/leantrail/arango_dump.py                       \
    --cone-downstream "DAG.LaplacianRank::laplacian_rank_eq_add_rank" \
    --max-depth 5                                                \
    --out artifacts/leantrail/causal_cone.json
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Dict, List, Optional, Set

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

try:
    from arango import ArangoClient
    from arango.exceptions import ArangoError
except ImportError:
    ArangoClient = None  # type: ignore[assignment]
    ArangoError = RuntimeError  # type: ignore[assignment]


# ---------------------------------------------------------------------------
# ArangoDB helpers
# ---------------------------------------------------------------------------


def _read_arango_env_file() -> Dict[str, str]:
    """Read `/home/goutev/.config/arango/env.sh` style `export K=V` defaults."""
    env_path = Path.home() / ".config" / "arango" / "env.sh"
    values: Dict[str, str] = {}
    if not env_path.exists():
        return values
    for line in env_path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = line.strip()
        if not line.startswith("export ") or "=" not in line:
            continue
        key, value = line[len("export "):].split("=", 1)
        values[key.strip()] = value.strip().strip('"').strip("'")
    return values


ARANGO_ENV_FILE = _read_arango_env_file()


def _env_default(*names: str, fallback: str) -> str:
    for name in names:
        if os.environ.get(name):
            return os.environ[name]
        if ARANGO_ENV_FILE.get(name):
            return ARANGO_ENV_FILE[name]
    return fallback


class HttpArangoDB:
    """Tiny Arango `_api/cursor` fallback used when python-arango is absent.

    It POSTs AQL directly to `/_db/<db>/_api/cursor` with Basic auth.  It is
    intentionally small but enough for dumps and cone queries.
    """

    def __init__(self, endpoint: str, database: str, username: str, password: str):
        self.endpoint = endpoint.rstrip("/")
        self.database = database
        self.username = username
        self.password = password

    def aql_execute(self, query: str, bind_vars: Optional[Dict[str, Any]] = None) -> List[Dict[str, Any]]:
        body = json.dumps({
            "query": query,
            "bindVars": bind_vars or {},
            "batchSize": 10000,
        }).encode("utf-8")
        req = urllib.request.Request(
            f"{self.endpoint}/_db/{self.database}/_api/cursor",
            data=body,
            headers={"Content-Type": "application/json"},
        )
        token = base64.b64encode(f"{self.username}:{self.password}".encode()).decode()
        req.add_header("Authorization", f"Basic {token}")
        try:
            with urllib.request.urlopen(req, timeout=60) as response:
                result = json.load(response)
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            raise RuntimeError(f"Arango HTTP {exc.code}: {detail}") from exc
        if result.get("error"):
            raise RuntimeError(json.dumps(result, indent=2))
        rows = list(result.get("result", []))
        cursor_id = result.get("id")
        while result.get("hasMore") and cursor_id:
            req = urllib.request.Request(
                f"{self.endpoint}/_db/{self.database}/_api/cursor/{cursor_id}",
                data=b"",
                headers={"Content-Type": "application/json"},
            )
            req.add_header("Authorization", f"Basic {token}")
            try:
                with urllib.request.urlopen(req, timeout=60) as response:
                    result = json.load(response)
            except urllib.error.HTTPError as exc:
                detail = exc.read().decode("utf-8", errors="replace")
                raise RuntimeError(f"Arango HTTP {exc.code}: {detail}") from exc
            if result.get("error"):
                raise RuntimeError(json.dumps(result, indent=2))
            rows.extend(result.get("result", []))
            cursor_id = result.get("id")
        return rows


def _get_client(endpoint: str, username: str, password: str) -> Any:
    if ArangoClient is None:
        return None
    return ArangoClient(hosts=endpoint)


def _open_db(client: Any, endpoint: str, database: str, username: str, password: str) -> Any:
    if client is None:
        print("python-arango not available; using HTTP _api/cursor fallback", file=sys.stderr)
        return HttpArangoDB(endpoint, database, username, password)
    return client.db(database, username=username, password=password)


def _aql(db: Any, query: str, bind_vars: Optional[Dict[str, Any]] = None) -> List[Dict[str, Any]]:
    if isinstance(db, HttpArangoDB):
        return db.aql_execute(query, bind_vars)
    return list(db.aql.execute(query, bind_vars=bind_vars or {}))


def _collection_export(db: Any, collection_name: str) -> List[Dict[str, Any]]:
    if isinstance(db, HttpArangoDB):
        query = f"FOR doc IN @@collection RETURN doc"
        return _aql(db, query, {"@collection": collection_name})
    try:
        return [doc for doc in db.collection(collection_name).all()]
    except ArangoError:
        return []


def _resolve_seed_id(db: Any, node_collection: str, seed: str) -> str:
    """Accept either an Arango `_id`, `_key`, or declaration `name` as cone seed."""
    if "/" in seed:
        return seed
    rows = _aql(
        db,
        """
        FOR doc IN @@collection
          FILTER doc._key == @seed OR doc.name == @seed
          LIMIT 1
          RETURN doc._id
        """,
        {"@collection": node_collection, "seed": seed},
    )
    if not rows:
        raise SystemExit(
            f"Seed {seed!r} not found in collection {node_collection!r}; pass a full _id or existing name/_key."
        )
    return str(rows[0])


# ---------------------------------------------------------------------------
# AQL-powered causal cone
# ---------------------------------------------------------------------------

CAUSAL_CONE_DOWNSTREAM_AQL = """
FOR v, e, p IN 1..@max_depth OUTBOUND @seed_id @@edge_collection
  OPTIONS {uniqueVertices: "global", bfs: true}
  RETURN {
    node: {id: v._id, name: v.name, kind: v.kind, file: v.file, module: v.module},
    depth: LENGTH(p.edges),
    path: p.vertices[*]._id
  }
"""

CAUSAL_CONE_UPSTREAM_AQL = """
FOR v, e, p IN 1..@max_depth INBOUND @seed_id @@edge_collection
  OPTIONS {uniqueVertices: "global", bfs: true}
  RETURN {
    node: {id: v._id, name: v.name, kind: v.kind, file: v.file, module: v.module},
    depth: LENGTH(p.edges),
    path: p.vertices[*]._id
  }
"""

MULTI_APEX_CONES_AQL = """
FOR seed IN @seed_ids
  FOR v, e, p IN 1..@max_depth ANY seed @@edge_collection
    OPTIONS {uniqueVertices: "global", bfs: true}
    RETURN DISTINCT {
      node: {id: v._id, name: v.name, kind: v.kind, file: v.file, module: v.module},
      seed: seed,
      depth: LENGTH(p.edges)
    }
"""


def query_causal_cone(
    db: Any,
    seed_id: str,
    edge_collection: str,
    max_depth: int,
    direction: str = "downstream",
) -> List[Dict[str, Any]]:
    """Return the causal cone of `seed_id` following edges up to `max_depth`.

    direction: "downstream" (OUTBOUND), "upstream" (INBOUND), or "any" (ANY).
    """
    if direction == "downstream":
        aql = CAUSAL_CONE_DOWNSTREAM_AQL
    elif direction == "upstream":
        aql = CAUSAL_CONE_UPSTREAM_AQL
    elif direction == "any":
        aql = MULTI_APEX_CONES_AQL
    else:
        raise ValueError(f"unknown cone direction: {direction}")

    bind_vars: Dict[str, Any] = {
        "@edge_collection": edge_collection,
        "max_depth": max_depth,
    }
    if direction == "any":
        bind_vars["seed_ids"] = [seed_id]
    else:
        bind_vars["seed_id"] = seed_id

    return _aql(db, aql, bind_vars)


def query_multi_apex_cone(
    db: Any,
    seed_ids: List[str],
    edge_collection: str,
    max_depth: int,
) -> List[Dict[str, Any]]:
    """Causal cone around multiple seed nodes simultaneously."""
    return _aql(
        db,
        MULTI_APEX_CONES_AQL,
        {
            "seed_ids": seed_ids,
            "@edge_collection": edge_collection,
            "max_depth": max_depth,
        },
    )


# ---------------------------------------------------------------------------
# Graph format conversion
# ---------------------------------------------------------------------------


def to_force_graph(
    nodes: List[Dict[str, Any]],
    edges: List[Dict[str, Any]],
) -> Dict[str, Any]:
    """Convert ArangoDB documents to ForceGraph-compatible {nodes, links}."""
    result_nodes = []
    for n in nodes:
        n_out = dict(n)
        n_out["id"] = n.get("_id", n.get("id", ""))
        result_nodes.append(n_out)

    result_edges = []
    for e in edges:
        e_out = dict(e)
        e_out["source"] = e.get("_from", e.get("source", ""))
        e_out["target"] = e.get("_to", e.get("target", ""))
        result_edges.append(e_out)

    return {"nodes": result_nodes, "links": result_edges}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Dump ArangoDB DAG graph to JSON or extract causal cones."
    )
    parser.add_argument("--endpoint", default=_env_default("ARANGO_ENDPOINT", "ARANGO_URL", fallback="http://127.0.0.1:8530"))
    parser.add_argument("--database", default=_env_default("ARANGO_DATABASE", "ARANGO_DB", fallback="infogeometry"))
    parser.add_argument("--username", default=_env_default("ARANGO_USERNAME", "ARANGO_USER", fallback="root"))
    parser.add_argument("--password", default=_env_default("ARANGO_PASSWORD", fallback=""))
    parser.add_argument("--collection", default=_env_default("ARANGO_NODE_COLLECTION", fallback="dag_nodes"),
                        help="Node collection name; repo default: dag_nodes")
    parser.add_argument("--edges", default=_env_default("ARANGO_EDGE_COLLECTION", fallback="dag_edges"),
                        help="Edge collection name; repo default: dag_edges")
    parser.add_argument("--out", default="artifacts/leantrail/dag_graph.json")

    # Causal cone
    parser.add_argument("--cone-downstream", default=None,
                        help="Seed node ID for downstream causal cone")
    parser.add_argument("--cone-upstream", default=None,
                        help="Seed node ID for upstream causal cone")
    parser.add_argument("--cone-multi", default=None,
                        help="Comma-separated seed node IDs for multi-apex cone")
    parser.add_argument("--max-depth", type=int, default=5,
                        help="Max traversal depth for causal cone (default: 5)")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()

    client = _get_client(args.endpoint, args.username, args.password)
    db = _open_db(client, args.endpoint, args.database, args.username, args.password)

    out_path = Path(args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)

    try:
        # Causal cone mode
        if args.cone_downstream:
            seed_id = _resolve_seed_id(db, args.collection, args.cone_downstream)
            print(f"Causal cone DOWNSTREAM from: {seed_id}")
            results = query_causal_cone(
                db, seed_id, args.edges, args.max_depth, "downstream"
            )
            out_path.write_text(json.dumps(results, indent=2, ensure_ascii=True) + "\n")
            print(f"  {len(results)} nodes in cone -> {out_path}")
            return 0

        if args.cone_upstream:
            seed_id = _resolve_seed_id(db, args.collection, args.cone_upstream)
            print(f"Causal cone UPSTREAM from: {seed_id}")
            results = query_causal_cone(
                db, seed_id, args.edges, args.max_depth, "upstream"
            )
            out_path.write_text(json.dumps(results, indent=2, ensure_ascii=True) + "\n")
            print(f"  {len(results)} nodes in cone -> {out_path}")
            return 0

        if args.cone_multi:
            seeds = [_resolve_seed_id(db, args.collection, s.strip()) for s in args.cone_multi.split(",") if s.strip()]
            print(f"Multi-apex cone from: {seeds}")
            results = query_multi_apex_cone(db, seeds, args.edges, args.max_depth)
            out_path.write_text(json.dumps(results, indent=2, ensure_ascii=True) + "\n")
            print(f"  {len(results)} nodes in cone -> {out_path}")
            return 0

        # Full dump mode
        print(f"Dumping full graph from {args.database}.{args.collection} / .{args.edges}", flush=True)
        nodes = _collection_export(db, args.collection)
        edges = _collection_export(db, args.edges)

        graph = to_force_graph(nodes, edges)
        out_path.write_text(json.dumps(graph, indent=2, ensure_ascii=True) + "\n")

        print(f"  Nodes: {len(nodes)}  Edges: {len(edges)}")
        print(f"  Output: {out_path}")
        return 0
    except (ArangoError, ConnectionError, OSError, RuntimeError) as exc:
        print(f"Arango query failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
