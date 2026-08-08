#!/usr/bin/env python3
from __future__ import annotations

import json
import os
from pathlib import Path

from arango import ArangoClient


def env_first(*names: str, default: str | None = None) -> str | None:
    for name in names:
        value = os.environ.get(name)
        if value:
            return value
    return default


ARANGO_HOST = env_first("ARANGO_URL", "ARANGO_ENDPOINT", "ARANGO_HOST", default="http://127.0.0.1:8530")
ARANGO_ROOT_DB = "_system"
ARANGO_DB = env_first("ARANGO_DATABASE", "ARANGO_DB", default="LeanAST")
ARANGO_USER = env_first("ARANGO_USER", "ARANGO_USERNAME", default="root")
ARANGO_PASSWORD = env_first("ARANGO_PASSWORD", "ARANGO_PASS", default="") or ""
ARANGO_GRAPH = env_first("ARANGO_GRAPH", default="QuantumTopology")


def load_graph_payload(json_path: str):
    """Load either ExtractGraph list JSON or node/edge graph JSON."""
    with open(json_path, "r", encoding="utf-8") as f:
        payload = json.load(f)

    if isinstance(payload, list):
        nodes = [
            {
                "name": rec["name"],
                "type": rec.get("type", rec.get("kind", "unknown")),
                "kind": rec.get("kind", "unknown"),
                "deps": rec.get("deps", []),
            }
            for rec in payload
        ]
        edges = []
        for rec in payload:
            for dep in rec.get("deps", []):
                edges.append({"from_node": rec["name"], "to_node": dep, "relation": "depends_on"})
        return nodes, edges

    if isinstance(payload, dict):
        return payload.get("nodes", []), payload.get("edges", payload.get("links", []))

    raise SystemExit(f"Unsupported graph format in {json_path}")


def _connect_db():
    try:
        client = ArangoClient(hosts=ARANGO_HOST)
        sys_db = client.db(ARANGO_ROOT_DB, username=ARANGO_USER, password=ARANGO_PASSWORD)
        if ARANGO_DB is None:
            raise ValueError("ARANGO_DB resolved to None")
        if not sys_db.has_database(ARANGO_DB):
            sys_db.create_database(ARANGO_DB)
        return client.db(ARANGO_DB, username=ARANGO_USER, password=ARANGO_PASSWORD)
    except Exception as exc:
        print(f"Skipping Arango ingest (unavailable): {ARANGO_HOST} :: {exc}")
        return None


def _select_graph_json() -> str | None:
    candidates = [
        Path(os.getenv("ARANGO_GRAPH_JSON", "")) if os.getenv("ARANGO_GRAPH_JSON") else None,
        Path(__file__).with_name("proof_graph.json"),
        Path(__file__).with_name("ast_graph.json"),
        Path("/home/goutev/auto/proofs/proof_graph.json"),
        Path("/home/goutev/auto/proofs/ast_graph.json"),
    ]
    return next((str(p) for p in candidates if p is not None and p.exists()), None)


def sanitize_key(name: str) -> str:
    return name.replace(".", "_").replace("'", "_").replace(" ", "")


def main() -> None:
    json_path = _select_graph_json()
    if json_path is None:
        print("No graph JSON found (proof_graph.json or ast_graph.json)")
        return

    nodes, edges = load_graph_payload(json_path)
    print(f"Loaded {len(nodes)} nodes and {len(edges)} edges from {json_path}.")

    db = _connect_db()
    if db is None:
        return

    graph_name = ARANGO_GRAPH or "QuantumTopology"
    if db.has_graph(graph_name):
        db.delete_graph(graph_name, drop_collections=True)

    topo_graph = db.create_graph(graph_name)

    v_coll_name = "Theorems"
    e_coll_name = "ProofSteps"

    if not topo_graph.has_vertex_collection(v_coll_name):
        v_coll = topo_graph.create_vertex_collection(v_coll_name)
    else:
        v_coll = topo_graph.vertex_collection(v_coll_name)

    if not topo_graph.has_edge_definition(e_coll_name):
        e_coll = topo_graph.create_edge_definition(
            edge_collection=e_coll_name,
            from_vertex_collections=[v_coll_name],
            to_vertex_collections=[v_coll_name],
        )
    else:
        e_coll = topo_graph.edge_collection(e_coll_name)

    print("Ingesting Nodes...")
    arango_nodes = []
    for node in nodes:
        name = node["name"]
        arango_nodes.append(
            {
                "_key": sanitize_key(name),
                "lean_name": name,
                "type": node.get("type", node.get("kind", "unknown")),
                "kind": node.get("kind", "unknown"),
            }
        )
    v_coll.insert_many(arango_nodes)

    print("Ingesting Edges...")
    arango_edges = []
    saved_keys = {n["_key"] for n in arango_nodes}

    for edge in edges:
        from_name = edge.get("from_node") or edge.get("from") or edge.get("source")
        to_name = edge.get("to_node") or edge.get("to") or edge.get("target")
        if not from_name or not to_name:
            continue
        from_key = sanitize_key(from_name)
        to_key = sanitize_key(to_name)
        if from_key in saved_keys and to_key in saved_keys:
            arango_edges.append(
                {
                    "_from": f"{v_coll_name}/{from_key}",
                    "_to": f"{v_coll_name}/{to_key}",
                    "relation": edge.get("relation", "depends_on"),
                }
            )

    e_coll.insert_many(arango_edges)
    print(f"Successfully inserted {len(arango_edges)} internal logical edges.")

    target_theorem = os.getenv("ARANGO_TARGET_THEOREM", "braid_adj")
    aql_query = f"""
    FOR v, e, p IN 1..10 OUTBOUND 'Theorems/{target_theorem}' ProofSteps
        SORT LENGTH(p.edges) DESC
        RETURN {{
            "target": v.lean_name,
            "p_adic_depth": LENGTH(p.edges),
            "path": p.vertices[*].lean_name
        }}
    """

    try:
        cursor = db.aql.execute(aql_query)
        results = list(cursor)
        print(f"Found {len(results)} topological dependency paths from {target_theorem}.")
        if results:
            print("\nDeepest dependencies (High p-adic distance):")
            for r in results[:5]:
                print(f" -> Depth {r['p_adic_depth']}: {r['target']}")
    except Exception as exc:
        print(f"AQL execution failed (is {target_theorem} in the DB?): {exc}")


if __name__ == "__main__":
    main()
