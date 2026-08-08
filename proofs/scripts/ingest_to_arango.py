#!/usr/bin/env python3
"""
Ingest ExtractGraph JSON into ArangoDB.

Usage:
  # Start ArangoDB (Docker), choosing either an empty local password or an
  # explicit one supplied via ARANGO_PASSWORD:
  docker run -e ARANGO_NO_AUTH=1 -p 8529:8529 -d arangodb

  # Install deps:
  pip install python-arango

  # Run ingestion, overriding endpoint/password if needed:
  ARANGO_URL=http://127.0.0.1:8529 python3 scripts/ingest_to_arango.py
"""

import os
import json
from pathlib import Path

from arango import ArangoClient

DB_NAME = os.environ.get("ARANGO_DB", "lean_proofs")
JSON_PATH = Path(__file__).parent.parent / "proof_graph.json"
ARANGO_HOST = os.environ.get("ARANGO_URL", os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8529"))
ARANGO_USER = os.environ.get("ARANGO_USER", os.environ.get("ARANGO_USERNAME", "root"))
ARANGO_PASSWORD = os.environ.get("ARANGO_PASSWORD", "")


def setup_database(db):
    """Create collections and graph if they don't exist."""
    # Vertex collections
    for name in ["declarations", "modules", "tactics"]:
        if not db.has_collection(name):
            db.create_collection(name)

    # Edge collections
    for name in ["depends_on", "defines", "uses_tactic"]:
        if not db.has_collection(name):
            db.create_collection(name)

    # Graph
    if not db.has_graph("proof_graph"):
        graph = db.create_graph("proof_graph")
        graph.create_edge_definition(
            edge_collection="depends_on",
            from_vertex_collections=["declarations"],
            to_vertex_collections=["declarations"],
        )


def ingest_declarations(db, decls):
    """Insert declaration vertices and dependency edges from ExtractGraph JSON."""
    decls_coll = db.collection("declarations")
    edges_coll = db.collection("depends_on")

    count = 0
    edge_count = 0

    for decl in decls:
        key = decl["name"].replace(".", "_")
        doc = {
            "_key": key,
            "name": decl["name"],
            "kind": decl.get("kind", "unknown"),
            "module": decl["name"].split(".")[0],
        }
        decls_coll.insert(doc, overwrite=True)
        count += 1

        # Insert dependency edges
        for dep in decl.get("deps", []):
            dep_key = dep.replace(".", "_")
            edge = {
                "_from": f"declarations/{key}",
                "_to": f"declarations/{dep_key}",
            }
            try:
                edges_coll.insert(edge)
                edge_count += 1
            except Exception:
                # Target vertex might not exist (for example, a Mathlib/stdlib dep
                # outside the exported graph), or the edge may already exist.
                pass

    return count, edge_count


def _connect_db():
    try:
        client = ArangoClient(hosts=ARANGO_HOST)
        sys_db = client.db("_system", username=ARANGO_USER, password=ARANGO_PASSWORD)
        if not sys_db.has_database(DB_NAME):
            sys_db.create_database(DB_NAME)
        return client.db(DB_NAME, username=ARANGO_USER, password=ARANGO_PASSWORD)
    except Exception as exc:
        print(f"Skipping Arango ingest (unavailable): {ARANGO_HOST} :: {exc}")
        return None


def main():
    db = _connect_db()
    if db is None:
        return

    setup_database(db)

    # Load JSON
    if not JSON_PATH.exists():
        print(f"Proof graph not found at {JSON_PATH}; nothing to ingest")
        return

    with open(JSON_PATH) as f:
        decls = json.load(f)

    print(f"Loaded {len(decls)} declarations from {JSON_PATH}")

    # Ingest
    node_count, edge_count = ingest_declarations(db, decls)
    print(f"Ingested {node_count} nodes, {edge_count} edges")
    print("Done.")


if __name__ == "__main__":
    main()
