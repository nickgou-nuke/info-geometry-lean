from __future__ import annotations

import os

from arango import ArangoClient

ARANGO_HOST = os.environ.get("ARANGO_URL", os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8530"))
ARANGO_DB = os.environ.get("ARANGO_DATABASE", os.environ.get("ARANGO_DB", "LeanAST"))
ARANGO_USER = os.environ.get("ARANGO_USER", os.environ.get("ARANGO_USERNAME", "root"))
ARANGO_PASSWORD = os.environ.get("ARANGO_PASSWORD", "")


def _connect_graph(graph_name: str = "QuantumTopology"):
    try:
        client = ArangoClient(hosts=ARANGO_HOST)
        sys_db = client.db("_system", username=ARANGO_USER, password=ARANGO_PASSWORD)
        if not sys_db.has_database(ARANGO_DB):
            sys_db.create_database(ARANGO_DB)
        db = client.db(ARANGO_DB, username=ARANGO_USER, password=ARANGO_PASSWORD)
        if not db.has_graph(graph_name):
            db.create_graph(graph_name)
        topo_graph = db.graph(graph_name)
        if not topo_graph.has_vertex_collection("Theorems"):
            topo_graph.create_vertex_collection("Theorems")
        if not topo_graph.has_edge_definition("ProofSteps"):
            topo_graph.create_edge_definition(
                edge_collection="ProofSteps",
                from_vertex_collections=["Theorems"],
                to_vertex_collections=["Theorems"],
            )
        return db, topo_graph
    except Exception as exc:
        print(f"Skipping Arango ingest (unavailable): {ARANGO_HOST} :: {exc}")
        return None


def ingest_weyl_gauge():
    # Connect to ArangoDB if available.
    connected = _connect_graph("QuantumTopology")
    if connected is None:
        return
    db, topo_graph = connected

    v_coll = topo_graph.vertex_collection("Theorems")
    e_coll = topo_graph.edge_collection("ProofSteps")

    # Add roadmap nodes for Weyl-gauge/V4 actions. These are graph annotations,
    # not formal Lean theorem certificates.
    nodes = [
        {"_key": "WeylSector", "lean_name": "WeylSector", "type": "Topology", "kind": "Classifier"},
        {"_key": "P", "lean_name": "P (Parity)", "type": "Matrix → Matrix", "kind": "Definition"},
        {"_key": "T_op", "lean_name": "T_op (Time Reversal)", "type": "Matrix → Matrix", "kind": "Definition"},
        {"_key": "PT", "lean_name": "PT (CPT Inversion)", "type": "Matrix → Matrix", "kind": "Definition"},
        {"_key": "det_PT", "lean_name": "det_PT", "type": "Theorem", "kind": "Theorem"}
    ]

    for node in nodes:
        if not v_coll.has(node["_key"]):
            v_coll.insert(node)

    # Add intended comparison/dependency edges linking the roadmap nodes.
    edges = [
        {"_from": "Theorems/WeylSector", "_to": "Theorems/KleinBottle", "relation": "classifies_topology"},
        {"_from": "Theorems/P", "_to": "Theorems/CPT_Symmetry", "relation": "implements_parity"},
        {"_from": "Theorems/T_op", "_to": "Theorems/CPT_Symmetry", "relation": "implements_time_reversal"},
        {"_from": "Theorems/PT", "_to": "Theorems/CPT_Symmetry", "relation": "is_full_inversion"},
        {"_from": "Theorems/PT", "_to": "Theorems/WeylSector", "relation": "preserves_signature"},
        {"_from": "Theorems/det_PT", "_to": "Theorems/AnomalyCancellation", "relation": "certifies_invariance"}
    ]

    for edge in edges:
        try:
            e_coll.insert(edge)
        except Exception as e:
            print(f"Edge exists or error: {e}")

    print("Ingested Weyl-gauge/CPT roadmap annotations into ArangoDB.")

if __name__ == "__main__":
    ingest_weyl_gauge()
