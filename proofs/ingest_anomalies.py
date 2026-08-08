from __future__ import annotations

import os

from arango import ArangoClient

ARANGO_HOST = os.environ.get("ARANGO_URL", os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8530"))
ARANGO_DB = os.environ.get("ARANGO_DATABASE", os.environ.get("ARANGO_DB", "LeanAST"))
ARANGO_USER = os.environ.get("ARANGO_USER", os.environ.get("ARANGO_USERNAME", "root"))
ARANGO_PASSWORD = os.environ.get("ARANGO_PASSWORD", "")
GRAPH_NAME = "QuantumTopology"


def _connect_db():
    try:
        client = ArangoClient(hosts=ARANGO_HOST)
        sys_db = client.db("_system", username=ARANGO_USER, password=ARANGO_PASSWORD)
        if not sys_db.has_database(ARANGO_DB):
            sys_db.create_database(ARANGO_DB)
        db = client.db(ARANGO_DB, username=ARANGO_USER, password=ARANGO_PASSWORD)
        if not db.has_graph(GRAPH_NAME):
            db.create_graph(GRAPH_NAME)
        graph = db.graph(GRAPH_NAME)
        if not graph.has_vertex_collection("Theorems"):
            graph.create_vertex_collection("Theorems")
        if not graph.has_edge_definition("ProofSteps"):
            graph.create_edge_definition(
                edge_collection="ProofSteps",
                from_vertex_collections=["Theorems"],
                to_vertex_collections=["Theorems"],
            )
        return db
    except Exception as exc:
        print(f"Skipping Arango ingest (unavailable): {ARANGO_HOST} :: {exc}")
        return None


def ingest_anomalies():
    db = _connect_db()
    if db is None:
        return

    topo_graph = db.graph(GRAPH_NAME)
    v_coll = topo_graph.vertex_collection("Theorems")
    e_coll = topo_graph.edge_collection("ProofSteps")

    # Add project-roadmap nodes for the non-orientable/orbifold anomaly story.
    # These graph annotations are not Lean proofs by themselves.
    nodes = [
        {"_key": "KleinBottle", "lean_name": "KleinBottle", "type": "Topology", "kind": "Manifold"},
        {"_key": "Orbifold", "lean_name": "Non-Orientable Orbifold", "type": "Topology", "kind": "Orbifold"},
        {"_key": "CPT_Symmetry", "lean_name": "CPT Symmetry", "type": "Physics", "kind": "Symmetry"},
        {"_key": "AnomalyCancellation", "lean_name": "Anomaly Cancellation", "type": "Physics", "kind": "Mechanism"},
        {"_key": "M", "lean_name": "M", "type": "ℂ → ℂ", "kind": "Definition"},
        {"_key": "H", "lean_name": "H", "type": "ℂ → ℂ", "kind": "Definition"},
        {"_key": "G", "lean_name": "G", "type": "ℂ → ℂ", "kind": "Definition"},
        {"_key": "klein_bottle_relation", "lean_name": "klein_bottle_relation", "type": "Theorem", "kind": "Theorem"}
    ]

    for node in nodes:
        if not v_coll.has(node["_key"]):
            v_coll.insert(node)

    # Add intended dependency/analogy edges between the roadmap nodes.
    edges = [
        {"_from": "Theorems/M", "_to": "Theorems/CPT_Symmetry", "relation": "implements"},
        {"_from": "Theorems/H", "_to": "Theorems/Orbifold", "relation": "generates_cone_point"},
        {"_from": "Theorems/M", "_to": "Theorems/Orbifold", "relation": "generates_mirror_boundary"},
        {"_from": "Theorems/Orbifold", "_to": "Theorems/KleinBottle", "relation": "resolves_to"},
        {"_from": "Theorems/KleinBottle", "_to": "Theorems/AnomalyCancellation", "relation": "cancels_anomalies"},
        {"_from": "Theorems/CPT_Symmetry", "_to": "Theorems/AnomalyCancellation", "relation": "pairs_particles_holes"},
        {"_from": "Theorems/klein_bottle_relation", "_to": "Theorems/KleinBottle", "relation": "defines_fundamental_group"},
        {"_from": "Theorems/G", "_to": "Theorems/klein_bottle_relation", "relation": "generator"}
    ]

    for edge in edges:
        try:
            e_coll.insert(edge)
        except Exception as exc:
            print(f"Edge exists or error: {exc}")

    print("Ingested Klein-bottle/orbifold anomaly roadmap annotations into ArangoDB.")


if __name__ == "__main__":
    ingest_anomalies()
