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


def ingest_soldering_triality():
    # Connect to ArangoDB if available.
    connected = _connect_graph("QuantumTopology")
    if connected is None:
        return
    db, topo_graph = connected

    v_coll = topo_graph.vertex_collection("Theorems")
    e_coll = topo_graph.edge_collection("ProofSteps")

    # Add roadmap nodes for the matrix/spacetime soldering analogy.
    # These are graph annotations, not formal Lean theorem certificates.
    nodes = [
        {"_key": "Matrix_Algebra", "lean_name": "Matrix Algebra (Internal)", "type": "Algebraic", "kind": "Structure"},
        {"_key": "Spacetime_Manifold", "lean_name": "Spacetime Manifold (External)", "type": "Geometric", "kind": "Structure"},
        {"_key": "Determinant", "lean_name": "Determinant", "type": "Algebraic Invariant", "kind": "Invariant"},
        {"_key": "Minkowski_Metric", "lean_name": "Minkowski Quadratic Form", "type": "Geometric Invariant", "kind": "Invariant"},
        {"_key": "SL2C_Matrix_Transform", "lean_name": "SL(2, C) Transform", "type": "Algebraic Operation", "kind": "Transformation"},
        {"_key": "Lorentz_Transformation", "lean_name": "Lorentz Transform", "type": "Geometric Operation", "kind": "Transformation"},
        {"_key": "Cartan_Soldering_Form", "lean_name": "Cartan Soldering Equivalence", "type": "Theorem", "kind": "Bridge"}
    ]

    for node in nodes:
        if not v_coll.has(node["_key"]):
            v_coll.insert(node)

    # Add intended comparison/dependency edges between the roadmap nodes.
    edges = [
        {"_from": "Theorems/Matrix_Algebra", "_to": "Theorems/Spacetime_Manifold", "relation": "soldering_map"},
        {"_from": "Theorems/Determinant", "_to": "Theorems/Minkowski_Metric", "relation": "is_isometrically_equivalent"},
        {"_from": "Theorems/SL2C_Matrix_Transform", "_to": "Theorems/Lorentz_Transformation", "relation": "induces"},
        {"_from": "Theorems/Cartan_Soldering_Form", "_to": "Theorems/Matrix_Algebra", "relation": "unifies"},
        {"_from": "Theorems/Cartan_Soldering_Form", "_to": "Theorems/Spacetime_Manifold", "relation": "unifies"},
        # Link back to the pre-existing Weyl Gauge node we ingested earlier
        {"_from": "Theorems/Minkowski_Metric", "_to": "Theorems/WeylSector", "relation": "classified_by_causal_cone"}
    ]

    for edge in edges:
        try:
            e_coll.insert(edge)
        except Exception as e:
            print(f"Edge exists or error: {e}")

    print("Ingested Cartan-soldering roadmap annotations into ArangoDB.")

if __name__ == "__main__":
    ingest_soldering_triality()
