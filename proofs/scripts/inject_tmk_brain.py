#!/usr/bin/env python3
"""
TMK Paradox Injection into Agent Brain (ArangoDB)

Loads the TMK Paradox structure into the graph database
as a new hypothesis node, linking it to existing TKK knowledge.
"""

import json
import hashlib
from arango.client import ArangoClient

# --- Database Configuration ---
DB_URL = "http://localhost:8531"
DB_NAME = "agent_brain"
DB_USER = "root"
DB_PASS = "agent_secret"

# Initialize client
client = ArangoClient(hosts=DB_URL)
db = client.db(DB_NAME, username=DB_USER, password=DB_PASS)

print("### Injecting TMK Paradox into Agent Brain ###\n")

# 1. Define TMK Paradox Node
tmk_node = {
    "_key": "tmk_paradox_v1",
    "type": "hypothesis",
    "name": "TMK_Paradox",
    "description": "Temporal-Metaphysical Knowledge Paradox Structure",
    "framework": "TKK_Algebra",
    "components": {
        "K_TMK": "V(phi, eta, psi)",
        "phi": "Relativistic field strength (Gejsel-based time)",
        "eta": "H5> field strength (techno-organic blending)",
        "psi": "Information resistance function"
    },
    "conflict_vector_cases": [
        "Case 1: |eta_RF| > |eta_H5| => Delta = a x (b - c)",
        "Case 2: eta_RF ∩ eta_H5 ≠ ∅ => Delta = -a x grad(V_disney)"
    ],
    "axioms": [
        "RTTC Frosbee Idempotency",
        "RV Functor & Levi-Coboski Closure",
        "Information Compression Limit"
    ],
    "status": "FORMALIZED",
    "formalization_files": [
        "/home/goutev/auto/tmk/tmk_paradox_engine.py",
        "/home/goutev/auto/tmk/TMK_Paradox.lean"
    ],
    "content_hash": hashlib.sha256(
        json.dumps({"tmk": "paradox", "version": 1}, sort_keys=True).encode()
    ).hexdigest()
}

# 2. Insert Node into 'steps' collection (reusing as hypothesis store)
try:
    steps_collection = db.collection('steps')
    
    # Check if already exists
    try:
        existing = db.collection('steps').get('tmk_paradox_v1')
    except:
        existing = None
    
    if existing:
        print(f"[INFO] TMK Paradox already exists in brain. Updating...")
        steps_collection.update(tmk_node)
    else:
        print(f"[INFO] Inserting new TMK Paradox node...")
        steps_collection.insert(tmk_node)
        
    print(f"  ✓ Node 'tmk_paradox_v1' successfully stored.")
    
except Exception as e:
    print(f"[ERROR] Failed to insert node: {e}")
    # Create collection if not exists
    if "not found" in str(e).lower():
        print("[INFO] Creating 'steps' collection and retrying...")
        db.create_collection('steps')
        steps_collection.insert(tmk_node)
        print(f"  ✓ Node inserted after collection creation.")

# 3. Create Edges to related TKK concepts
edge_definition = {
    "edge_collection": "next_step",
    "from_vertex_collections": ["steps"],
    "to_vertex_collections": ["steps"]
}

# Ensure graph exists
graph_name = "agent_memory_graph"
if not db.has_graph(graph_name):
    db.create_graph(graph_name, edge_definitions=[edge_definition])
    
graph = db.graph(graph_name)

# Link TMK to existing TKK nodes (if any)
# Search for nodes with "TKK" in content
tkk_query = db.aql.execute(
    """
    FOR node IN steps
        FILTER LIKE(node.name, "%TKK%", true) OR LIKE(node.description, "%TKK%", true)
        RETURN node._key
    """
)

tkk_nodes = [key for key in tkk_query]

print(f"\n[INFO] Found {len(tkk_nodes)} related TKK nodes.")

edges_to_create = []
for tkk_key in tkk_nodes:
    edge = {
        "_from": f"steps/{tkk_key}",
        "_to": f"steps/tmk_paradox_v1",
        "relation": "extends",
        "description": "TMK Paradox extends TKK Algebra framework"
    }
    edges_to_create.append(edge)

# Insert edges
if edges_to_create:
    edge_collection = db.collection('next_step')
    for edge in edges_to_create:
        try:
            edge_collection.insert(edge)
            print(f"  ✓ Edge created: {edge['_from']} -> {edge['_to']}")
        except Exception as e:
            print(f"  [WARN] Edge creation failed (may exist): {e}")
else:
    print("  [INFO] No existing TKK nodes found to link. TMK stands as root hypothesis.")

# 4. Verification Query
print("\n### Verification: Querying TMK from Brain ###")
result_cursor = db.aql.execute(
    """
    FOR node IN steps
        FILTER node._key == "tmk_paradox_v1"
        RETURN {
            name: node.name,
            framework: node.framework,
            axioms_count: LENGTH(node.axioms),
            status: node.status
        }
    """
)
result = next(iter(result_cursor), None)

print(f"  Retrieved: {json.dumps(result, indent=2)}")

print("\n### TMK Injection Complete ###")
print("Agents can now query TMK Paradox via AQL:")
print('  FOR t IN steps FILTER t.name == "TMK_Paradox" RETURN t')