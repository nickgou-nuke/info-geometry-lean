#!/usr/bin/env python3
"""
ingest_triality_graph.py
Ingests the D4 Triality / Cl(5,5) framework into ArangoDB.

Creates a knowledge graph linking:
- Lean files and theorems
- Wieser thesis concepts
- Nuclear physics data (B(E1) ratios)
- External repos (gatl, lean-ga, etc.)

Usage:
  python3 ingest_triality_graph.py
"""

import json
import requests
from datetime import datetime

# ArangoDB Configuration
ARANGODB_URL = "http://localhost:8529"
ARANGODB_DB = "_system"
ARANGODB_USER = "root"
ARANGODB_PASS = ""  # Set if password protected

# Graph Name
GRAPH_NAME = "tkk_triality_knowledge_graph"

# ==============================================================================
# DATA DEFINITIONS
# ==============================================================================

# 1. Lean Files
lean_files = [
    {
        "_key": "Clifford55_lean",
        "path": "/home/goutev/auto/proofs/Clifford55.lean",
        "type": "LeanModule",
        "concepts": ["Cl(5,5)", "Pin(5,5)", "Q8_group", "gradeInvolution", "LipschitzGroup"],
        "theorems": ["V4_relations", "gradeInvolution_sq", "lipschitz_eq_pin"],
        "status": "70% complete"
    },
    {
        "_key": "TrialityBridge_lean",
        "path": "/home/goutev/auto/proofs/TrialityBridge.lean",
        "type": "LeanModule",
        "concepts": ["Cl-Zorn isomorphism", "mass splitting", "B(E1) ratio"],
        "theorems": ["q8_mass_splitting", "empirical_fit_A31"],
        "status": "70% complete"
    },
    {
        "_key": "ZornCore_lean",
        "path": "/home/goutev/auto/proofs/ZornCore.lean",
        "type": "LeanModule",
        "concepts": ["Zorn matrices", "Split-octonions", "associator"],
        "theorems": ["mixed_nonassociative", "U_nilpotent"],
        "status": "complete"
    },
    {
        "_key": "MasterUnification_lean",
        "path": "/home/goutev/auto/proofs/MasterUnification.lean",
        "type": "LeanModule",
        "concepts": ["Data-driven proofs", "D4 roots", "S3 action"],
        "theorems": ["triality_maps_vector_to_spinor"],
        "status": "50% complete"
    }
]

# 2. Wieser Thesis Concepts
wieser_concepts = [
    {
        "_key": "grade_involution",
        "type": "MathConcept",
        "source": "Wieser Thesis Ch.3",
        "definition": "α: Cl → Cl with α(v) = -v",
        "application": "Defines Pin vs Spin twisted adjoint"
    },
    {
        "_key": "lipschitz_group",
        "type": "MathConcept",
        "source": "Wieser Thesis Ch.4",
        "definition": "Γ = {g ∈ Clˣ | gVg⁻¹ ⊆ V}",
        "application": "Alternative Pin(5,5) definition"
    },
    {
        "_key": "spinor_norm",
        "type": "MathConcept",
        "source": "Wieser Thesis Ch.4",
        "definition": "N(g) = g·α(g) (scalar part)",
        "application": "Determinant formula det(Ad_g) = N(g)⁵"
    },
    {
        "_key": "spectral_characterization",
        "type": "MathConcept",
        "source": "Wieser Thesis Ch.5",
        "definition": "Eigenvalues of Ad_g action",
        "application": "B(E1) amplitudes as spectra"
    }
]

# 3. Nuclear Physics Data
nuclear_data = [
    {
        "_key": "A31_mirror",
        "type": "Nucleus",
        "A": 31,
        "Z": 15,  # Phosphorus
        "B_E1_ratio": 2.32,
        "fitted_epsilon": 0.12,
        "fitted_delta": 0.04,
        "status": "verified"
    },
    {
        "_key": "A35_mirror",
        "type": "Nucleus",
        "A": 35,
        "B_E1_ratio": None,  # Prediction needed
        "predicted_ratio": 1.9,
        "status": "prediction"
    },
    {
        "_key": "A67_mirror",
        "type": "Nucleus",
        "A": 67,
        "B_E1_ratio": None,
        "predicted_ratio": 1.5,
        "status": "prediction"
    }
]

# 4. External Repositories
external_repos = [
    {
        "_key": "gatl",
        "url": "https://github.com/laffernandes/gatl",
        "type": "LeanRepo",
        "relevance": "Clifford group formalization",
        "priority": "CRITICAL"
    },
    {
        "_key": "lean_ga",
        "url": "https://github.com/pygae/lean-ga",
        "type": "LeanRepo",
        "relevance": "Python-Lean bridge",
        "priority": "HIGH"
    },
    {
        "_key": "lean_graded_rings",
        "url": "https://github.com/eric-wieser/lean-graded-rings",
        "type": "LeanRepo",
        "relevance": "Graded algebra structures",
        "priority": "HIGH"
    }
]

# ==============================================================================
# ARANGODB FUNCTIONS
# ==============================================================================

def get_arango_session():
    session = requests.Session()
    session.auth = (ARANGODB_USER, ARANGODB_PASS)
    session.headers.update({"Content-Type": "application/json"})
    return session

def create_database_if_not_exists(session):
    url = f"{ARANGODB_URL}/_api/database/{ARANGODB_DB}"
    resp = session.get(url)
    if resp.status_code == 404:
        print(f"❌ Database '{ARANGODB_DB}' not found. Please create it first.")
        return False
    return True

def create_collection(session, name, schema_type="document"):
    url = f"{ARANGODB_URL}/_api/collection"
    data = {"name": name, "type": 2 if schema_type == "document" else 3}
    resp = session.post(url, data=json.dumps(data))
    if resp.status_code in [200, 409]:  # 409 = already exists
        print(f"✓ Collection '{name}' ready")
        return True
    else:
        print(f"❌ Failed to create '{name}': {resp.text}")
        return False

def insert_documents(session, collection, docs):
    url = f"{ARANGODB_URL}/_api/document/{collection}?waitForSync=true"
    resp = session.post(url, data=json.dumps(docs))
    if resp.status_code == 201:
        print(f"✓ Inserted {len(docs)} docs into '{collection}'")
        return True
    else:
        print(f"❌ Failed: {resp.text}")
        return False

def create_edge_collection(session, name):
    return create_collection(session, name, schema_type="edge")

def insert_edges(session, collection, edges):
    url = f"{ARANGODB_URL}/_api/document/{collection}?waitForSync=true"
    resp = session.post(url, data=json.dumps(edges))
    if resp.status_code == 201:
        print(f"✓ Created {len(edges)} edges in '{collection}'")
        return True
    else:
        print(f"❌ Failed: {resp.text}")
        return False

# ==============================================================================
# MAIN INGESTION PIPELINE
# ==============================================================================

def main():
    print("="*60)
    print("ArangoDB Ingestion: TKK Triality Knowledge Graph")
    print("="*60)
    
    session = get_arango_session()
    
    # Test connection
    try:
        resp = session.get(f"{ARANGODB_URL}/_api/version")
        if resp.status_code != 200:
            print("❌ Cannot connect to ArangoDB. Is it running?")
            return
        print("✓ Connected to ArangoDB")
    except Exception as e:
        print(f"❌ Connection error: {e}")
        return
    
    if not create_database_if_not_exists(session):
        return
    
    # Create collections
    collections = ["lean_files", "math_concepts", "nuclear_data", "external_repos"]
    for coll in collections:
        create_collection(session, coll)
    
    # Create edge collection
    create_edge_collection(session, "relationships")
    
    # Insert documents
    print("\n--- Inserting Documents ---")
    insert_documents(session, "lean_files", lean_files)
    insert_documents(session, "math_concepts", wieser_concepts)
    insert_documents(session, "nuclear_data", nuclear_data)
    insert_documents(session, "external_repos", external_repos)
    
    # Create edges (relationships)
    print("\n--- Creating Relationships ---")
    edges = [
        # Lean files -> Concepts
        {"_from": "lean_files/Clifford55_lean", "_to": "math_concepts/grade_involution", "type": "implements"},
        {"_from": "lean_files/Clifford55_lean", "_to": "math_concepts/lipschitz_group", "type": "implements"},
        {"_from": "lean_files/Clifford55_lean", "_to": "math_concepts/spinor_norm", "type": "implements"},
        {"_from": "lean_files/TrialityBridge_lean", "_to": "math_concepts/spectral_characterization", "type": "uses"},
        
        # Nuclear data -> Lean files
        {"_from": "nuclear_data/A31_mirror", "_to": "lean_files/TrialityBridge_lean", "type": "verified_by"},
        {"_from": "nuclear_data/A35_mirror", "_to": "lean_files/TrialityBridge_lean", "type": "predicted_by"},
        {"_from": "nuclear_data/A67_mirror", "_to": "lean_files/TrialityBridge_lean", "type": "predicted_by"},
        
        # External repos -> Lean files
        {"_from": "external_repos/gatl", "_to": "lean_files/Clifford55_lean", "type": "enhances"},
        {"_from": "external_repos/lean_ga", "_to": "lean_files/ZornCore_lean", "type": "enhances"},
    ]
    
    insert_edges(session, "relationships", edges)
    
    # Summary
    print("\n" + "="*60)
    print("✅ INGESTION COMPLETE")
    print(f"   Collections: {len(collections) + 1}")
    print(f"   Documents: {len(lean_files) + len(wieser_concepts) + len(nuclear_data) + len(external_repos)}")
    print(f"   Relationships: {len(edges)}")
    print(f"   Graph: {GRAPH_NAME}")
    print("="*60)
    print("\nTo query:")
    print(f"  arangosh --database {ARANGODB_DB}")
    print("  db._query(`FOR f IN lean_files RETURN f`).toArray()")

if __name__ == "__main__":
    main()