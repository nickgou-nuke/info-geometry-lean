#!/usr/bin/env python3
"""Interrogating the causal chain from Fenchel to Vorticity."""

import os
import json
import base64
from urllib.request import Request, urlopen

ENDPOINT = os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8530").rstrip("/")
DATABASE = os.environ.get("ARANGO_DATABASE", "infogeometry")
USER = os.environ.get("ARANGO_USER") or os.environ.get("ARANGO_USERNAME", "root")
PASSWORD = os.environ.get("ARANGO_PASS") or os.environ.get("ARANGO_PASSWORD", "alexandria_root")

def query_arango(aql, bind_vars=None):
    token = base64.b64encode(f"{USER}:{PASSWORD}".encode()).decode("ascii")
    url = f"{ENDPOINT}/_db/{DATABASE}/_api/cursor"
    payload = {"query": aql, "bindVars": bind_vars or {}}
    req = Request(url, data=json.dumps(payload).encode("utf-8"), method="POST")
    req.add_header("Authorization", f"Basic {token}")
    req.add_header("Content-Type", "application/json")
    try:
        with urlopen(req) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        print(f"Error querying ArangoDB: {e}")
        return None

def interrogate_causal_chain():
    # 1. Lookup the correct node IDs dynamically
    vort_query = """
    FOR node IN ig_nodes
      FILTER CONTAINS(node.name, "vorticity_isDivergenceFree")
      LIMIT 1
      RETURN node._id
    """
    fenchel_query = """
    FOR node IN ig_nodes
      FILTER CONTAINS(node.name, "bregman_as_fenchelGap") || CONTAINS(node.name, "fenchel_legendre")
      LIMIT 1
      RETURN node._id
    """
    
    vort_res = query_arango(vort_query)
    fenchel_res = query_arango(fenchel_query)
    
    vort_id = vort_res["result"][0] if vort_res and vort_res.get("result") else None
    fenchel_id = fenchel_res["result"][0] if fenchel_res and fenchel_res.get("result") else None
    
    if not vort_id or not fenchel_id:
        print("⚡ The spine is disconnected or hidden. Check graph hydration.")
        return
        
    print(f"📡 Found Vorticity node: {vort_id}")
    print(f"📡 Found Fenchel node: {fenchel_id}")
    
    # 2. Run SHORTEST_PATH
    interrogation_query = """
    FOR path IN OUTBOUND SHORTEST_PATH 
        @vort_id TO @fenchel_id 
        ig_edges
        RETURN {
            nodes: path.vertices[*].name,
            types: path.vertices[*].type,
            edges: path.edges[*].dependency_type
        }
    """
    results_raw = query_arango(interrogation_query, {"vort_id": vort_id, "fenchel_id": fenchel_id})
    results = results_raw.get("result", []) if results_raw else []
    
    if not results:
        # Try INBOUND if OUTBOUND is empty
        interrogation_query_in = """
        FOR path IN INBOUND SHORTEST_PATH 
            @vort_id TO @fenchel_id 
            ig_edges
            RETURN {
                nodes: path.vertices[*].name,
                types: path.vertices[*].type,
                edges: path.edges[*].dependency_type
            }
        """
        results_raw = query_arango(interrogation_query_in, {"vort_id": vort_id, "fenchel_id": fenchel_id})
        results = results_raw.get("result", []) if results_raw else []
        
    if not results or not results[0].get('nodes'):
        # Broaden search to general outbound paths
        traverse_query = """
        FOR v, e, p IN 1..10 OUTBOUND @vort_id ig_edges
          FILTER CONTAINS(v.name, "fenchelGap") || CONTAINS(v.name, "Bregman")
          LIMIT 1
          RETURN {
              nodes: p.vertices[*].name,
              edges: p.edges[*].dependency_type
          }
        """
        results_raw = query_arango(traverse_query, {"vort_id": vort_id})
        results = results_raw.get("result", []) if results_raw else []

    if not results:
        print("⚡ The spine is disconnected or hidden. Check graph hydration.")
        return
        
    print("\n═ PHYSICAL SPINE LOCATED ══════════════════════════════════════════")
    node_chain = results[0].get('nodes', [])
    edge_types = results[0].get('edges', [])
    
    for i in range(len(node_chain)):
        print(f" [{i+1}] {node_chain[i]}")
        if i < len(edge_types):
            print(f"      │ ({edge_types[i]})")
            print(f"      ▼")
    print("══════════════════════════════════════════════════════════════════")

if __name__ == "__main__":
    interrogate_causal_chain()
