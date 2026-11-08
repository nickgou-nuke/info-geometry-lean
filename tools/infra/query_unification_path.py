#!/usr/bin/env python3
"""Query the dependency path from Fenchel-Legendre to Vorticity."""

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

def main():
    print("=== Querying Unification Path from Fenchel-Legendre to Vorticity ===")
    
    # 1. Dynamically locate the source and target node IDs
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
        print(f"Error: Could not locate required nodes. Vorticity: {vort_id}, Fenchel: {fenchel_id}")
        return
        
    print(f"Located Vorticity node: {vort_id}")
    print(f"Located Fenchel node: {fenchel_id}")
    
    # 2. Query shortest path dynamically
    path_query = """
    FOR v, e IN OUTBOUND SHORTEST_PATH
      @vort_id TO @fenchel_id
      ig_edges
      RETURN {name: v.name, module: v.module, kind: v.kind}
    """
    path_results = query_arango(path_query, {"vort_id": vort_id, "fenchel_id": fenchel_id})
    
    path = path_results.get("result", []) if path_results else []
    
    if not path:
        # Try INBOUND if OUTBOUND is empty
        path_query_in = """
        FOR v, e IN INBOUND SHORTEST_PATH
          @vort_id TO @fenchel_id
          ig_edges
          RETURN {name: v.name, module: v.module, kind: v.kind}
        """
        path_results = query_arango(path_query_in, {"vort_id": vort_id, "fenchel_id": fenchel_id})
        path = path_results.get("result", []) if path_results else []
        
    if not path:
        print("\nNo direct shortest path found. Querying general traversal...")
        traverse_query = """
        FOR v, e, p IN 1..10 OUTBOUND @vort_id ig_edges
          FILTER CONTAINS(v.name, "fenchelGap") || CONTAINS(v.name, "Bregman")
          LIMIT 1
          RETURN p.vertices[* RETURN {name: CURRENT.name, module: CURRENT.module}]
        """
        traverse_results = query_arango(traverse_query, {"vort_id": vort_id})
        res = traverse_results.get("result", []) if traverse_results else []
        path = res[0] if res else []
        
    print("\nDependency Path:")
    if path:
        for idx, step in enumerate(path):
            print(f"  [{idx}] Module: {step.get('module', '')} | Name: {step.get('name', '')}")
            
        out_dir = "/tmp/multi_engine_results"
        os.makedirs(out_dir, exist_ok=True)
        out_path = os.path.join(out_dir, "unification_path.json")
        with open(out_path, "w") as f:
            json.dump(path, f, indent=2)
        print(f"\nPath successfully exported to {out_path}!")
    else:
        print("  No dependency path found between the nodes.")

if __name__ == "__main__":
    main()
