import json
import os
import subprocess

def build_shapehash_bridge():
    print("=== Building ShapeHash-to-Lean Bridge ===")
    os.makedirs("handover/injections", exist_ok=True)
    
    # 1. Query the top-N clusters from ArangoDB (8530)
    aql_query = """
    FOR doc IN dag_nodes
      FILTER doc.valueFingerprint != null AND doc.valueFingerprint != ''
      COLLECT fingerprint = doc.valueFingerprint INTO group
      LET count = LENGTH(group)
      FILTER count > 1
      SORT count DESC
      LIMIT 3
      RETURN {
        shapeHash: fingerprint.shapeHash,
        count: count,
        canonical_node: FIRST(group).doc,
        all_nodes: (FOR g IN group LIMIT 5 RETURN g.doc.name)
      }
    """
    
    print("Querying Top Clusters from ArangoDB...")
    query_cmd = [
        "python3", "tools/leantrail/aql_query.py",
        "--password", "alexandria_root",
        "--endpoint", "http://127.0.0.1:8530",
        "--database", "infogeometry",
        aql_query
    ]
    
    result = subprocess.run(query_cmd, capture_output=True, text=True)
    if result.returncode != 0 or not result.stdout.strip():
        print("Failed to execute AQL query or no results returned.")
        # Fallback to the known JSON if database is slow
        if os.path.exists("scratch/duplicate_hashes.json"):
            with open("scratch/duplicate_hashes.json", "r") as f:
                clusters = json.load(f)
                # Mock the canonical node structure based on known data
                for c in clusters:
                    c['canonical_node'] = {'name': c['nodes'][0]['name']}
                    c['shapeHash'] = c['hash']['shapeHash']
        else:
            return
    else:
        try:
            clusters = json.loads(result.stdout)
        except:
            print("Could not parse JSON. Raw output:")
            print(result.stdout)
            return

    # 2 & 3 & 4. For each cluster, extract canonical node and generate a Lean unified lemma
    for idx, cluster in enumerate(clusters):
        shape_hash = cluster.get('shapeHash')
        count = cluster.get('count')
        canonical_name = cluster['canonical_node'].get('name', 'UnknownNode')
        
        bridge_file = f"handover/injections/Unified_Shape_{shape_hash}.lean"
        
        print(f"Cluster {idx+1}: ShapeHash {shape_hash} ({count} duplicates)")
        print(f"Canonical Source: {canonical_name}")
        
        lean_code = f"""import Mathlib

/-!
# Unified ShapeHash Closure: {shape_hash}
This file records a structural duplication cluster with {count} members.
Canonical origin: {canonical_name}

Policy:
- do not emit vacuous bridge theorems of the form `: True := by trivial`;
- do not treat structural shape equivalence as a mathematical proof;
- recover the real predicate from the canonical owner file;
- add genuine projection/use lemmas;
- prove constructively or leave explicit `sorry` debt.

This file is therefore an honest scaffold only. No theorem is auto-generated
from shape-hash data alone.
-/

namespace InfoGeometry.Unified.{shape_hash}

/-
TODO(owner-directed repair):
1. read the canonical owner theorem/structure at `{canonical_name}`;
2. identify the hidden mathematical predicate behind `_True`/`_sorry`/certificate fields;
3. restate that predicate explicitly here or in the owner file;
4. add projection lemmas and use lemmas;
5. prove the result constructively, or keep `sorry`.
-/

end InfoGeometry.Unified.{shape_hash}
"""
        with open(bridge_file, "w") as f:
            f.write(lean_code)
            
        print(f"--> Emitted proposal: {bridge_file}\n")
        
    print("Bridge generation complete! GEPA substrate is ready.")

if __name__ == '__main__':
    build_shapehash_bridge()
