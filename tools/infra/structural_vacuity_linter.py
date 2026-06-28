import json
import os
import subprocess

def run_vacuity_linter():
    print("=== ArangoDB Structural Vacuity Linter ===")
    
    # We query the DAG for any shapeHashes that contain known "cheat" nodes
    # (e.g. ending in _True, _sorryProof, or containing 'sorry').
    # Then we flag ALL nodes sharing that exact mathematical structure as vacuous!
    
    aql_query = """
    FOR doc IN dag_nodes
      FILTER doc.valueFingerprint != null AND doc.valueFingerprint != ''
      COLLECT fingerprint = doc.valueFingerprint INTO group
      LET nodes = (FOR g IN group RETURN g.doc.name)
      
      // Identify if this cluster contains a known vacuous cheat
      LET has_cheat = (
        FOR n IN nodes 
        FILTER LIKE(n, "%_True") OR LIKE(n, "%_sorryProof") OR LIKE(n, "%sorry%") 
        LIMIT 1 
        RETURN true
      )
      
      // We only care about clusters that have a cheat
      FILTER LENGTH(has_cheat) > 0
      
      // Return the entire cluster so we can expose the hidden cheats
      RETURN {
        shapeHash: fingerprint.shapeHash,
        total_nodes: LENGTH(nodes),
        all_nodes: nodes
      }
    """
    
    print("Scanning codebase AST for structural vacuity...")
    query_cmd = [
        "python3", "tools/leantrail/aql_query.py",
        "--password", "alexandria_root",
        "--endpoint", "http://127.0.0.1:8530",
        "--database", "infogeometry",
        aql_query
    ]
    
    result = subprocess.run(query_cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print("AQL query failed.")
        return

    try:
        vacuous_clusters = json.loads(result.stdout)
    except:
        print("Failed to parse AQL output.")
        return

    total_vacuous_nodes = sum(c['total_nodes'] for c in vacuous_clusters)
    print(f"Found {len(vacuous_clusters)} vacuous structural shapes.")
    print(f"Total structurally vacuous theorems flagged: {total_vacuous_nodes}\n")
    
    # Save the report
    report_file = "reports/structural_vacuity_report.json"
    os.makedirs("reports", exist_ok=True)
    
    with open(report_file, "w") as f:
        json.dump(vacuous_clusters, f, indent=2)
        
    print(f"✅ Vacuity Linter complete! Report saved to {report_file}")
    
    # Print a few examples of "hidden" vacuity where a normal-looking theorem 
    # shares a shapeHash with a cheat.
    print("\n[ALERT] Hidden Vacuity Examples (Normal names hiding a cheat structure):")
    hidden_count = 0
    for cluster in vacuous_clusters:
        cheats = [n for n in cluster['all_nodes'] if "_True" in n or "sorry" in n.lower()]
        normal = [n for n in cluster['all_nodes'] if n not in cheats]
        
        if len(normal) > 0 and len(cheats) > 0:
            print(f" - Shape {cluster['shapeHash']} is vacuous (based on {cheats[0]})")
            print(f"   => FLAG: {normal[0]} is a hidden cheat!")
            hidden_count += 1
            if hidden_count >= 5:
                break

if __name__ == '__main__':
    run_vacuity_linter()
