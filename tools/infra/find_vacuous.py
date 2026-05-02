#!/usr/bin/env python3
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SRC_ROOT = REPO_ROOT / "src"
for path in (REPO_ROOT, SRC_ROOT):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from igf.graph import ArangoHttpTarget, execute_aql


def run_aql(query, bind_vars=None):
    load_repo_arango_env()
    target = ArangoHttpTarget(
        endpoint=arango_endpoint().rstrip("/"),
        database=arango_database(),
        username=arango_username(),
        password=arango_password("alexandria_root"),
    )
    return execute_aql(target, query, bind_vars or {})

def main():
    # Attempt 1: Check for explicit vacuous or surrogate flags in ig_nodes or components
    print("Finding vacuous theorems in ArangoDB...")
    
    # Let's search ig_nodes for 'trivial' in the value or name, or if it has a 'vacuous' attribute
    # Since the exact schema of 'vacuous' isn't known, we'll try a few heuristics.
    
    query = """
    FOR doc IN ig_nodes
      FILTER doc.is_prop == true
      FILTER doc.value LIKE "%trivial%" OR doc.value LIKE "%True%" OR doc.name LIKE "%vacuous%"
      RETURN { name: doc.name, value: doc.value, kind: doc.kind }
    """
    
    try:
        results = run_aql(query)
        print(f"Found {len(results)} potentially vacuous theorems via AQL:")
        for r in results:
            print(f"- {r['name']}")
    except Exception as e:
        print(f"Error querying Arango: {e}")
        
    print("\nChecking canonical policy lint output for 'trivial_proof'...")
    try:
        with open("reports/dag/policy-lint-report.json") as f:
            lint_data = json.load(f)
            vacuous = [v for v in lint_data.get("violations", []) if "trivial" in v.get("reason", "")]
            print(f"Found {len(vacuous)} trivial/vacuous theorems in lint report:")
            for v in vacuous:
                print(f"- {v['name']} ({v['reason']})")
    except Exception as e:
        print(f"Could not read lint report: {e}")

if __name__ == "__main__":
    main()
