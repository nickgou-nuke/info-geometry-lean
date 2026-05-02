#!/usr/bin/env python3
import os, json, base64
from urllib.request import Request, urlopen
from urllib.error import HTTPError

def request_json(method, url, payload=None):
    endpoint = os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8530").rstrip("/")
    user = os.environ.get("ARANGO_USER") or os.environ.get("ARANGO_USERNAME", "root")
    password = os.environ.get("ARANGO_PASS") or os.environ.get("ARANGO_PASSWORD", "alexandria_root")
    token = base64.b64encode(f"{user}:{password}".encode()).decode("ascii")

    body = None if payload is None else json.dumps(payload).encode("utf-8")
    req = Request(url, data=body, method=method)
    req.add_header("Authorization", "Basic " + token)
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urlopen(req) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except HTTPError as exc:
        raise RuntimeError(f"HTTP {exc.code} {url}: {exc.read().decode('utf-8')}")

def run_aql(query, bind_vars=None):
    url = "http://127.0.0.1:8530/_db/infogeometry/_api/cursor"
    payload = {"query": query, "bindVars": bind_vars or {}}
    return request_json("POST", url, payload=payload).get("result", [])

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
