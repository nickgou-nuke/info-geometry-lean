import os, json, base64
from urllib.request import Request, urlopen

def query(aql, bind_vars=None):
    endpoint = os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8530").rstrip("/")
    db = os.environ.get("ARANGO_DATABASE", "infogeometry")
    user = os.environ.get("ARANGO_USER") or os.environ.get("ARANGO_USERNAME", "root")
    password = os.environ.get("ARANGO_PASS") or os.environ.get("ARANGO_PASSWORD", "alexandria_root")
    
    token = base64.b64encode(f"{user}:{password}".encode()).decode("ascii")
    url = f"{endpoint}/_db/{db}/_api/cursor"
    payload = {"query": aql, "bindVars": bind_vars or {}}
    req = Request(url, data=json.dumps(payload).encode("utf-8"), method="POST")
    req.add_header("Authorization", f"Basic {token}")
    req.add_header("Content-Type", "application/json")
    try:
        with urlopen(req) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        return None

res = query("""
FOR edge IN topology_overlay_edges
  FILTER edge._from == 'ig_nodes/InfoGeometry.Canonical.DimensionAgnosticModularKLDivergence.generalizedKL_scale_shape_split'
  RETURN edge
""")
print("Edges for node:", json.dumps(res.get("result", []), indent=2))
