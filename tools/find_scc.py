from __future__ import annotations

import base64
import json
import os
from urllib.request import Request, urlopen


def query(aql: str, bind_vars: dict | None = None) -> dict:
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
    with urlopen(req) as resp:
        return json.loads(resp.read().decode("utf-8"))


def main() -> int:
    res = query("""
FOR node IN ig_nodes
  FILTER node.name == "InfoGeometry.Canonical.AnomalyGauge.commutator_is_skew_adjoint"
  LET scc = (FOR e IN topology_overlay_edges FILTER e._from == node._id AND e.role == "member_of_scc" RETURN e._to)[0]
  RETURN { id: node._id, name: node.name, scc: scc }
""")
    print("Target node and SCC:", json.dumps(res.get("result", []), indent=2))

    if res.get("result"):
        scc_id = res["result"][0]["scc"]
        res_members = query("""
FOR e IN topology_overlay_edges
  FILTER e._to == @scc_id AND e.role == "member_of_scc"
  FOR node IN ig_nodes
    FILTER node._id == e._from
    RETURN node.name
""", {"scc_id": scc_id})
        print("SCC Members:", json.dumps(res_members.get("result", []), indent=2))

        res_deps = query("""
FOR v, e, p IN 1..1 OUTBOUND @scc_id arango_dag_component_edges
  RETURN v.representative
""", {"scc_id": scc_id})
        print("SCC Dependencies:", json.dumps(res_deps.get("result", []), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
