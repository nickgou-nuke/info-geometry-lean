#!/usr/bin/env python3
"""Verify raw-to-overlay-to-raw descent in the layered Arango graph."""

from __future__ import annotations

import argparse
import base64
import json
from typing import Any
from urllib.request import Request, urlopen


def auth_header(username: str, password: str) -> str:
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"


def aql(args: argparse.Namespace, query: str, bind_vars: dict[str, Any] | None = None) -> list[Any]:
    url = f"{args.endpoint.rstrip('/')}/_db/{args.database}/_api/cursor"
    req = Request(
        url,
        data=json.dumps({"query": query, "bindVars": bind_vars or {}}).encode("utf-8"),
        method="POST",
    )
    req.add_header("Authorization", auth_header(args.username, args.password))
    req.add_header("Content-Type", "application/json")
    req.add_header("Accept", "application/json")
    with urlopen(req, timeout=30) as response:
        payload = json.loads(response.read().decode("utf-8"))
    return payload.get("result", [])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default="http://127.0.0.1:8529")
    parser.add_argument("--database", default="infogeometry")
    parser.add_argument("--username", default="root")
    parser.add_argument("--password", default="")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    raw_edges = aql(
        args,
        """
        FOR e IN raw_info_edges
          FILTER e.role == "raw_dependency"
          LIMIT 1
          RETURN e
        """,
    )
    if not raw_edges:
        raise SystemExit("no raw_info_edges rows found")
    edge = raw_edges[0]

    memberships = aql(
        args,
        """
        FOR m IN topology_overlay_edges
          FILTER m.role == "member_of_scc" && m._from == @from
          LIMIT 1
          RETURN m
        """,
        {"from": edge["_from"]},
    )
    if not memberships:
        raise SystemExit(f"missing member_of_scc edge for {edge['_from']}")
    membership = memberships[0]

    quotients = aql(
        args,
        """
        FOR q IN topology_overlay_edges
          FILTER q.role == "scc_quotient"
          FILTER q.src_scc == @src_scc && q.dst_scc == @dst_scc && q.kind == @kind
          LIMIT 1
          RETURN q
        """,
        {"src_scc": edge["src_scc"], "dst_scc": edge["dst_scc"], "kind": edge["kind"]},
    )
    if not quotients:
        raise SystemExit(
            "missing scc_quotient edge for "
            f"src_scc={edge['src_scc']} dst_scc={edge['dst_scc']} kind={edge['kind']}"
        )
    quotient = quotients[0]

    witness_counts = aql(
        args,
        """
        FOR e IN raw_info_edges
          FILTER e.src_scc == @src_scc && e.dst_scc == @dst_scc && e.kind == @kind
          COLLECT WITH COUNT INTO n
          RETURN n
        """,
        {"src_scc": edge["src_scc"], "dst_scc": edge["dst_scc"], "kind": edge["kind"]},
    )
    witness_count = int(witness_counts[0])
    ok = witness_count == int(quotient["multiplicity"])

    report = {
        "schema": "info_geometry.layered_arango_descent_check.v1",
        "ok": ok,
        "raw_edge_key": edge["_key"],
        "raw_edge_from": edge["_from"],
        "raw_edge_to": edge["_to"],
        "member_of_scc_edge": membership["_key"],
        "member_of_scc_to": membership["_to"],
        "quotient_edge": quotient["_key"],
        "quotient_multiplicity": quotient["multiplicity"],
        "raw_witness_query_count": witness_count,
        "witness_count_matches_multiplicity": ok,
    }
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True))
    else:
        print(
            "LAYERED_ARANGO_DESCENT_OK"
            if ok
            else "LAYERED_ARANGO_DESCENT_FAILED",
            report["raw_edge_key"],
            report["member_of_scc_edge"],
            report["quotient_edge"],
            f"witnesses={witness_count}",
        )
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
