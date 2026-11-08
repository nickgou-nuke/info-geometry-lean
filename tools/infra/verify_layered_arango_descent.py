#!/usr/bin/env python3
"""Verify raw-to-overlay-to-raw descent in the layered Arango graph."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

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


def aql(args: argparse.Namespace, query: str, bind_vars: dict[str, Any] | None = None) -> list[Any]:
    target = ArangoHttpTarget(
        endpoint=args.endpoint.rstrip("/"),
        database=args.database,
        username=args.username,
        password=args.password,
    )
    return execute_aql(target, query, bind_vars, timeout=30)


def main() -> int:
    load_repo_arango_env()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password())
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
    target_memberships = aql(
        args,
        """
        FOR m IN topology_overlay_edges
          FILTER m.role == "member_of_scc" && m._from == @to
          LIMIT 1
          RETURN m
        """,
        {"to": edge["_to"]},
    )
    if not target_memberships:
        raise SystemExit(f"missing member_of_scc edge for {edge['_to']}")
    target_membership = target_memberships[0]
    src_scc = int(membership["scc_id"])
    dst_scc = int(target_membership["scc_id"])

    quotients = aql(
        args,
        """
        FOR q IN topology_overlay_edges
          FILTER q.role == "scc_quotient"
          FILTER q.src_scc == @src_scc && q.dst_scc == @dst_scc && q.kind == @kind
          LIMIT 1
          RETURN q
        """,
        {"src_scc": src_scc, "dst_scc": dst_scc, "kind": edge["kind"]},
    )
    if not quotients:
        raise SystemExit(
            "missing scc_quotient edge for "
            f"src_scc={src_scc} dst_scc={dst_scc} kind={edge['kind']}"
        )
    quotient = quotients[0]

    witness_counts = aql(
        args,
        """
        FOR e IN raw_info_edges
          FILTER e.role == "raw_dependency" && e.kind == @kind
          LET fm = FIRST(
            FOR m IN topology_overlay_edges
              FILTER m.role == "member_of_scc" && m._from == e._from
              RETURN m
          )
          LET tm = FIRST(
            FOR m IN topology_overlay_edges
              FILTER m.role == "member_of_scc" && m._from == e._to
              RETURN m
          )
          FILTER fm != null && tm != null
          FILTER TO_NUMBER(fm.scc_id) == @src_scc && TO_NUMBER(tm.scc_id) == @dst_scc
          COLLECT WITH COUNT INTO n
          RETURN n
        """,
        {"src_scc": src_scc, "dst_scc": dst_scc, "kind": edge["kind"]},
    )
    witness_count = int(witness_counts[0])
    ok = witness_count == int(quotient["multiplicity"])

    report = {
        "schema": "info_geometry.layered_arango_descent_check.v1",
        "ok": ok,
        "raw_edge_key": edge["_key"],
        "raw_edge_from": edge["_from"],
        "raw_edge_to": edge["_to"],
        "src_scc": src_scc,
        "dst_scc": dst_scc,
        "member_of_scc_edge": membership["_key"],
        "member_of_scc_to": membership["_to"],
        "target_member_of_scc_edge": target_membership["_key"],
        "target_member_of_scc_to": target_membership["_to"],
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
