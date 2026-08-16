#!/usr/bin/env python3
"""Verify raw_infotree_* descent invariants in ArangoDB.

This verifier is intentionally non-mutating. It checks that the stage
``raw_infotree_*`` projection imported by ``arango_raw_infotree_ingest.py`` is
referentially closed and navigable:

* tree edges point to real InfoTree nodes,
* row tables descend through the expected edge collections,
* lctx references descend from nodes or mctx decls,
* lctx declaration rows descend from lctx references,
* leakage rows remain attached to their source node,
* tactic payloads retain before/after mctx state references.

It does not prove full compiler losslessness. Projection leakage remains the
explicit witness for compiler state that is not yet structurally serialized.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.arango_raw_infotree_ingest import (
    EDGE_COLLECTIONS,
    ROW_FILES,
    ArangoTarget,
    collection_count,
    db_url,
    list_collections,
    request_json,
)


@dataclass(frozen=True)
class QueryCheck:
    name: str
    query: str
    expect_empty: bool = True


def run_aql(target: ArangoTarget, query: str, bind_vars: dict[str, Any] | None = None) -> list[Any]:
    payload = {
        "query": query,
        "bindVars": bind_vars or {},
        "batchSize": 1000,
        "count": True,
    }
    result = request_json(
        "POST",
        db_url(target, "/_api/cursor"),
        username=target.username,
        password=target.password,
        payload=payload,
    )
    if not isinstance(result, dict):
        raise RuntimeError(f"AQL cursor returned non-object payload: {result!r}")
    rows = result.get("result")
    if not isinstance(rows, list):
        raise RuntimeError(f"AQL cursor returned invalid result rows: {result!r}")
    return rows


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def structural_checks() -> list[QueryCheck]:
    return [
        QueryCheck(
            name="tree_edges_reference_existing_nodes",
            query="""
FOR e IN raw_infotree_tree_edges
  LET fromDoc = DOCUMENT(e._from)
  LET toDoc = DOCUMENT(e._to)
  FILTER fromDoc == null OR toDoc == null
  LIMIT 20
  RETURN { edge: e, missingFrom: fromDoc == null, missingTo: toDoc == null }
""",
        ),
        QueryCheck(
            name="root_node_edges_reference_existing_roots_and_nodes",
            query="""
FOR e IN raw_infotree_root_node_edges
  LET fromDoc = DOCUMENT(e._from)
  LET toDoc = DOCUMENT(e._to)
  FILTER fromDoc == null OR toDoc == null
  LIMIT 20
  RETURN { edge: e, missingRoot: fromDoc == null, missingNode: toDoc == null }
""",
        ),
        QueryCheck(
            name="node_payload_rows_have_edges",
            query="""
FOR p IN raw_infotree_payloads
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_node_payload_edges
      FILTER e._from == CONCAT("raw_infotree_nodes/", p.nodeKey)
      FILTER e._to == CONCAT("raw_infotree_payloads/", p._key)
      RETURN 1
  )
  FILTER edgeCount == 0
  LIMIT 20
  RETURN p
""",
        ),
        QueryCheck(
            name="payload_field_rows_have_edges",
            query="""
FOR f IN raw_infotree_payload_fields
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_payload_field_edges
      FILTER e._from == CONCAT("raw_infotree_payloads/", f.payloadKey)
      FILTER e._to == CONCAT("raw_infotree_payload_fields/", f._key)
      RETURN 1
  )
  FILTER edgeCount == 0
  LIMIT 20
  RETURN f
""",
        ),
        QueryCheck(
            name="context_rows_have_node_edges",
            query="""
FOR c IN raw_infotree_contexts
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_node_context_edges
      FILTER e._from == CONCAT("raw_infotree_nodes/", c.nodeKey)
      FILTER e._to == CONCAT("raw_infotree_contexts/", c._key)
      RETURN 1
  )
  FILTER edgeCount == 0
  LIMIT 20
  RETURN c
""",
        ),
        QueryCheck(
            name="decl_link_rows_have_node_edges",
            query="""
FOR d IN raw_infotree_decl_links
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_node_decl_link_edges
      FILTER e._from == CONCAT("raw_infotree_nodes/", d.nodeKey)
      FILTER e._to == CONCAT("raw_infotree_decl_links/", d._key)
      RETURN 1
  )
  FILTER edgeCount == 0
  LIMIT 20
  RETURN d
""",
        ),
        QueryCheck(
            name="decl_link_declname_join_to_ig_decl_nodes_nonempty",
            query="""
FOR d IN raw_infotree_decl_links
  FILTER d.declName != null
  FILTER d.declName != ""
  FILTER CONTAINS(d.declName, ".")
  FILTER d.declName != SUBSTITUTE(d.module, "lean.", "")
  LET matches = (
    FOR n IN ig_nodes
      FILTER n.name == d.declName
      LIMIT 1
      RETURN n._id
  )
  FILTER LENGTH(matches) == 0
  LIMIT 20
  RETURN { declLink: d._key, declName: d.declName }
""",
        ),
        QueryCheck(
            name="decl_link_declname_join_to_ig_decl_nodes_unique",
            query="""
FOR d IN raw_infotree_decl_links
  FILTER d.declName != null
  FILTER d.declName != ""
  FILTER CONTAINS(d.declName, ".")
  FILTER d.declName != SUBSTITUTE(d.module, "lean.", "")
  LET matches = (
    FOR n IN ig_nodes
      FILTER n.name == d.declName
      RETURN n._id
  )
  FILTER LENGTH(matches) > 1
  LIMIT 20
  RETURN { declLink: d._key, declName: d.declName, matchCount: LENGTH(matches) }
""",
        ),
        QueryCheck(
            name="tactic_argument_declname_join_to_ig_decl_nodes_nonempty",
            query="""
FOR a IN raw_infotree_tactic_arguments
  FILTER a.declName != null
  FILTER a.declName != ""
  FILTER CONTAINS(a.declName, ".")
  FILTER a.declName != SUBSTITUTE(a.module, "lean.", "")
  LET matches = (
    FOR n IN ig_nodes
      FILTER n.name == a.declName
      LIMIT 1
      RETURN n._id
  )
  FILTER LENGTH(matches) == 0
  LIMIT 20
  RETURN { argumentKey: a.argumentKey, declName: a.declName }
""",
        ),
        QueryCheck(
            name="env_ref_rows_have_node_edges",
            query="""
FOR r IN raw_infotree_env_refs
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_node_env_ref_edges
      FILTER e._from == CONCAT("raw_infotree_nodes/", r.nodeKey)
      FILTER e._to == CONCAT("raw_infotree_env_refs/", r._key)
      RETURN 1
  )
  FILTER edgeCount == 0
  LIMIT 20
  RETURN r
""",
        ),
        QueryCheck(
            name="mctx_ref_rows_have_node_edges",
            query="""
FOR r IN raw_infotree_mctx_refs
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_node_mctx_ref_edges
      FILTER e._from == CONCAT("raw_infotree_nodes/", r.nodeKey)
      FILTER e._to == CONCAT("raw_infotree_mctx_refs/", r._key)
      RETURN 1
  )
  FILTER edgeCount == 0
  LIMIT 20
  RETURN r
""",
        ),
        QueryCheck(
            name="mctx_decl_rows_have_mctx_ref_edges",
            query="""
FOR d IN raw_infotree_mctx_decls
  LET refCount = LENGTH(
    FOR r IN raw_infotree_mctx_refs
      FILTER r.mctxKey == d.mctxKey
      RETURN 1
  )
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_mctx_decl_edges
      FILTER e.mctxKey == d.mctxKey
      FILTER e._to == CONCAT("raw_infotree_mctx_decls/", d._key)
      RETURN 1
  )
  FILTER refCount == 0 OR edgeCount != refCount
  LIMIT 20
  RETURN { decl: d, refCount: refCount, edgeCount: edgeCount }
""",
        ),
        QueryCheck(
            name="mctx_lctx_refs_descend_from_mctx_decl",
            query="""
FOR r IN raw_infotree_lctx_refs
  FILTER r.sourceKind == "mctx_decl"
  LET sourceDoc = DOCUMENT(CONCAT("raw_infotree_mctx_decls/", r.sourceKey))
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_source_lctx_ref_edges
      FILTER e._from == CONCAT("raw_infotree_mctx_decls/", r.sourceKey)
      FILTER e._to == CONCAT("raw_infotree_lctx_refs/", r._key)
      RETURN 1
  )
  FILTER sourceDoc == null OR edgeCount == 0
  LIMIT 20
  RETURN { lctxRef: r, missingSource: sourceDoc == null, missingEdge: edgeCount == 0 }
""",
        ),
        QueryCheck(
            name="node_lctx_refs_descend_from_node",
            query="""
FOR r IN raw_infotree_lctx_refs
  FILTER r.sourceKind != "mctx_decl"
  LET sourceDoc = DOCUMENT(CONCAT("raw_infotree_nodes/", r.nodeKey))
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_source_lctx_ref_edges
      FILTER e._from == CONCAT("raw_infotree_nodes/", r.nodeKey)
      FILTER e._to == CONCAT("raw_infotree_lctx_refs/", r._key)
      RETURN 1
  )
  FILTER sourceDoc == null OR edgeCount == 0
  LIMIT 20
  RETURN { lctxRef: r, missingSource: sourceDoc == null, missingEdge: edgeCount == 0 }
""",
        ),
        QueryCheck(
            name="lctx_refs_descend_to_decl_rows",
            query="""
FOR r IN raw_infotree_lctx_refs
  FILTER r.lctxSize > 0
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_lctx_ref_decl_edges
      FILTER e._from == CONCAT("raw_infotree_lctx_refs/", r._key)
      RETURN 1
  )
  FILTER edgeCount != r.lctxSize
  LIMIT 20
  RETURN { lctxRef: r, expectedDecls: r.lctxSize, edgeCount: edgeCount }
""",
        ),
        QueryCheck(
            name="leakage_rows_have_node_edges",
            query="""
FOR l IN raw_infotree_projection_leakage
  FILTER HAS(l, "nodeKey") AND l.nodeKey != null
  LET sourceDoc = DOCUMENT(CONCAT("raw_infotree_nodes/", l.nodeKey))
  LET edgeCount = LENGTH(
    FOR e IN raw_infotree_node_leakage_edges
      FILTER e._from == CONCAT("raw_infotree_nodes/", l.nodeKey)
      FILTER e._to == CONCAT("raw_infotree_projection_leakage/", l._key)
      RETURN 1
  )
  FILTER sourceDoc == null OR edgeCount == 0
  LIMIT 20
  RETURN { leakage: l, missingSource: sourceDoc == null, missingEdge: edgeCount == 0 }
""",
        ),
    ]


def count_report(target: ArangoTarget, ingest_report: dict[str, Any] | None) -> dict[str, Any]:
    collections = [*ROW_FILES.keys(), *EDGE_COLLECTIONS, "ig_nodes"]
    existing = list_collections(target)
    missing_collections = sorted(set(collections) - existing)
    live = {
        name: collection_count(target, name) if name in existing else None
        for name in collections
    }
    expected: dict[str, int] = {}
    if ingest_report is not None:
        for section in ("row_counts", "edge_counts"):
            rows = ingest_report.get(section)
            if isinstance(rows, dict):
                for key, value in rows.items():
                    if isinstance(value, int):
                        expected[str(key)] = value
    mismatches = {
        name: {"expected": expected[name], "live": live.get(name)}
        for name in sorted(expected)
        if live.get(name) != expected[name]
    }
    return {
        "live": live,
        "expected": expected,
        "missing_collections": missing_collections,
        "mismatches": mismatches,
        "ok": not missing_collections and not mismatches and all(isinstance(value, int) and value >= 0 for value in live.values()),
    }


def leakage_report(target: ArangoTarget) -> dict[str, Any]:
    rows = run_aql(
        target,
        """
FOR l IN raw_infotree_projection_leakage
  COLLECT field = l.field WITH COUNT INTO count
  SORT count DESC, field ASC
  RETURN { field: field, count: count }
""",
    )
    return {
        "total": sum(row.get("count", 0) for row in rows if isinstance(row, dict)),
        "by_field": rows,
    }


def tactic_report(target: ArangoTarget) -> dict[str, Any]:
    rows = run_aql(
        target,
        """
LET tacticPayloads = (
  FOR p IN raw_infotree_payloads
    FILTER p.kind == "tactic"
    RETURN p
)
LET withBefore = (
  FOR p IN tacticPayloads
    LET refs = (
      FOR e IN raw_infotree_node_mctx_ref_edges
        FILTER e._from == CONCAT("raw_infotree_nodes/", p.nodeKey)
        LET ref = DOCUMENT(e._to)
        FILTER ref != null AND CONTAINS(ref._key, "tacticBefore")
        RETURN ref
    )
    FILTER LENGTH(refs) > 0
    RETURN p._key
)
LET withAfter = (
  FOR p IN tacticPayloads
    LET refs = (
      FOR e IN raw_infotree_node_mctx_ref_edges
        FILTER e._from == CONCAT("raw_infotree_nodes/", p.nodeKey)
        LET ref = DOCUMENT(e._to)
        FILTER ref != null AND CONTAINS(ref._key, "tacticAfter")
        RETURN ref
    )
    FILTER LENGTH(refs) > 0
    RETURN p._key
)
LET missingBefore = MINUS(tacticPayloads[*]._key, withBefore)
LET missingAfter = MINUS(tacticPayloads[*]._key, withAfter)
RETURN {
  tacticPayloadCount: LENGTH(tacticPayloads),
  withBefore: LENGTH(withBefore),
  withAfter: LENGTH(withAfter),
  missingBefore: SLICE(missingBefore, 0, 20),
  missingAfter: SLICE(missingAfter, 0, 20)
}
""",
    )
    report = rows[0] if rows and isinstance(rows[0], dict) else {}
    tactic_count = report.get("tacticPayloadCount")
    if not isinstance(tactic_count, int):
        tactic_count = 0
    before = report.get("withBefore")
    after = report.get("withAfter")
    skipped = tactic_count == 0
    ok = skipped or (before == tactic_count and after == tactic_count)
    return {**report, "ok": ok, "skipped": skipped}


def run_checks(target: ArangoTarget) -> dict[str, Any]:
    reports: dict[str, Any] = {}
    for check in structural_checks():
        rows = run_aql(target, check.query)
        ok = len(rows) == 0 if check.expect_empty else len(rows) > 0
        reports[check.name] = {
            "ok": ok,
            "sample_count": len(rows),
            "samples": rows,
        }
    return reports


def parse_args() -> argparse.Namespace:
    load_repo_arango_env(REPO_ROOT)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password())
    parser.add_argument("--ingest-report", type=Path)
    parser.add_argument("--json-out", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    target = ArangoTarget(
        endpoint=str(args.endpoint).rstrip("/"),
        database=str(args.database),
        username=str(args.username),
        password=str(args.password),
    )
    ingest_report = load_json(args.ingest_report)
    counts = count_report(target, ingest_report)
    if counts["missing_collections"]:
        checks: dict[str, Any] = {}
        tactic: dict[str, Any] = {
            "ok": False,
            "skipped": True,
            "reason": "missing required collections for descent/join checks",
        }
        leakage: dict[str, Any] = {
            "total": None,
            "by_field": [],
            "skipped": True,
            "reason": "missing required collections for descent/join checks",
        }
    else:
        checks = run_checks(target)
        tactic = tactic_report(target)
        leakage = leakage_report(target)

    check_failures = [name for name, report in checks.items() if not report.get("ok")]
    ok = counts["ok"] and not check_failures and tactic["ok"]
    report = {
        "schema": "info_geometry.raw_infotree_arango_descent_verification.v1",
        "database": target.database,
        "ok": ok,
        "counts_ok": counts["ok"],
        "counts": counts,
        "checks": checks,
        "check_failures": check_failures,
        "tactic_state_descent": tactic,
        "leakage": leakage,
    }

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, ensure_ascii=True))
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
