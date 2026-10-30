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
import re
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


def remap_query(query: str, collections: dict[str, str]) -> str:
    """Remap trusted query templates, including document-ID string prefixes."""
    return re.sub(r"\braw_infotree_[a-z_]+\b",
                  lambda match: collections[match.group()], query)


def shared_context_checks() -> list[QueryCheck]:
    checks = []
    for kind, ref_key, decl_key in (("mctx", "(r.mctxKey || r.mctxRefKey)",
                                   "(r.mctxKey || r.mctxRefKey)"),
                                  ("lctx", "r.lctxKey", "r.sourceKey")):
        context = f"raw_infotree_{kind}_contexts"
        for table, expression, edge, outgoing in (
                ("refs", ref_key, "ref_context", True),
                ("decls", decl_key, "context_decl", False)):
            rows = f"raw_infotree_{kind}_{table}"
            edges = f"raw_infotree_{kind}_{edge}_edges"
            source = "r._id" if outgoing else f'CONCAT("{context}/", {expression})'
            dest = f'CONCAT("{context}/", {expression})' if outgoing else "r._id"
            # Exactly one edge per raw row, and no edge to the wrong context.
            row_endpoint = "_from" if outgoing else "_to"
            checks.append(QueryCheck(f"{kind}_{table}_exact_context_membership", f"""
FOR r IN {rows}
  LET ctx = DOCUMENT(CONCAT("{context}/", {expression}))
  LET links = (FOR e IN {edges} FILTER e.{row_endpoint} == r._id RETURN e)
  FILTER ctx == null OR ctx.rootKey != (r.rootKey || "") OR LENGTH(links) != 1
    OR links[0]._from != {source} OR links[0]._to != {dest}
  LIMIT 20 RETURN {{row: r._id, context: ctx, links: links}}
"""))
        # This counts declarations once per context, not once per ref×decl pair.
        if kind == "lctx":
            checks.append(QueryCheck("lctx_shared_sizes_match", f"""
FOR c IN {context}
  LET size = LENGTH(FOR e IN raw_infotree_lctx_context_decl_edges
                    FILTER e._from == c._id RETURN 1)
  FOR r IN raw_infotree_lctx_refs FILTER r.lctxKey == c._key
  FILTER r.lctxSize != size
  LIMIT 20 RETURN {{ref: r._id, expected: r.lctxSize, actual: size}}
"""))
    return checks


def generation_checks(layout: str, collections: dict[str, str], definitions: list[dict[str, Any]]) -> list[QueryCheck]:
    removed = {"mctx_decl_rows_have_mctx_ref_edges", "lctx_refs_descend_to_decl_rows"}
    checks = [c for c in structural_checks()
              if "ig_nodes" not in c.query and not (layout == "shared" and c.name in removed)]
    if layout == "shared":
        checks.extend(shared_context_checks())
    checks = [QueryCheck(c.name, remap_query(c.query, collections), c.expect_empty) for c in checks]
    # Validate every edge family's endpoints, including cross-generation wires.
    for definition in definitions:
        collection = definition["collection"]
        checks.append(QueryCheck(f"{collection}_closed_endpoints", f"""
FOR e IN {collection}
  FILTER DOCUMENT(e._from) == null OR DOCUMENT(e._to) == null
    OR PARSE_IDENTIFIER(e._from).collection NOT IN {json.dumps(definition['from'])}
    OR PARSE_IDENTIFIER(e._to).collection NOT IN {json.dumps(definition['to'])}
  LIMIT 20 RETURN e
"""))
    return checks


def verify_generation(target: ArangoTarget, generation_id: str) -> dict[str, Any]:
    from tools.infra.arango_raw_infotree_graph import generation_graph_spec
    if not re.fullmatch(r"[0-9a-f]{24}", generation_id):
        raise ValueError("invalid generation ID")
    receipt = request_json("GET", db_url(target,
        f"/_api/document/raw_infotree_generations/{generation_id}"),
        username=target.username, password=target.password)
    layout, definitions = generation_graph_spec(receipt, generation_id)
    collections = receipt["collections"]
    expected = {**receipt["rowCounts"], **receipt["edgeCounts"]}
    if set(expected) != set(collections) or any(type(n) is not int or n < 0 for n in expected.values()):
        raise ValueError("generation receipt has incomplete or invalid expected counts")
    existing = list_collections(target)
    missing = sorted(set(collections.values()) - existing)
    live = {name: collection_count(target, name) for name in collections.values() if name in existing}
    mismatches = {collections[name]: {"expected": n, "live": live.get(collections[name])}
                  for name, n in expected.items() if live.get(collections[name]) != n}
    checks = {}
    if not missing:
        for check in generation_checks(layout, collections, definitions):
            rows = run_aql(target, check.query)
            checks[check.name] = {"ok": not rows, "sample_count": len(rows), "samples": rows}
    return {"schema": "info_geometry.raw_infotree_arango_descent_verification.v2",
            "database": target.database, "generation_id": generation_id,
            "context_layout": layout,
            "ok": not missing and not mismatches and all(c["ok"] for c in checks.values()),
            "counts": {"live": live, "missing_collections": missing, "mismatches": mismatches},
            "checks": checks,
            "external_declaration_join": {"status": "not_checked",
                "reason": "ig_nodes has no established generation binding in this receipt"},
            "scope": "raw projection counts, structural descent and endpoint closure; not compiler losslessness"}


def compare_context_layouts(target: ArangoTarget, expanded_id: str, shared_id: str) -> dict[str, Any]:
    """Compare live raw rows and context endpoint multisets without global pair materialization."""
    from tools.infra.arango_raw_infotree_graph import generation_graph_spec
    receipts = []
    for ident, expected_layout in ((expanded_id, "expanded"), (shared_id, "shared")):
        if not re.fullmatch(r"[0-9a-f]{24}", ident):
            raise ValueError("invalid generation ID")
        receipt = request_json("GET", db_url(target,
            f"/_api/document/raw_infotree_generations/{ident}"),
            username=target.username, password=target.password)
        layout, _ = generation_graph_spec(receipt, ident)
        if layout != expected_layout:
            raise ValueError("comparison requires expanded then shared generations")
        receipts.append(receipt)
    old, new = receipts
    for field in ("buildFingerprint", "sourceProvenance"):
        if not old.get(field) or old[field] != new.get(field):
            raise ValueError(f"generation provenance mismatch: {field}")
    checks = {}
    # Bidirectional raw-row comparison also detects additional rows, not just count differences.
    for name in ROW_FILES:
        for direction, left, right in (("forward", old, new), ("reverse", new, old)):
            rows = run_aql(target, """
FOR r IN @@left
  LET other = DOCUMENT(@right, r._key)
  FILTER other == null OR UNSET(r, "_id", "_rev") != UNSET(other, "_id", "_rev")
  LIMIT 20 RETURN r._key
""", {"@left": left["collections"][name], "right": right["collections"][name]})
            checks[f"{name}_{direction}"] = {"ok": not rows, "samples": rows}
    for kind, legacy in (("mctx", "raw_infotree_mctx_decl_edges"),
                         ("lctx", "raw_infotree_lctx_ref_decl_edges")):
        # Arrays are bounded by one reference's context, not the whole ref×decl relation.
        rows = run_aql(target, """
FOR r IN @@refs
  LET oldRef = CONCAT(@oldRefs, "/", r._key)
  LET expanded = (FOR e IN @@expanded FILTER e._from == oldRef
    LET key = PARSE_IDENTIFIER(e._to).key SORT key RETURN key)
  LET shared = (FOR a IN @@refContext FILTER a._from == r._id
    FOR b IN @@contextDecl FILTER b._from == a._to
    LET key = PARSE_IDENTIFIER(b._to).key SORT key RETURN key)
  FILTER expanded != shared
  LIMIT 20 RETURN {reference: r._key, expanded: expanded, shared: shared}
""", {"@refs": new["collections"][f"raw_infotree_{kind}_refs"],
       "oldRefs": old["collections"][f"raw_infotree_{kind}_refs"],
       "@expanded": old["collections"][legacy],
       "@refContext": new["collections"][f"raw_infotree_{kind}_ref_context_edges"],
       "@contextDecl": new["collections"][f"raw_infotree_{kind}_context_decl_edges"]})
        checks[f"{kind}_endpoint_multiset"] = {"ok": not rows, "samples": rows}
    old_edges = sum(old["edgeCounts"].values())
    new_edges = sum(new["edgeCounts"].values())
    return {"schema": "info_geometry.raw_context_layout_comparison.v1",
            "expanded_generation": expanded_id, "shared_generation": shared_id,
            "ok": all(c["ok"] for c in checks.values()), "checks": checks,
            "receipt_edge_counts": {"expanded": old_edges, "shared": new_edges},
            "scope": "raw-row equality and context endpoint multisets; run generation descent separately"}


def parse_args() -> argparse.Namespace:
    load_repo_arango_env(REPO_ROOT)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password())
    parser.add_argument("--ingest-report", type=Path)
    parser.add_argument("--generation-id", help="Verify a completed immutable raw generation")
    parser.add_argument("--compare-expanded-generation", help="Compare this expanded generation with --generation-id shared generation")
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
    if args.compare_expanded_generation and not args.generation_id:
        raise ValueError("--compare-expanded-generation requires --generation-id")
    if args.generation_id:
        if args.ingest_report:
            raise ValueError("use --generation-id or --ingest-report, not both")
        report = (compare_context_layouts(target, args.compare_expanded_generation, args.generation_id)
                  if args.compare_expanded_generation else verify_generation(target, args.generation_id))
        if args.json_out:
            args.json_out.parent.mkdir(parents=True, exist_ok=True)
            args.json_out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(report, indent=2))
        return 0 if report["ok"] else 2
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
