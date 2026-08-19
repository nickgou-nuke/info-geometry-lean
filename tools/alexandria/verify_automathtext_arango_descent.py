#!/usr/bin/env python3
"""Verify AutoMathText-V2 epistemic ancestry descent in ArangoDB.

Non-mutating verifier for the generic `automath_*` sidecar graph imported by
`automathtext_arango_ingest.py`.  It checks that GraphRAG/theorem-shape/overlay
navigation can descend back to raw AutoMathText fragments through explicit
witness and ancestry links.

This is a provenance/retrieval integrity check only.  It is not mathematical
proof authority; Lean/build/audit remain the proof authority.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.alexandria.arango_ingest import db_url, request_json  # noqa: E402
from tools.alexandria.automathtext_arango_ingest import (  # noqa: E402
    DOCUMENT_COLLECTIONS,
    EDGE_COLLECTIONS,
)
from tools.infra.arango_env import (  # noqa: E402
    alexandria_arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)

AqlRunner = Callable[[str, dict[str, Any] | None], list[Any]]


@dataclass(frozen=True)
class QueryCheck:
    name: str
    query: str
    bind_vars: dict[str, Any] | None = None
    expect_empty: bool = True
    severity: str = "blocking"


def execute_aql(
    *,
    endpoint: str,
    database: str,
    username: str,
    password: str,
    query: str,
    bind_vars: dict[str, Any] | None = None,
    batch_size: int = 1000,
) -> list[Any]:
    payload = {"query": query, "bindVars": bind_vars or {}, "batchSize": batch_size, "count": True}
    first = request_json("POST", db_url(endpoint, database, "/_api/cursor"), username, password, payload)
    if not isinstance(first, dict):
        raise RuntimeError(f"AQL returned non-object payload: {first!r}")
    rows = list(first.get("result", []))
    cursor_id = first.get("id")
    has_more = bool(first.get("hasMore"))
    while has_more and cursor_id:
        page = request_json("PUT", db_url(endpoint, database, f"/_api/cursor/{cursor_id}"), username, password)
        if not isinstance(page, dict):
            raise RuntimeError(f"AQL cursor page returned non-object payload: {page!r}")
        rows.extend(page.get("result", []))
        cursor_id = page.get("id")
        has_more = bool(page.get("hasMore"))
    return rows


def collection_count_query(collection: str) -> str:
    return f"RETURN LENGTH({collection})"


def collection_counts(runner: AqlRunner) -> dict[str, int]:
    counts: dict[str, int] = {}
    for collection in DOCUMENT_COLLECTIONS + EDGE_COLLECTIONS:
        result = runner(collection_count_query(collection), None)
        counts[collection] = int(result[0]) if result else 0
    return counts


def edge_endpoint_check(collection: str) -> QueryCheck:
    return QueryCheck(
        name=f"{collection}_endpoints_resolve",
        query=f"""
FOR e IN {collection}
  LET fromDoc = DOCUMENT(e._from)
  LET toDoc = DOCUMENT(e._to)
  FILTER fromDoc == null OR toDoc == null
  LIMIT 20
  RETURN {{ edge: e, missingFrom: fromDoc == null, missingTo: toDoc == null }}
""",
    )


def structural_checks() -> list[QueryCheck]:
    checks = [edge_endpoint_check(collection) for collection in EDGE_COLLECTIONS]
    checks.extend(
        [
            QueryCheck(
                name="chunks_descend_to_fragments",
                query="""
FOR c IN automath_chunks
  LET f = DOCUMENT(CONCAT("automath_fragments/", c.source_fragment))
  LET ancestry = FIRST(
    FOR e IN automath_ancestry_edges
      FILTER e.role == "fragment_to_chunk"
      FILTER e._from == CONCAT("automath_fragments/", c.source_fragment)
      FILTER e._to == CONCAT("automath_chunks/", c._key)
      RETURN e
  )
  FILTER f == null OR ancestry == null
  LIMIT 20
  RETURN { chunk: c, missingFragment: f == null, missingAncestryEdge: ancestry == null }
""",
            ),
            QueryCheck(
                name="chunks_have_fragment_first_ancestry_path",
                query="""
FOR c IN automath_chunks
  LET f = DOCUMENT(CONCAT("automath_fragments/", c.source_fragment))
  FILTER f != null
  FILTER !IS_ARRAY(c.ancestry_path) OR LENGTH(c.ancestry_path) < 2 OR c.ancestry_path[0] != f.ancestry_hash
  LIMIT 20
  RETURN { chunk: c, fragment: f }
""",
            ),
            QueryCheck(
                name="entities_descend_to_chunk_and_fragment",
                query="""
FOR ent IN automath_entities
  LET c = DOCUMENT(CONCAT("automath_chunks/", ent.source_chunk))
  LET f = DOCUMENT(CONCAT("automath_fragments/", ent.source_fragment))
  FILTER c == null OR f == null
  LIMIT 20
  RETURN { entity: ent, missingChunk: c == null, missingFragment: f == null }
""",
            ),
            QueryCheck(
                name="expr_nodes_descend_to_chunks",
                query="""
FOR n IN automath_expr_nodes
  LET c = DOCUMENT(CONCAT("automath_chunks/", n.source_chunk))
  LET ancestry = FIRST(
    FOR e IN automath_ancestry_edges
      FILTER e.role == "chunk_to_expr_node"
      FILTER e._from == CONCAT("automath_chunks/", n.source_chunk)
      FILTER e._to == CONCAT("automath_expr_nodes/", n._key)
      RETURN e
  )
  FILTER c == null OR ancestry == null
  LIMIT 20
  RETURN { exprNode: n, missingChunk: c == null, missingAncestryEdge: ancestry == null }
""",
            ),
            QueryCheck(
                name="theorem_shapes_descend_to_chunks_and_fragments",
                query="""
FOR s IN automath_theorem_shapes
  LET c = DOCUMENT(CONCAT("automath_chunks/", s.source_chunk))
  LET f = DOCUMENT(CONCAT("automath_fragments/", s.source_fragment))
  LET ancestry = FIRST(
    FOR e IN automath_ancestry_edges
      FILTER e.role == "chunk_to_theorem_shape"
      FILTER e._from == CONCAT("automath_chunks/", s.source_chunk)
      FILTER e._to == CONCAT("automath_theorem_shapes/", s._key)
      RETURN e
  )
  FILTER c == null OR f == null OR ancestry == null
  LIMIT 20
  RETURN { theoremShape: s, missingChunk: c == null, missingFragment: f == null, missingAncestryEdge: ancestry == null }
""",
            ),
            QueryCheck(
                name="theorem_shapes_have_raw_to_shape_ancestry_path",
                query="""
FOR s IN automath_theorem_shapes
  LET c = DOCUMENT(CONCAT("automath_chunks/", s.source_chunk))
  LET f = DOCUMENT(CONCAT("automath_fragments/", s.source_fragment))
  FILTER c != null AND f != null
  FILTER !IS_ARRAY(s.ancestry_path)
    OR LENGTH(s.ancestry_path) < 3
    OR s.ancestry_path[0] != f.ancestry_hash
    OR s.ancestry_path[1] != c.ancestry_hash
    OR s.ancestry_path[2] != s.ancestry_hash
  LIMIT 20
  RETURN { theoremShape: s, chunk: c, fragment: f }
""",
            ),
            QueryCheck(
                name="triples_have_ancestry_and_source_context",
                query="""
FOR t IN automath_triples
  FILTER t.ancestry_hash == null
    OR !IS_ARRAY(t.ancestry_path)
    OR LENGTH(t.ancestry_path) == 0
    OR (t.source_fragment == null AND t.source_chunk == null)
  LIMIT 20
  RETURN t
""",
            ),
            QueryCheck(
                name="overlay_edges_have_witness_chunk_descent",
                query="""
FOR e IN automath_overlay_edges
  LET missingWitnesses = (
    FOR chunkKey IN (IS_ARRAY(e.witness_chunk_keys) ? e.witness_chunk_keys : [])
      LET c = DOCUMENT(CONCAT("automath_chunks/", chunkKey))
      FILTER c == null
      RETURN chunkKey
  )
  FILTER !IS_ARRAY(e.witness_chunk_keys) OR LENGTH(e.witness_chunk_keys) == 0 OR LENGTH(missingWitnesses) > 0
  LIMIT 20
  RETURN { edge: e, missingWitnesses: missingWitnesses }
""",
            ),
            QueryCheck(
                name="ancestry_edges_hashes_match_endpoints",
                query="""
FOR e IN automath_ancestry_edges
  LET fromDoc = DOCUMENT(e._from)
  LET toDoc = DOCUMENT(e._to)
  FILTER fromDoc != null AND toDoc != null
  FILTER e.source_ancestry_hash != fromDoc.ancestry_hash OR e.target_ancestry_hash != toDoc.ancestry_hash
  LIMIT 20
  RETURN { edge: e, fromDoc: fromDoc, toDoc: toDoc }
""",
            ),
        ]
    )
    return checks


def positive_presence_checks(counts: dict[str, int]) -> list[dict[str, Any]]:
    required_nonempty = ["automath_fragments", "automath_chunks", "automath_ancestry_edges"]
    failures: list[dict[str, Any]] = []
    for collection in required_nonempty:
        if counts.get(collection, 0) <= 0:
            failures.append(
                {
                    "name": f"{collection}_nonempty",
                    "severity": "blocking",
                    "count": counts.get(collection, 0),
                    "message": f"{collection} must be non-empty for provenance descent verification",
                }
            )
    return failures


def run_checks(runner: AqlRunner) -> dict[str, Any]:
    counts = collection_counts(runner)
    failures: list[dict[str, Any]] = positive_presence_checks(counts)
    passed: list[str] = []
    check_results: list[dict[str, Any]] = []

    for check in structural_checks():
        rows = runner(check.query, check.bind_vars)
        failed = bool(rows) if check.expect_empty else not bool(rows)
        result = {
            "name": check.name,
            "severity": check.severity,
            "ok": not failed,
            "sample_count": len(rows),
            "samples": rows[:5],
        }
        check_results.append(result)
        if failed:
            failures.append(result)
        else:
            passed.append(check.name)

    blocking_failures = [f for f in failures if f.get("severity") == "blocking"]
    return {
        "schema": "info_geometry.alexandria.automathtext_arango_descent_check.v1",
        "ok": not blocking_failures,
        "authority": "provenance_retrieval_check_only_not_proof_authority",
        "collection_counts": counts,
        "passed_checks": passed,
        "checks": check_results,
        "failure_count": len(failures),
        "blocking_failure_count": len(blocking_failures),
        "failures": failures,
        "required_nonempty_collections": ["automath_fragments", "automath_chunks", "automath_ancestry_edges"],
    }


def make_live_runner(args: argparse.Namespace) -> AqlRunner:
    def runner(query: str, bind_vars: dict[str, Any] | None = None) -> list[Any]:
        return execute_aql(
            endpoint=args.endpoint,
            database=args.database,
            username=args.username,
            password=args.password,
            query=query,
            bind_vars=bind_vars,
        )

    return runner


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default=alexandria_arango_endpoint())
    parser.add_argument("--database", default="alexandria")
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password("alexandria_root"))
    parser.add_argument("--json", action="store_true", help="Print full JSON report.")
    parser.add_argument("--json-out", type=Path, help="Write full JSON report to path.")
    return parser.parse_args()


def main() -> int:
    load_repo_arango_env(Path.cwd())
    args = parse_args()
    report = run_checks(make_live_runner(args))
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(report, ensure_ascii=True, indent=2, sort_keys=True))
    else:
        status = "AUTOMATHTEXT_ARANGO_DESCENT_OK" if report["ok"] else "AUTOMATHTEXT_ARANGO_DESCENT_FAILED"
        print(
            status,
            f"collections={len(report['collection_counts'])}",
            f"blocking_failures={report['blocking_failure_count']}",
        )
    return 0 if report["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
