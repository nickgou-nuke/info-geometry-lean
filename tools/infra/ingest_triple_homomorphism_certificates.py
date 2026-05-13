#!/usr/bin/env python3
"""Materialize Lean finite triple-homomorphism audits as Arango edge documents.

This script consumes the audit JSON and missing-triples JSONL emitted by
``lean/DAG/TripleHomomorphismExport.lean``.  It mirrors that Lean-native finite
incidence-preservation result into a graph edge layer.  It does not certify
theorem equality or rewrite safety; those remain the responsibility of
``KernelEquivalenceExport.lean`` and kernel-equivalence certificate edges.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.arango_raw_infotree_ingest import (
    ArangoTarget,
    CollectionSpec,
    collection_count,
    create_collection,
    ensure_database,
    ensure_index,
    import_rows,
    iter_jsonl,
    list_collections,
    truncate_collection,
)


DEFAULT_AUDIT = Path("artifacts/expr-graph/translation-candidates/triple-homomorphism-audit.json")
DEFAULT_MISSING = Path("artifacts/expr-graph/translation-candidates/missing-triples.jsonl")
DEFAULT_OUTPUT = Path("artifacts/expr-graph/wire-topology/ig_triple_homomorphism_edges.jsonl")
DEFAULT_EDGE_COLLECTION = "ig_triple_homomorphism_edges"

INDEX_SPECS: list[list[str]] = [
    ["kind"],
    ["status"],
    ["sourceId"],
    ["targetId"],
    ["sourceLabel"],
    ["targetLabel"],
    ["verificationTier"],
    ["proofAuthority"],
    ["checker"],
    ["leanVerified"],
    ["safeForAutoRewrite"],
    ["safeForDedupSCC"],
    ["graphUse"],
    ["candidatePairHash"],
    ["certificateHash"],
    ["missingTripleHash"],
    ["_from", "kind"],
    ["_to", "kind"],
]


def stable_hash(*parts: Any) -> str:
    payload = "|".join(str(part) for part in parts)
    return "sha256:" + hashlib.sha256(payload.encode("utf-8")).hexdigest()


def stable_key(prefix: str, *parts: Any) -> str:
    return prefix + "_" + stable_hash(*parts).split(":", 1)[1][:32]


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def bool_field(row: dict[str, Any], field: str) -> bool:
    return bool(row.get(field, False))


def triple_hom_status(audit: dict[str, Any]) -> str:
    return "triple_hom_verified" if bool_field(audit, "leanVerified") else "triple_hom_rejected"


def graph_use(audit: dict[str, Any]) -> str:
    return "triple-homomorphism-scc" if bool_field(audit, "leanVerified") else "rejected-candidate"


def certificate_tags(audit: dict[str, Any]) -> list[str]:
    tags = ["finite_triple_homomorphism"]
    if bool_field(audit, "leanVerified"):
        tags.append("lean_verified")
        tags.append("triple_preserved")
    else:
        tags.append("triple_hom_rejected")
        tags.append("missing_mapped_triples")
    tags.append("rewrite_not_authorized")
    return tags


def normalize_certificate_edge(
    audit: dict[str, Any],
    *,
    source_id: str,
    target_id: str,
    source_label: str = "",
    target_label: str = "",
    audit_file: str = "",
    missing_file: str = "",
    edge_collection: str = DEFAULT_EDGE_COLLECTION,
) -> dict[str, Any]:
    if not source_id or not target_id:
        raise ValueError("triple homomorphism certificate requires source_id and target_id")
    if source_id == target_id:
        raise ValueError("triple homomorphism certificate has identical source_id/target_id")

    tier = str(audit.get("verificationTier", "") or "lean_native_finite_triple_homomorphism")
    authority = str(audit.get("proofAuthority", "") or "Lean finite triple preservation checker")
    checker = str(audit.get("checker", "") or "DAG.TripleHomomorphismExport.auditHomomorphism")
    cert_hash = stable_hash(
        "triple-hom-cert",
        source_id,
        target_id,
        tier,
        audit.get("checkedTriples", 0),
        audit.get("preservedTriples", 0),
        audit.get("missingTriples", 0),
        bool_field(audit, "leanVerified"),
    )
    pair_hash = stable_hash("triple-homomorphism-pair", source_id, target_id)

    return {
        "_key": stable_key("thc", source_id, target_id, cert_hash),
        "_from": source_id,
        "_to": target_id,
        "kind": "triple_homomorphism_certificate",
        "status": triple_hom_status(audit),
        "sourceId": source_id,
        "targetId": target_id,
        "sourceLabel": source_label,
        "targetLabel": target_label,
        "sourceTriples": int(audit.get("sourceTriples", 0) or 0),
        "targetTriples": int(audit.get("targetTriples", 0) or 0),
        "objectMappings": int(audit.get("objectMappings", 0) or 0),
        "relationMappings": int(audit.get("relationMappings", 0) or 0),
        "checkedTriples": int(audit.get("checkedTriples", 0) or 0),
        "preservedTriples": int(audit.get("preservedTriples", 0) or 0),
        "missingTriples": int(audit.get("missingTriples", 0) or 0),
        "leanVerified": bool_field(audit, "leanVerified"),
        "safeForDedupSCC": bool_field(audit, "leanVerified"),
        "safeForAutoRewrite": False,
        "verificationTier": tier,
        "proofAuthority": authority,
        "checker": checker,
        "certificateKind": "lean_native_finite_triple_homomorphism",
        "certificateHash": cert_hash,
        "candidatePairHash": pair_hash,
        "auditFile": audit_file,
        "missingFile": missing_file,
        "tags": certificate_tags(audit),
        "graphUse": graph_use(audit),
        "edgeCollection": edge_collection,
    }


def normalize_missing_triple_edge(
    row: dict[str, Any],
    *,
    source_id: str,
    target_id: str,
    certificate_hash: str,
    index: int,
    edge_collection: str = DEFAULT_EDGE_COLLECTION,
) -> dict[str, Any]:
    missing_hash = stable_hash(
        "missing-mapped-triple",
        source_id,
        target_id,
        row.get("subject", ""),
        row.get("predicate", ""),
        row.get("object", ""),
        row.get("mappedSubject", ""),
        row.get("mappedPredicate", ""),
        row.get("mappedObject", ""),
    )
    return {
        "_key": stable_key("mmt", certificate_hash, index, missing_hash),
        "_from": source_id,
        "_to": target_id,
        "kind": "missing_mapped_triple",
        "status": "missing_mapped_triple",
        "sourceId": source_id,
        "targetId": target_id,
        "subject": str(row.get("subject", "") or ""),
        "predicate": str(row.get("predicate", "") or ""),
        "object": str(row.get("object", "") or ""),
        "mappedSubject": str(row.get("mappedSubject", "") or ""),
        "mappedPredicate": str(row.get("mappedPredicate", "") or ""),
        "mappedObject": str(row.get("mappedObject", "") or ""),
        "leanVerified": False,
        "safeForDedupSCC": False,
        "safeForAutoRewrite": False,
        "verificationTier": "missing_mapped_triple",
        "proofAuthority": "Lean finite triple preservation checker",
        "checker": "DAG.TripleHomomorphismExport.auditHomomorphism",
        "certificateHash": certificate_hash,
        "missingTripleHash": missing_hash,
        "graphUse": "rejected-candidate-evidence",
        "edgeCollection": edge_collection,
    }


def materialize_edges(
    audit_path: Path,
    missing_path: Path,
    *,
    source_id: str,
    target_id: str,
    source_label: str = "",
    target_label: str = "",
    edge_collection: str = DEFAULT_EDGE_COLLECTION,
) -> list[dict[str, Any]]:
    audit = read_json(audit_path)
    cert = normalize_certificate_edge(
        audit,
        source_id=source_id,
        target_id=target_id,
        source_label=source_label,
        target_label=target_label,
        audit_file=str(audit_path),
        missing_file=str(missing_path),
        edge_collection=edge_collection,
    )
    rows = [cert]
    if missing_path.exists():
        for index, row in enumerate(iter_jsonl(missing_path)):
            rows.append(
                normalize_missing_triple_edge(
                    row,
                    source_id=source_id,
                    target_id=target_id,
                    certificate_hash=str(cert["certificateHash"]),
                    index=index,
                    edge_collection=edge_collection,
                )
            )
    return rows


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
            count += 1
    return count


def ensure_certificate_collection(target: ArangoTarget, *, edge_collection: str, truncate: bool) -> dict[str, Any]:
    ensure_database(target)
    existing = list_collections(target)
    report: dict[str, Any] = {"created": False, "existing": edge_collection in existing, "truncated": False}
    if edge_collection not in existing:
        create_collection(target, CollectionSpec(edge_collection, edge=True))
        report["created"] = True
    if truncate:
        truncate_collection(target, edge_collection)
        report["truncated"] = True
    return report


def ensure_certificate_indexes(target: ArangoTarget, *, edge_collection: str) -> list[dict[str, Any]]:
    report: list[dict[str, Any]] = []
    for fields in INDEX_SPECS:
        result = ensure_index(target, edge_collection, fields)
        report.append(
            {
                "fields": fields,
                "error": bool(result.get("error")) if isinstance(result, dict) else False,
                "id": result.get("id") if isinstance(result, dict) else None,
                "isNewlyCreated": result.get("isNewlyCreated") if isinstance(result, dict) else None,
            }
        )
    return report


def ingest_edges(
    rows: list[dict[str, Any]],
    target: ArangoTarget,
    *,
    edge_collection: str,
    truncate: bool,
    skip_indexes: bool,
    batch_size: int,
) -> dict[str, Any]:
    report: dict[str, Any] = {
        "schema": "info_geometry.triple_homomorphism_certificates.v1",
        "truth_boundary": "Lean finite triple preservation only; not theorem equality or rewrite authority",
        "edge_collection": edge_collection,
        "collections": ensure_certificate_collection(target, edge_collection=edge_collection, truncate=truncate),
        "imports": import_rows(target, edge_collection, rows, batch_size=batch_size),
    }
    if not skip_indexes:
        report["indexes"] = ensure_certificate_indexes(target, edge_collection=edge_collection)
    report["live_count"] = collection_count(target, edge_collection)
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT)
    parser.add_argument("--missing", type=Path, default=DEFAULT_MISSING)
    parser.add_argument("--source-id", required=True)
    parser.add_argument("--target-id", required=True)
    parser.add_argument("--source-label", default="")
    parser.add_argument("--target-label", default="")
    parser.add_argument("--jsonl-out", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--report-out",
        type=Path,
        default=Path("artifacts/expr-graph/translation-candidates/triple_homomorphism_ingest_report.json"),
    )
    parser.add_argument("--edge-collection", default=DEFAULT_EDGE_COLLECTION)
    parser.add_argument("--endpoint", default=None)
    parser.add_argument("--database", default=None)
    parser.add_argument("--username", default=None)
    parser.add_argument("--password", default=None)
    parser.add_argument("--truncate", action="store_true")
    parser.add_argument("--skip-indexes", action="store_true")
    parser.add_argument("--skip-arango", action="store_true")
    parser.add_argument("--batch-size", type=int, default=1000)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        rows = materialize_edges(
            args.audit,
            args.missing,
            source_id=str(args.source_id),
            target_id=str(args.target_id),
            source_label=str(args.source_label),
            target_label=str(args.target_label),
            edge_collection=str(args.edge_collection),
        )
        written = write_jsonl(args.jsonl_out, rows)
        report: dict[str, Any] = {
            "schema": "info_geometry.triple_homomorphism_certificates.v1",
            "audit": str(args.audit),
            "missing": str(args.missing),
            "jsonl_out": str(args.jsonl_out),
            "edges": written,
            "arango": None,
        }
        if not args.skip_arango:
            load_repo_arango_env()
            target = ArangoTarget(
                endpoint=args.endpoint or arango_endpoint(),
                database=args.database or arango_database(),
                username=args.username or arango_username(),
                password=args.password or arango_password(),
            )
            report["arango"] = ingest_edges(
                rows,
                target,
                edge_collection=str(args.edge_collection),
                truncate=bool(args.truncate),
                skip_indexes=bool(args.skip_indexes),
                batch_size=int(args.batch_size),
            )
        args.report_out.parent.mkdir(parents=True, exist_ok=True)
        args.report_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"Triple homomorphism certificate report written: {args.report_out}")
        return 0
    except subprocess.CalledProcessError as exc:
        print(str(exc), file=sys.stderr)
        return exc.returncode or 1
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
