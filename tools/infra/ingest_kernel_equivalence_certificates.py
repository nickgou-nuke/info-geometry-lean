#!/usr/bin/env python3
"""Materialize Lean kernel-equivalence certificates as Arango edge documents.

This script is deliberately separate from candidate generation.  It consumes
JSONL rows emitted by ``lean/DAG/KernelEquivalenceExport.lean`` and creates a
certificate edge layer.  It does not infer equivalence from hashes, vectors, or
RDF topology; it only mirrors Lean/kernel certificate rows into graph form.
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


DEFAULT_CERTS = Path("artifacts/expr-graph/translation-candidates/lean-kernel-equivalence.jsonl")
DEFAULT_OUTPUT = Path("artifacts/expr-graph/wire-topology/ig_kernel_equivalence_edges.jsonl")
DEFAULT_EDGE_COLLECTION = "ig_kernel_equivalence_edges"
DEFAULT_DECL_COLLECTION = "ig_decl_topologies"

INDEX_SPECS: list[list[str]] = [
    ["kind"],
    ["status"],
    ["mode"],
    ["sourceDecl"],
    ["targetDecl"],
    ["verificationTier"],
    ["proofAuthority"],
    ["leanVerified"],
    ["kernelTypeDefEq"],
    ["kernelValueDefEq"],
    ["safeForAutoRewrite"],
    ["graphUse"],
    ["candidatePairHash"],
    ["certificateHash"],
    ["_from", "kind"],
    ["_to", "kind"],
]


def stable_hash(*parts: Any) -> str:
    payload = "|".join(str(part) for part in parts)
    return "sha256:" + hashlib.sha256(payload.encode("utf-8")).hexdigest()


def stable_key(prefix: str, *parts: Any) -> str:
    return prefix + "_" + stable_hash(*parts).split(":", 1)[1][:32]


def decl_ref(decl: str, *, decl_collection: str) -> str:
    return f"{decl_collection}/{stable_key('topo', decl)}"


def bool_field(row: dict[str, Any], field: str) -> bool:
    return bool(row.get(field, False))


def certificate_tags(row: dict[str, Any]) -> list[str]:
    tags: list[str] = []
    if bool_field(row, "kernelTypeDefEq"):
        tags.append("kernel_type_defeq")
    if bool_field(row, "kernelValueDefEq"):
        tags.append("kernel_value_defeq")
    if bool_field(row, "leanVerified"):
        tags.append("lean_verified")
    else:
        tags.append("kernel_rejected")
    if bool_field(row, "safeForAutoRewrite"):
        tags.append("rewrite_safe")
    else:
        tags.append("rewrite_not_authorized")
    return tags


def graph_use(row: dict[str, Any]) -> str:
    if bool_field(row, "safeForAutoRewrite"):
        return "rewrite-safe-scc"
    if bool_field(row, "leanVerified"):
        return "verified-equivalence-only"
    return "rejected-candidate"


def certificate_status(row: dict[str, Any]) -> str:
    if bool_field(row, "safeForAutoRewrite"):
        return "rewrite_safe"
    if bool_field(row, "leanVerified"):
        return "verified_not_rewrite_safe"
    return "rejected"


def normalize_certificate_edge(
    row: dict[str, Any],
    *,
    edge_collection: str = DEFAULT_EDGE_COLLECTION,
    decl_collection: str = DEFAULT_DECL_COLLECTION,
    certificate_file: str = "",
) -> dict[str, Any]:
    source = str(row.get("sourceDecl", "") or "")
    target = str(row.get("targetDecl", "") or "")
    if not source or not target:
        raise ValueError("kernel certificate row is missing sourceDecl/targetDecl")
    if source == target:
        raise ValueError("kernel certificate row has identical sourceDecl/targetDecl")

    mode = str(row.get("mode", "") or "")
    verification_tier = str(row.get("verificationTier", "") or "")
    cert_hash = str(row.get("certificateHash", "") or stable_hash("kernel-cert", source, target, mode, verification_tier))
    pair_hash = stable_hash("kernel-equivalence-pair", source, target, mode)
    status = certificate_status(row)

    return {
        "_key": stable_key("kec", source, target, mode, cert_hash),
        "_from": decl_ref(source, decl_collection=decl_collection),
        "_to": decl_ref(target, decl_collection=decl_collection),
        "kind": "kernel_equivalence_certificate",
        "status": status,
        "sourceDecl": source,
        "targetDecl": target,
        "mode": mode,
        "sourceFound": bool_field(row, "sourceFound"),
        "targetFound": bool_field(row, "targetFound"),
        "sourceKind": str(row.get("sourceKind", "") or ""),
        "targetKind": str(row.get("targetKind", "") or ""),
        "sameKind": bool_field(row, "sameKind"),
        "kernelTypeDefEq": bool_field(row, "kernelTypeDefEq"),
        "kernelValueDefEq": bool_field(row, "kernelValueDefEq"),
        "sourceHasValue": bool_field(row, "sourceHasValue"),
        "targetHasValue": bool_field(row, "targetHasValue"),
        "leanVerified": bool_field(row, "leanVerified"),
        "safeForAutoRewrite": bool_field(row, "safeForAutoRewrite"),
        "verificationTier": verification_tier,
        "proofAuthority": str(row.get("proofAuthority", "") or "Lean.Meta.isDefEq"),
        "checker": str(row.get("checker", "") or "Lean.Meta.isDefEq"),
        "certificateKind": str(row.get("certificateKind", "") or "lean_kernel_equivalence"),
        "certificateHash": cert_hash,
        "candidatePairHash": pair_hash,
        "certificateFile": certificate_file,
        "tags": certificate_tags(row),
        "graphUse": graph_use(row),
        "error": str(row.get("error", "") or ""),
        "edgeCollection": edge_collection,
    }


def materialize_edges(
    certs_path: Path,
    *,
    edge_collection: str = DEFAULT_EDGE_COLLECTION,
    decl_collection: str = DEFAULT_DECL_COLLECTION,
    certificate_file: str | None = None,
) -> list[dict[str, Any]]:
    cert_file = certificate_file if certificate_file is not None else str(certs_path)
    return [
        normalize_certificate_edge(
            row,
            edge_collection=edge_collection,
            decl_collection=decl_collection,
            certificate_file=cert_file,
        )
        for row in iter_jsonl(certs_path)
    ]


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
        "schema": "info_geometry.kernel_equivalence_certificates.v1",
        "truth_boundary": "Lean.Meta.isDefEq certificate rows only; no vector/hash promotion",
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
    parser.add_argument("--certs", type=Path, default=DEFAULT_CERTS)
    parser.add_argument("--jsonl-out", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--report-out", type=Path, default=Path("artifacts/expr-graph/translation-candidates/kernel_equivalence_ingest_report.json"))
    parser.add_argument("--edge-collection", default=DEFAULT_EDGE_COLLECTION)
    parser.add_argument("--decl-collection", default=DEFAULT_DECL_COLLECTION)
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
            args.certs,
            edge_collection=str(args.edge_collection),
            decl_collection=str(args.decl_collection),
        )
        written = write_jsonl(args.jsonl_out, rows)
        report: dict[str, Any] = {
            "schema": "info_geometry.kernel_equivalence_certificates.v1",
            "certs": str(args.certs),
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
        print(f"Kernel equivalence certificate report written: {args.report_out}")
        return 0
    except subprocess.CalledProcessError as exc:
        print(str(exc), file=sys.stderr)
        return exc.returncode or 1
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
