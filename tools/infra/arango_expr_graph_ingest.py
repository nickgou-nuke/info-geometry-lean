#!/usr/bin/env python3
"""Ingest ExprArangoExport JSONL into ArangoDB.

This imports the expression-level graph emitted by
``lean/DAG/ExprArangoExport.lean``.  It keeps the compiler expression graph as
plain Arango vertices/edges and adds indexes for exact symbolic lookup:
De Bruijn binder incidence, expression shape, declarations, and AST edge roles.

Vector embeddings, RDF statement projection, and ArangoSearch views are intended
as overlays on top of this exact symbolic layer, not replacements for it.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

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


DEFAULT_INPUT_DIR = Path("artifacts/expr-graph/arango")

ROW_FILES: dict[str, str] = {
    "ig_nodes": "ig_nodes.jsonl",
    "ig_edges": "ig_edges.jsonl",
}

COLLECTION_SPECS = [
    CollectionSpec("ig_nodes", edge=False),
    CollectionSpec("ig_edges", edge=True),
]

INDEX_SPECS: dict[str, list[list[str]]] = {
    "ig_nodes": [
        ["graphKind"],
        ["exprTag"],
        ["kind"],
        ["decl"],
        ["module"],
        ["sectionTag"],
        ["shapeHash"],
        ["deBruijnIdx"],
        ["deBruijnHash"],
        ["alphaLocalHash"],
        ["deBruijnHash", "exprTag"],
        ["alphaLocalHash", "exprTag"],
    ],
    "ig_edges": [
        ["kind"],
        ["role"],
        ["decl"],
        ["sectionTag"],
        ["deBruijnIdx"],
        ["incidenceHash"],
        ["binderIncidenceHash"],
        ["_from", "role"],
        ["_to", "role"],
        ["kind", "role"],
    ],
}


def normalize_expr_row(collection: str, row: dict[str, Any]) -> dict[str, Any]:
    out = dict(row)
    if "_key" not in out or not str(out["_key"]):
        raise ValueError(f"{collection} row is missing _key")
    out["_key"] = str(out["_key"])
    return out


def expr_index_specs() -> dict[str, list[list[str]]]:
    return {collection: [list(fields) for fields in specs] for collection, specs in INDEX_SPECS.items()}


def ensure_expr_indexes(target: ArangoTarget) -> dict[str, Any]:
    report: dict[str, Any] = {}
    for collection, specs in INDEX_SPECS.items():
        collection_report = []
        for fields in specs:
            try:
                result = ensure_index(target, collection, fields)
                collection_report.append(
                    {
                        "fields": fields,
                        "error": bool(result.get("error")) if isinstance(result, dict) else False,
                        "id": result.get("id") if isinstance(result, dict) else None,
                        "isNewlyCreated": result.get("isNewlyCreated") if isinstance(result, dict) else None,
                    }
                )
            except Exception as exc:
                collection_report.append({"fields": fields, "error": True, "message": str(exc)})
        report[collection] = collection_report
    return report


def ensure_expr_collections(target: ArangoTarget, *, truncate: bool) -> dict[str, Any]:
    ensure_database(target)
    existing = list_collections(target)
    report: dict[str, Any] = {"created": [], "existing": [], "truncated": []}
    for spec in COLLECTION_SPECS:
        if spec.name not in existing:
            create_collection(target, spec)
            report["created"].append(spec.name)
        else:
            report["existing"].append(spec.name)
        if truncate:
            truncate_collection(target, spec.name)
            report["truncated"].append(spec.name)
    return report


def preflight(input_dir: Path) -> dict[str, Any]:
    missing = [name for name in ROW_FILES.values() if not (input_dir / name).exists()]
    counts = {
        collection: sum(1 for _ in iter_jsonl(input_dir / filename))
        for collection, filename in ROW_FILES.items()
        if (input_dir / filename).exists()
    }
    return {"input_dir": str(input_dir), "missing_files": missing, "counts": counts}


def ingest_expr_graph(
    input_dir: Path,
    target: ArangoTarget,
    *,
    truncate: bool,
    skip_indexes: bool,
    batch_size: int,
) -> dict[str, Any]:
    pf = preflight(input_dir)
    if pf["missing_files"]:
        raise RuntimeError(f"expr graph input preflight failed: missing {pf['missing_files']}")

    report: dict[str, Any] = {
        "schema": "info_geometry.arango_expr_graph_ingest.v1",
        "input_dir": str(input_dir),
        "preflight": pf,
        "collections": ensure_expr_collections(target, truncate=truncate),
        "imports": {},
    }

    for collection, filename in ROW_FILES.items():
        path = input_dir / filename
        rows = (normalize_expr_row(collection, row) for row in iter_jsonl(path))
        report["imports"][collection] = import_rows(
            target,
            collection,
            rows,
            batch_size=batch_size,
        )

    if not skip_indexes:
        report["indexes"] = ensure_expr_indexes(target)
    report["live_counts"] = {spec.name: collection_count(target, spec.name) for spec in COLLECTION_SPECS}
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=DEFAULT_INPUT_DIR)
    parser.add_argument("--endpoint", default=None)
    parser.add_argument("--database", default=None)
    parser.add_argument("--username", default=None)
    parser.add_argument("--password", default=None)
    parser.add_argument("--truncate", action="store_true")
    parser.add_argument("--skip-indexes", action="store_true")
    parser.add_argument("--batch-size", type=int, default=1000)
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/expr-graph/arango_expr_graph_ingest_report.json"))
    parser.add_argument("--skip-validate", action="store_true", help="Reserved for symmetry with other ingesters.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    load_repo_arango_env()
    target = ArangoTarget(
        endpoint=args.endpoint or arango_endpoint(),
        database=args.database or arango_database(),
        username=args.username or arango_username(),
        password=args.password or arango_password(),
    )

    try:
        report = ingest_expr_graph(
            args.input_dir,
            target,
            truncate=bool(args.truncate),
            skip_indexes=bool(args.skip_indexes),
            batch_size=int(args.batch_size),
        )
    except subprocess.CalledProcessError as exc:
        print(str(exc), file=sys.stderr)
        return exc.returncode or 1
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 1

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Expr graph Arango ingest report written: {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
