#!/usr/bin/env python3
"""Ingest AutoMathText-V2 Alexandria theorem-context JSONL into ArangoDB.

This loader is for the generic `automath_*` epistemic ancestry graph emitted by
`automathtext_v2_ingest.py`, not the older demo `alexandria_*` schema handled by
`arango_ingest.py`.

It preserves the layered sidecar boundary: raw fragments/chunks/entities/expression
nodes/theorem-shapes/overlay nodes are document collections; triples, De Bruijn
expression edges, ancestry edges, and overlay edges are edge collections.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.alexandria.arango_ingest import (  # noqa: E402
    ensure_collection,
    ensure_database,
    ensure_index,
    import_rows,
)
from tools.infra.arango_env import (  # noqa: E402
    alexandria_arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)

DOCUMENT_COLLECTIONS = [
    "automath_fragments",
    "automath_chunks",
    "automath_entities",
    "automath_expr_nodes",
    "automath_theorem_shapes",
    "automath_overlay_nodes",
]

EDGE_COLLECTIONS = [
    "automath_triples",
    "automath_expr_edges",
    "automath_ancestry_edges",
    "automath_overlay_edges",
]

INDEXES: dict[str, list[list[str]]] = {
    "automath_fragments": [
        ["source_dataset"],
        ["source_config"],
        ["source_domain"],
        ["source_id"],
        ["url"],
        ["text_hash"],
        ["ancestry_hash"],
        ["parent_id"],
        ["ingestion_run_id"],
    ],
    "automath_chunks": [
        ["fragment_key"],
        ["source_fragment"],
        ["chunkKind"],
        ["text_hash"],
        ["theorem_like_score"],
        ["proof_like_score"],
        ["ancestry_hash"],
        ["parent_ancestry_hash"],
        ["ancestry_path[*]"],
        ["ingestion_run_id"],
    ],
    "automath_entities": [
        ["entityType"],
        ["normalized"],
        ["surface"],
        ["source_fragment"],
        ["source_chunk"],
        ["ancestry_hash"],
        ["parent_ancestry_hash"],
    ],
    "automath_expr_nodes": [
        ["nodeKind"],
        ["chunk_key"],
        ["source_chunk"],
        ["source_fragment"],
        ["binderDepth"],
        ["deBruijnIdx"],
        ["ancestry_hash"],
        ["parent_ancestry_hash"],
    ],
    "automath_theorem_shapes": [
        ["source_chunk"],
        ["source_fragment"],
        ["formal_system"],
        ["head_symbol"],
        ["alpha_hash"],
        ["formula_hash"],
        ["entity_keys[*]"],
        ["ancestry_hash"],
        ["parent_ancestry_hash"],
        ["ancestry_path[*]"],
    ],
    "automath_overlay_nodes": [
        ["overlay_kind"],
        ["representative"],
        ["ancestry_hash"],
    ],
    "automath_triples": [
        ["predicate"],
        ["source_fragment"],
        ["source_chunk"],
        ["authority"],
        ["extraction_method"],
        ["ancestry_hash"],
        ["parent_ancestry_hash"],
        ["ancestry_path[*]"],
    ],
    "automath_expr_edges": [
        ["predicate"],
        ["relationType"],
        ["source_chunk"],
        ["source_fragment"],
        ["deBruijnIdx"],
        ["binderDepth"],
        ["authority"],
        ["ancestry_hash"],
    ],
    "automath_ancestry_edges": [
        ["role"],
        ["source_ancestry_hash"],
        ["target_ancestry_hash"],
        ["authority"],
        ["ancestry_hash"],
        ["parent_ancestry_hash"],
    ],
    "automath_overlay_edges": [
        ["role"],
        ["authority"],
        ["witness_chunk_keys[*]"],
        ["ancestry_hash"],
        ["parent_ancestry_hash"],
    ],
}

ALL_COLLECTIONS = DOCUMENT_COLLECTIONS + EDGE_COLLECTIONS


@dataclass(frozen=True)
class ImportPlanRow:
    collection: str
    path: Path
    edge: bool
    count: int
    present: bool

    def to_json(self) -> dict[str, Any]:
        return {
            "collection": self.collection,
            "path": self.path.as_posix(),
            "edge": self.edge,
            "count": self.count,
            "present": self.present,
        }


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def count_jsonl(path: Path) -> int:
    if not path.exists():
        return 0
    with path.open("r", encoding="utf-8") as handle:
        return sum(1 for line in handle if line.strip())


def build_import_plan(input_dir: Path) -> list[ImportPlanRow]:
    rows: list[ImportPlanRow] = []
    for collection in ALL_COLLECTIONS:
        path = input_dir / f"{collection}.jsonl"
        rows.append(
            ImportPlanRow(
                collection=collection,
                path=path,
                edge=collection in EDGE_COLLECTIONS,
                count=count_jsonl(path),
                present=path.exists(),
            )
        )
    return rows


def validate_edge_endpoints(rows: Iterable[dict[str, Any]], *, collection: str, offset: int = 0) -> None:
    for idx, row in enumerate(rows, start=1 + offset):
        if not row.get("_from") or not row.get("_to"):
            raise ValueError(f"Edge collection {collection} row {idx} is missing _from/_to: {row.get('_key', '<no-key>')}")


def batched_jsonl(path: Path, *, batch_size: int) -> Iterable[list[dict[str, Any]]]:
    batch: list[dict[str, Any]] = []
    for row in iter_jsonl(path):
        batch.append(row)
        if len(batch) >= batch_size:
            yield batch
            batch = []
    if batch:
        yield batch


def import_collection_batched(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    collection: str,
    path: Path,
    *,
    edge: bool,
    batch_size: int,
) -> dict[str, Any]:
    imported = 0
    batches = 0
    for payload in batched_jsonl(path, batch_size=batch_size):
        if edge:
            validate_edge_endpoints(payload, collection=collection, offset=imported)
        import_rows(endpoint, database, username, password, collection, payload)
        imported += len(payload)
        batches += 1
    return {"collection": collection, "count": imported, "edge": edge, "batches": batches, "batch_size": batch_size}


def import_automath_graph(
    *,
    input_dir: Path,
    endpoint: str,
    database: str,
    username: str,
    password: str,
    dry_run: bool,
    skip_indexes: bool,
    require_all: bool,
    json_out: Path | None = None,
    batch_size: int = 5000,
) -> dict[str, Any]:
    plan = build_import_plan(input_dir)
    missing = [row.collection for row in plan if not row.present]
    if require_all and missing:
        raise FileNotFoundError(f"Missing required AutoMathText JSONL collections under {input_dir}: {', '.join(missing)}")

    report: dict[str, Any] = {
        "schema": "info_geometry.alexandria.automathtext_arango_ingest.v1",
        "input_dir": input_dir.as_posix(),
        "endpoint": endpoint,
        "database": database,
        "dry_run": dry_run,
        "authority": "graph_context_only_not_proof_authority",
        "document_collections": DOCUMENT_COLLECTIONS,
        "edge_collections": EDGE_COLLECTIONS,
        "collections": [row.to_json() for row in plan],
        "missing_collections": missing,
        "batch_size": batch_size,
        "imported": [],
    }

    if dry_run:
        if json_out:
            json_out.parent.mkdir(parents=True, exist_ok=True)
            json_out.write_text(json.dumps(report, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        return report

    if batch_size <= 0:
        raise ValueError(f"batch_size must be positive, got {batch_size}")

    ensure_database(endpoint, database, username, password)
    for name in DOCUMENT_COLLECTIONS:
        ensure_collection(endpoint, database, username, password, name, edge=False)
    for name in EDGE_COLLECTIONS:
        ensure_collection(endpoint, database, username, password, name, edge=True)
    if not skip_indexes:
        for collection, fields_list in INDEXES.items():
            for fields in fields_list:
                ensure_index(endpoint, database, username, password, collection, fields)

    for row in plan:
        if not row.present or row.count == 0:
            continue
        report["imported"].append(
            import_collection_batched(
                endpoint,
                database,
                username,
                password,
                row.collection,
                row.path,
                edge=row.edge,
                batch_size=batch_size,
            )
        )

    if json_out:
        json_out.parent.mkdir(parents=True, exist_ok=True)
        json_out.write_text(json.dumps(report, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", required=True, type=Path)
    parser.add_argument("--endpoint", default=alexandria_arango_endpoint())
    parser.add_argument("--database", default="alexandria")
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password("alexandria_root"))
    parser.add_argument("--dry-run", action="store_true", help="Only report collection presence/counts; do not touch ArangoDB.")
    parser.add_argument("--skip-indexes", action="store_true", help="Create/import collections but skip persistent index creation.")
    parser.add_argument("--require-all", action="store_true", help="Fail if any automath_* JSONL collection is missing.")
    parser.add_argument("--json-out", type=Path, help="Optional report path.")
    parser.add_argument("--batch-size", type=int, default=5000, help="Rows per Arango import request; keep bounded for large automath_triples files.")
    return parser.parse_args()


def main() -> int:
    load_repo_arango_env(Path.cwd())
    args = parse_args()
    report = import_automath_graph(
        input_dir=args.input_dir,
        endpoint=args.endpoint,
        database=args.database,
        username=args.username,
        password=args.password,
        dry_run=bool(args.dry_run),
        skip_indexes=bool(args.skip_indexes),
        require_all=bool(args.require_all),
        json_out=args.json_out,
        batch_size=int(args.batch_size),
    )
    print(json.dumps(report, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
