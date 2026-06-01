#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
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
from igf.graph import (
    ArangoHttpTarget,
    collection_count,
    create_collection,
    ensure_database,
    import_jsonl,
    list_collections,
    truncate_collection,
)


@dataclass
class ArangoTarget:
    endpoint: str
    database: str
    username: str
    password: str
    nodes_collection: str
    edges_collection: str


def _ensure_collections(target: ArangoTarget, *, drop_existing: bool) -> None:
    http_target = _http_target(target)
    collections = list_collections(http_target)

    for name, edge in ((target.nodes_collection, False), (target.edges_collection, True)):
        if name not in collections:
            create_collection(http_target, name, edge=edge)
            continue
        if drop_existing:
            truncate_collection(http_target, name)


def _read_text(path: Path) -> bytes:
    if not path.exists():
        raise FileNotFoundError(f"Input file not found: {path}")
    return path.read_bytes()


def _http_target(target: ArangoTarget) -> ArangoHttpTarget:
    return ArangoHttpTarget(
        endpoint=target.endpoint.rstrip("/"),
        database=target.database,
        username=target.username,
        password=target.password,
    )


def _import_jsonl(target: ArangoTarget, collection: str, payload: bytes) -> dict[str, Any]:
    return import_jsonl(_http_target(target), collection, payload)


def _collection_count(target: ArangoTarget, collection: str) -> int:
    return collection_count(_http_target(target), collection)


def _parse_args() -> argparse.Namespace:
    load_repo_arango_env()
    parser = argparse.ArgumentParser(
        description="Ingest LeanTrail Arango JSONL exports into ArangoDB collections."
    )
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password("alexandria_root"))
    parser.add_argument("--input-dir", default="artifacts/leantrail/arango")
    parser.add_argument("--nodes-collection", default="ig_nodes")
    parser.add_argument("--edges-collection", default="ig_edges")
    parser.add_argument("--drop-existing", action="store_true")
    parser.add_argument(
        "--json-out",
        default="artifacts/leantrail/arango_ingest_report.json",
        help="Write ingest report JSON here.",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()

    target = ArangoTarget(
        endpoint=str(args.endpoint).rstrip("/"),
        database=str(args.database),
        username=str(args.username),
        password=str(args.password),
        nodes_collection=str(args.nodes_collection),
        edges_collection=str(args.edges_collection),
    )

    input_dir = Path(args.input_dir).resolve()
    nodes_path = input_dir / "ig_nodes.jsonl"
    edges_path = input_dir / "ig_edges.jsonl"

    ensure_database(_http_target(target))
    _ensure_collections(target, drop_existing=bool(args.drop_existing))

    nodes_import = _import_jsonl(target, target.nodes_collection, _read_text(nodes_path))
    edges_import = _import_jsonl(target, target.edges_collection, _read_text(edges_path))

    node_count = _collection_count(target, target.nodes_collection)
    edge_count = _collection_count(target, target.edges_collection)

    report = {
        "endpoint": target.endpoint,
        "database": target.database,
        "nodes_collection": target.nodes_collection,
        "edges_collection": target.edges_collection,
        "input_dir": str(input_dir),
        "imports": {
            "nodes": nodes_import,
            "edges": edges_import,
        },
        "counts": {
            "nodes": node_count,
            "edges": edge_count,
        },
    }

    out_path = Path(args.json_out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")

    print(f"Arango ingest report written: {out_path}")
    print(f"Counts: nodes={node_count} edges={edge_count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
