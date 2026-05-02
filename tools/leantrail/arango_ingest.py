#!/usr/bin/env python3
from __future__ import annotations

import argparse
import base64
import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.parse import quote
from urllib.request import Request, urlopen


@dataclass
class ArangoTarget:
    endpoint: str
    database: str
    username: str
    password: str
    nodes_collection: str
    edges_collection: str


def _auth_header(username: str, password: str) -> str:
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"


def _request_json(
    method: str,
    url: str,
    *,
    username: str,
    password: str,
    payload: dict[str, Any] | list[Any] | None = None,
    raw_body: bytes | None = None,
    content_type: str = "application/json",
) -> dict[str, Any]:
    body: bytes | None
    if raw_body is not None:
        body = raw_body
    elif payload is not None:
        body = json.dumps(payload, ensure_ascii=True).encode("utf-8")
    else:
        body = None

    req = Request(url, data=body, method=method)
    req.add_header("Authorization", _auth_header(username, password))
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", content_type)

    try:
        with urlopen(req) as resp:
            raw = resp.read().decode("utf-8")
            if not raw:
                return {}
            try:
                return json.loads(raw)
            except Exception:
                return {"raw": raw}
    except HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {url}: {raw}") from exc


def _db_url(target: ArangoTarget, path: str) -> str:
    return f"{target.endpoint}/_db/{quote(target.database)}/{path.lstrip('/')}"


def _sys_url(target: ArangoTarget, path: str) -> str:
    return f"{target.endpoint}/{path.lstrip('/')}"


def _ensure_database(target: ArangoTarget) -> None:
    dbs = _request_json(
        "GET",
        _sys_url(target, "/_api/database"),
        username=target.username,
        password=target.password,
    )
    names = dbs.get("result") if isinstance(dbs, dict) else None
    if isinstance(names, list) and target.database in names:
        return

    _request_json(
        "POST",
        _sys_url(target, "/_api/database"),
        username=target.username,
        password=target.password,
        payload={"name": target.database},
    )


def _list_collections(target: ArangoTarget) -> dict[str, dict[str, Any]]:
    payload = _request_json(
        "GET",
        _db_url(target, "/_api/collection"),
        username=target.username,
        password=target.password,
    )
    out: dict[str, dict[str, Any]] = {}
    for row in payload.get("result", []) if isinstance(payload, dict) else []:
        if isinstance(row, dict):
            name = str(row.get("name", "")).strip()
            if name:
                out[name] = row
    return out


def _create_collection(target: ArangoTarget, name: str, *, edge: bool) -> None:
    _request_json(
        "POST",
        _db_url(target, "/_api/collection"),
        username=target.username,
        password=target.password,
        payload={
            "name": name,
            "type": 3 if edge else 2,
            "waitForSync": False,
        },
    )


def _truncate_collection(target: ArangoTarget, name: str) -> None:
    _request_json(
        "PUT",
        _db_url(target, f"/_api/collection/{quote(name)}/truncate"),
        username=target.username,
        password=target.password,
    )


def _ensure_collections(target: ArangoTarget, *, drop_existing: bool) -> None:
    collections = _list_collections(target)

    for name, edge in ((target.nodes_collection, False), (target.edges_collection, True)):
        if name not in collections:
            _create_collection(target, name, edge=edge)
            continue
        if drop_existing:
            _truncate_collection(target, name)


def _read_text(path: Path) -> bytes:
    if not path.exists():
        raise FileNotFoundError(f"Input file not found: {path}")
    return path.read_bytes()


def _import_jsonl(target: ArangoTarget, collection: str, payload: bytes) -> dict[str, Any]:
    url = _db_url(
        target,
        f"/_api/import?collection={quote(collection)}&type=documents&onDuplicate=replace&complete=true",
    )
    return _request_json(
        "POST",
        url,
        username=target.username,
        password=target.password,
        raw_body=payload,
        content_type="application/json",
    )


def _collection_count(target: ArangoTarget, collection: str) -> int:
    out = _request_json(
        "GET",
        _db_url(target, f"/_api/collection/{quote(collection)}/count"),
        username=target.username,
        password=target.password,
    )
    if isinstance(out, dict):
        count = out.get("count")
        if isinstance(count, int):
            return count
    return -1


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Ingest LeanTrail Arango JSONL exports into ArangoDB collections."
    )
    parser.add_argument("--endpoint", default=os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8530"))
    parser.add_argument("--database", default=os.environ.get("ARANGO_DATABASE", "infogeometry"))
    parser.add_argument("--username", default=os.environ.get("ARANGO_USER") or os.environ.get("ARANGO_USERNAME", "root"))
    parser.add_argument("--password", default=os.environ.get("ARANGO_PASS") or os.environ.get("ARANGO_PASSWORD", "alexandria_root"))
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

    _ensure_database(target)
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
