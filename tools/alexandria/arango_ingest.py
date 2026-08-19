#!/usr/bin/env python3
from __future__ import annotations

import argparse
import base64
import json
from pathlib import Path
from typing import Any
from urllib.parse import quote
from urllib.request import Request, urlopen

from arango import ArangoClient
from tools.infra.arango_env import (
    alexandria_arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)

DOCUMENT_COLLECTIONS = [
    "alexandria_documents",
    "alexandria_sections",
    "alexandria_chunks",
    "alexandria_entities",
]
EDGE_COLLECTIONS = [
    "alexandria_document_section_edges",
    "alexandria_section_chunk_edges",
    "alexandria_chunk_entity_edges",
    "alexandria_chunk_adjacent_edges",
    "alexandria_entity_relation_edges",
]
INDEXES: dict[str, list[list[str]]] = {
    "alexandria_documents": [["path"], ["title"]],
    "alexandria_sections": [["documentKey"], ["title"]],
    "alexandria_chunks": [["documentKey"], ["sectionKey"], ["chunkKind"], ["tokens[*]"]],
    "alexandria_entities": [["chunkKey"], ["entityType"], ["surface"]],
}


def auth_header(username: str, password: str) -> str:
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"


def request_json(method: str, url: str, username: str, password: str, payload: Any | None = None) -> Any:
    body = None if payload is None else json.dumps(payload).encode("utf-8")
    req = Request(url, data=body, method=method)
    req.add_header("Authorization", auth_header(username, password))
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", "application/json")
    with urlopen(req) as resp:
        raw = resp.read().decode("utf-8")
        return json.loads(raw) if raw else {}


def sys_url(endpoint: str, path: str) -> str:
    return f"{endpoint.rstrip('/')}/{path.lstrip('/')}"


def db_url(endpoint: str, database: str, path: str) -> str:
    return f"{endpoint.rstrip('/')}/_db/{quote(database)}/{path.lstrip('/')}"


def ensure_database(endpoint: str, database: str, username: str, password: str) -> None:
    dbs = request_json("GET", sys_url(endpoint, "/_api/database"), username, password)
    if database in dbs.get("result", []):
        return
    request_json("POST", sys_url(endpoint, "/_api/database"), username, password, {"name": database})


def ensure_collection(endpoint: str, database: str, username: str, password: str, name: str, edge: bool) -> None:
    current = request_json("GET", db_url(endpoint, database, "/_api/collection"), username, password)
    names = {row.get("name") for row in current.get("result", []) if isinstance(row, dict)}
    if name in names:
        return
    request_json(
        "POST",
        db_url(endpoint, database, "/_api/collection"),
        username,
        password,
        {"name": name, "type": 3 if edge else 2},
    )


def ensure_index(endpoint: str, database: str, username: str, password: str, collection: str, fields: list[str]) -> None:
    payload = {"type": "persistent", "fields": fields, "unique": False, "sparse": True}
    request_json("POST", db_url(endpoint, database, f"/_api/index?collection={quote(collection)}"), username, password, payload)


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def import_rows(endpoint: str, database: str, username: str, password: str, collection: str, rows: list[dict[str, Any]]) -> None:
    if not rows:
        return
    client = ArangoClient(hosts=endpoint)
    db = client.db(database, username=username, password=password)
    col = db.collection(collection)
    col.import_bulk(rows, on_duplicate="replace", batch_size=1000)


def main() -> int:
    load_repo_arango_env(Path.cwd())
    ap = argparse.ArgumentParser(description="Ingest Alexandria JSONL artifacts into a second ArangoDB instance")
    ap.add_argument("--input-dir", required=True)
    ap.add_argument("--endpoint", default=alexandria_arango_endpoint())
    ap.add_argument("--database", default="alexandria")
    ap.add_argument("--username", default=arango_username())
    ap.add_argument("--password", default=arango_password("alexandria_root"))
    args = ap.parse_args()

    input_dir = Path(args.input_dir)
    ensure_database(args.endpoint, args.database, args.username, args.password)
    for name in DOCUMENT_COLLECTIONS:
        ensure_collection(args.endpoint, args.database, args.username, args.password, name, edge=False)
    for name in EDGE_COLLECTIONS:
        ensure_collection(args.endpoint, args.database, args.username, args.password, name, edge=True)
    for collection, fields_list in INDEXES.items():
        for fields in fields_list:
            ensure_index(args.endpoint, args.database, args.username, args.password, collection, fields)
    for collection in DOCUMENT_COLLECTIONS + EDGE_COLLECTIONS:
        path = input_dir / f"{collection}.jsonl"
        if path.exists():
            import_rows(args.endpoint, args.database, args.username, args.password, collection, list(iter_jsonl(path)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
