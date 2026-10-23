#!/usr/bin/env python3
"""Ingest Alexandria JSONL artifacts into ArangoDB and maintain its BM25 view.

Records are retrieval/navigation context only, never proof evidence.

Improvements over the original importer:
- uses the repo HTTP client (``igf.graph.arango_http``) instead of the
  optional ``python-arango`` package, which is not installed by default;
- ``--replace-documents`` removes a document's previous sections, chunks,
  entities and edges before importing, so edited files leave no stale chunks;
- ``--skip-unchanged`` skips documents whose ``contentHash`` is unchanged;
- maintains the ``alexandria_chunks_search`` ArangoSearch view (BM25 over
  ``text``/``title``, exact match on identifier pieces in ``searchTerms``).
"""
from __future__ import annotations

import argparse
import base64
import json
import sys
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import quote
from urllib.request import Request, urlopen

REPO_ROOT = Path(__file__).resolve().parents[2]
for _p in (REPO_ROOT, REPO_ROOT / "src"):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

from tools.alexandria.structural_chunking import ident_terms  # noqa: E402
from tools.infra.arango_env import (  # noqa: E402
    alexandria_arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from igf.graph.arango_http import ArangoHttpTarget, execute_aql, import_jsonl  # noqa: E402

SEARCH_VIEW = "alexandria_chunks_search"
IMPORT_BATCH_ROWS = 2000
CODE_SOURCE_FORMATS = {"lean_source", "lean_ast", "python_ast", "python"}

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
    "alexandria_entity_relation_edges": [["chunkKey"]],
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


def _target(endpoint: str, database: str, username: str, password: str) -> ArangoHttpTarget:
    return ArangoHttpTarget(endpoint.rstrip("/"), database, username, password)


def import_rows(endpoint: str, database: str, username: str, password: str, collection: str, rows: list[dict[str, Any]]) -> None:
    """Bulk import with ``onDuplicate=replace`` (signature kept for txt2kg)."""
    if not rows:
        return
    target = _target(endpoint, database, username, password)
    for start in range(0, len(rows), IMPORT_BATCH_ROWS):
        batch = rows[start : start + IMPORT_BATCH_ROWS]
        payload = "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in batch).encode("utf-8")
        result = import_jsonl(target, collection, payload, on_duplicate="replace", complete=True)
        if result.get("error"):
            raise RuntimeError(f"import into {collection} failed: {result}")


def search_view_definition() -> dict[str, Any]:
    identity = {"analyzers": ["identity"]}
    return {
        "links": {
            "alexandria_chunks": {
                "includeAllFields": False,
                "fields": {
                    "text": {"analyzers": ["text_en"]},
                    "title": {"analyzers": ["text_en", "identity"]},
                    "searchTerms": identity,
                    "chunkKind": identity,
                    "documentKey": identity,
                    "provenance": {
                        "fields": {
                            "path": identity,
                            "declName": identity,
                            "sourceFormat": identity,
                            "sourceKind": identity,
                        }
                    },
                },
            }
        }
    }


def ensure_search_view(endpoint: str, database: str, username: str, password: str, name: str = SEARCH_VIEW) -> str:
    """Create or update the BM25 ArangoSearch view over ``alexandria_chunks``."""
    definition = search_view_definition()
    views = request_json("GET", db_url(endpoint, database, "/_api/view"), username, password)
    names = {row.get("name") for row in views.get("result", []) if isinstance(row, dict)}
    if name in names:
        request_json(
            "PUT", db_url(endpoint, database, f"/_api/view/{quote(name)}/properties"), username, password, definition
        )
        return "updated"
    request_json(
        "POST", db_url(endpoint, database, "/_api/view"), username, password,
        {"name": name, "type": "arangosearch", **definition},
    )
    return "created"


def add_search_terms(row: dict[str, Any]) -> dict[str, Any]:
    """Attach identifier pieces (dots/underscores/camelCase split) to a chunk row."""
    provenance = row.get("provenance") if isinstance(row.get("provenance"), dict) else {}
    parts = [str(row.get("title", "")), str(provenance.get("declName") or "")]
    if provenance.get("sourceFormat") in CODE_SOURCE_FORMATS or "`" in str(row.get("text", "")):
        parts.append(str(row.get("text", "")))
    row["searchTerms"] = ident_terms("\n".join(parts))
    return row


def existing_content_hashes(target: ArangoHttpTarget, keys: list[str]) -> dict[str, str]:
    if not keys:
        return {}
    rows = execute_aql(
        target,
        "FOR d IN alexandria_documents FILTER d._key IN @keys RETURN [d._key, d.contentHash]",
        {"keys": keys},
        timeout=300,
    )
    return {key: value for key, value in rows if value}


REMOVE_DOCUMENT_QUERIES = [
    "FOR c IN alexandria_chunks FILTER c.documentKey IN @docs "
    "FOR e IN alexandria_chunk_entity_edges FILTER e._from == c._id REMOVE e IN alexandria_chunk_entity_edges",
    "FOR c IN alexandria_chunks FILTER c.documentKey IN @docs "
    "FOR e IN alexandria_chunk_adjacent_edges FILTER e._from == c._id REMOVE e IN alexandria_chunk_adjacent_edges",
    "FOR c IN alexandria_chunks FILTER c.documentKey IN @docs "
    "FOR e IN alexandria_chunk_adjacent_edges FILTER e._to == c._id REMOVE e IN alexandria_chunk_adjacent_edges",
    "FOR c IN alexandria_chunks FILTER c.documentKey IN @docs "
    "FOR e IN alexandria_section_chunk_edges FILTER e._to == c._id REMOVE e IN alexandria_section_chunk_edges",
    "FOR c IN alexandria_chunks FILTER c.documentKey IN @docs "
    "FOR r IN alexandria_entity_relation_edges FILTER r.chunkKey == c._key REMOVE r IN alexandria_entity_relation_edges",
    "FOR c IN alexandria_chunks FILTER c.documentKey IN @docs "
    "FOR en IN alexandria_entities FILTER en.chunkKey == c._key REMOVE en IN alexandria_entities",
    "FOR c IN alexandria_chunks FILTER c.documentKey IN @docs REMOVE c IN alexandria_chunks",
    "FOR s IN alexandria_sections FILTER s.documentKey IN @docs REMOVE s IN alexandria_sections",
    "FOR e IN alexandria_document_section_edges FILTER e._from IN @docIds REMOVE e IN alexandria_document_section_edges",
]


def remove_documents(target: ArangoHttpTarget, document_keys: list[str], batch: int = 200) -> None:
    """Delete everything previously ingested for these documents (not the document rows)."""
    for start in range(0, len(document_keys), batch):
        docs = document_keys[start : start + batch]
        bind = {"docs": docs, "docIds": [f"alexandria_documents/{key}" for key in docs]}
        for query in REMOVE_DOCUMENT_QUERIES:
            needed = {k: v for k, v in bind.items() if f"@{k}" in query}
            execute_aql(target, query, needed, timeout=600)


def _ref_key(ref: Any) -> str:
    return str(ref).split("/", 1)[-1] if ref else ""


def drop_rows_for_documents(rows_by_collection: dict[str, list[dict[str, Any]]], skip_docs: set[str]) -> None:
    """Remove rows belonging to ``skip_docs`` from a loaded artifact set, in place."""
    if not skip_docs:
        return
    chunk_rows = rows_by_collection.get("alexandria_chunks", [])
    skip_chunks = {row["_key"] for row in chunk_rows if row.get("documentKey") in skip_docs}
    skip_sections = {
        row["_key"] for row in rows_by_collection.get("alexandria_sections", []) if row.get("documentKey") in skip_docs
    }
    skip_entities = {
        row["_key"] for row in rows_by_collection.get("alexandria_entities", []) if row.get("chunkKey") in skip_chunks
    }
    skip_all = skip_docs | skip_chunks | skip_sections | skip_entities
    for collection, rows in rows_by_collection.items():
        rows_by_collection[collection] = [
            row
            for row in rows
            if row.get("_key") not in skip_all
            and _ref_key(row.get("_from")) not in skip_all
            and _ref_key(row.get("_to")) not in skip_all
        ]


def load_artifacts(input_dir: Path, collections: Iterable[str]) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = {}
    for collection in collections:
        path = input_dir / f"{collection}.jsonl"
        if path.exists():
            out[collection] = list(iter_jsonl(path))
    return out


def main() -> int:
    load_repo_arango_env(Path.cwd())
    ap = argparse.ArgumentParser(description="Ingest Alexandria JSONL artifacts into a second ArangoDB instance")
    ap.add_argument("--input-dir", help="semantic_ingest output directory (omit with --search-view-only)")
    ap.add_argument("--endpoint", default=alexandria_arango_endpoint())
    ap.add_argument("--database", default="alexandria")
    ap.add_argument("--username", default=arango_username())
    ap.add_argument("--password", default=arango_password("alexandria_root"))
    ap.add_argument("--replace-documents", action="store_true",
                    help="delete previously ingested sections/chunks/entities/edges of each input document first")
    ap.add_argument("--skip-unchanged", action="store_true",
                    help="skip documents whose stored contentHash equals the artifact contentHash")
    ap.add_argument("--no-search-view", action="store_true", help="do not create/update the BM25 search view")
    ap.add_argument("--search-view-only", action="store_true", help="only create/update the BM25 search view")
    args = ap.parse_args()
    conn = (args.endpoint, args.database, args.username, args.password)

    if args.search_view_only:
        print(json.dumps({"searchView": SEARCH_VIEW, "status": ensure_search_view(*conn)}))
        return 0
    if not args.input_dir:
        ap.error("--input-dir is required unless --search-view-only is given")

    input_dir = Path(args.input_dir)
    ensure_database(*conn)
    for name in DOCUMENT_COLLECTIONS:
        ensure_collection(*conn, name, edge=False)
    for name in EDGE_COLLECTIONS:
        ensure_collection(*conn, name, edge=True)
    for collection, fields_list in INDEXES.items():
        for fields in fields_list:
            ensure_index(*conn, collection, fields)

    rows = load_artifacts(input_dir, DOCUMENT_COLLECTIONS + EDGE_COLLECTIONS)
    target = _target(*conn)
    documents = rows.get("alexandria_documents", [])
    skipped: set[str] = set()
    if args.skip_unchanged:
        stored = existing_content_hashes(target, [row["_key"] for row in documents])
        skipped = {
            row["_key"] for row in documents if row.get("contentHash") and stored.get(row["_key"]) == row["contentHash"]
        }
        drop_rows_for_documents(rows, skipped)
    if args.replace_documents:
        remove_documents(target, [row["_key"] for row in rows.get("alexandria_documents", [])])
    rows["alexandria_chunks"] = [add_search_terms(row) for row in rows.get("alexandria_chunks", [])]
    for collection in DOCUMENT_COLLECTIONS + EDGE_COLLECTIONS:
        import_rows(*conn, collection, rows.get(collection, []))

    summary: dict[str, Any] = {
        "documents": len(documents),
        "skippedUnchanged": len(skipped),
        "imported": {name: len(value) for name, value in rows.items() if value},
    }
    if not args.no_search_view:
        summary["searchView"] = {SEARCH_VIEW: ensure_search_view(*conn)}
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
