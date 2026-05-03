"""Arango graph registry and query helpers for igf."""

from igf.graph.arango_client import connect_db, ensure_collections_and_indexes
from igf.graph.arango_http import (
    ArangoHttpTarget,
    auth_header,
    collection_count,
    create_collection,
    db_url,
    drop_collection,
    ensure_database,
    ensure_index,
    execute_aql,
    import_jsonl,
    list_collections,
    request_json,
    request_raw,
    sys_url,
    target_from_config,
    truncate_collection,
)
from igf.graph.query_runner import resolve_run_id, run_query

__all__ = [
    "ArangoHttpTarget",
    "auth_header",
    "collection_count",
    "connect_db",
    "create_collection",
    "db_url",
    "drop_collection",
    "ensure_database",
    "ensure_collections_and_indexes",
    "ensure_index",
    "execute_aql",
    "import_jsonl",
    "list_collections",
    "request_json",
    "request_raw",
    "resolve_run_id",
    "run_query",
    "sys_url",
    "target_from_config",
    "truncate_collection",
]
