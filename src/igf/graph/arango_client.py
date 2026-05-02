from __future__ import annotations

from typing import Any

from igf.config.model import ArangoConfig

from .collections import EDGE_COLLECTIONS, VERTEX_COLLECTIONS
from .indexes import INDEXES


def connect_db(config: ArangoConfig) -> Any:
    try:
        from arango import ArangoClient
    except Exception as exc:  # pragma: no cover - depends on optional runtime package
        raise RuntimeError(
            "python-arango is required for igf ingest/verify; install python-arango"
        ) from exc

    client = ArangoClient(hosts=config.endpoint)
    return client.db(config.database, username=config.user, password=config.password)


def ensure_collections_and_indexes(db: Any) -> None:
    for name in sorted(VERTEX_COLLECTIONS):
        if not db.has_collection(name):
            db.create_collection(name)

    for name in sorted(EDGE_COLLECTIONS):
        if not db.has_collection(name):
            db.create_collection(name, edge=True)

    for collection, specs in INDEXES.items():
        col = db.collection(collection)
        for spec in specs:
            try:
                col.add_persistent_index(
                    fields=list(spec["fields"]),
                    unique=bool(spec.get("unique", False)),
                )
            except Exception:
                # Existing indexes and Arango version differences should not make
                # idempotent preflight/ingest fail.
                continue

