#!/usr/bin/env python3
"""Initialize and ingest the isolated aiClaw proof-memory ArangoDB.

This intentionally avoids the repo theorem-DAG brain. By default it targets
http://127.0.0.1:8540 and database aiclaw_auto_rag. It refuses to write to
the common repo DAG endpoint/database unless --allow-shared-brain is passed.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlparse
from urllib.request import Request, urlopen


DEFAULT_URL = "http://127.0.0.1:8540"
DEFAULT_DB = "aiclaw_auto_rag"
DEFAULT_USER = "root"
DEFAULT_PASSWORD = "password"
DEFAULT_KB = Path("knowledge_base.json")
SHARED_DAG_DATABASES = {"infogeometry", "hive_live"}
LOOPBACK_HOSTS = {"127.0.0.1", "localhost", "::1", "0:0:0:0:0:0:0:1"}


def env(name: str, default: str) -> str:
    return os.environ.get(name, default)


def safe_key(value: str) -> str:
    value = re.sub(r"[^A-Za-z0-9_-]+", "_", value.strip())
    value = value.strip("_-")
    if not value:
        value = hashlib.sha256(b"empty").hexdigest()[:16]
    return value[:240]


def auth_header(user: str, password: str) -> str:
    token = base64.b64encode(f"{user}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"


def request_json(
    method: str,
    url: str,
    user: str,
    password: str,
    payload: dict[str, Any] | None = None,
    *,
    tolerate: set[int] | None = None,
) -> Any:
    tolerate = tolerate or set()
    data = None if payload is None else json.dumps(payload).encode("utf-8")
    req = Request(url, data=data, method=method)
    req.add_header("Authorization", auth_header(user, password))
    req.add_header("Content-Type", "application/json")
    try:
        with urlopen(req, timeout=10) as response:
            raw = response.read().decode("utf-8")
            return json.loads(raw) if raw else {}
    except HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        if exc.code in tolerate:
            try:
                return json.loads(raw) if raw else {"error": True, "code": exc.code}
            except json.JSONDecodeError:
                return {"error": True, "code": exc.code, "raw": raw}
        raise RuntimeError(f"{method} {url} failed with HTTP {exc.code}: {raw}") from exc
    except URLError as exc:
        raise RuntimeError(f"{method} {url} failed: {exc}") from exc


def arango_parts(url: str) -> tuple[str | None, int | None]:
    parsed = urlparse(url if "://" in url else f"http://{url}")
    return parsed.hostname, parsed.port


def guard_separate_brain(url: str, database: str, allow_shared: bool) -> None:
    if allow_shared:
        return
    host, port = arango_parts(url)
    shared_endpoint = (host or "").lower() in LOOPBACK_HOSTS and port == 8530
    shared_database = database.lower() in SHARED_DAG_DATABASES
    if shared_endpoint or shared_database:
        raise SystemExit(
            "Refusing to write to the repo DAG brain. Use AICLAW_ARANGO_URL on a separate "
            "port/database, or pass --allow-shared-brain if you really intend this."
        )


def db_url(base: str, database: str, suffix: str) -> str:
    return f"{base.rstrip('/')}/_db/{quote(database)}/{suffix.lstrip('/')}"


def create_database(base: str, database: str, user: str, password: str) -> None:
    request_json(
        "POST",
        f"{base.rstrip('/')}/_api/database",
        user,
        password,
        {"name": database},
        tolerate={409},
    )


def ensure_collection(base: str, database: str, user: str, password: str, name: str, edge: bool = False) -> None:
    payload = {"name": name, "type": 3 if edge else 2}
    request_json(
        "POST",
        db_url(base, database, "/_api/collection"),
        user,
        password,
        payload,
        tolerate={409},
    )


def ensure_index(base: str, database: str, user: str, password: str, collection: str, fields: list[str]) -> None:
    request_json(
        "POST",
        db_url(base, database, f"/_api/index?collection={quote(collection)}"),
        user,
        password,
        {"type": "persistent", "fields": fields, "sparse": True},
        tolerate={409},
    )


def ensure_view(base: str, database: str, user: str, password: str) -> None:
    payload = {
        "name": "literature_search_view",
        "type": "arangosearch",
        "links": {
            "literature_nodes": {
                "includeAllFields": True,
                "fields": {
                    "embedding": {"analyzers": ["identity"]},
                    "title": {"analyzers": ["text_en"]},
                    "content": {"analyzers": ["text_en"]},
                },
            }
        },
    }
    request_json(
        "POST",
        db_url(base, database, "/_api/view"),
        user,
        password,
        payload,
        tolerate={409},
    )


def init_schema(args: argparse.Namespace) -> None:
    guard_separate_brain(args.url, args.database, args.allow_shared_brain)
    if args.dry_run:
        print(f"dry-run: would initialize {args.url} database {args.database}")
        return
    request_json("GET", f"{args.url.rstrip('/')}/_api/version", args.user, args.password)
    create_database(args.url, args.database, args.user, args.password)
    ensure_collection(args.url, args.database, args.user, args.password, "literature_nodes")
    ensure_collection(args.url, args.database, args.user, args.password, "citation_edges", edge=True)
    for fields in (["title"], ["source"], ["status"], ["id"]):
        ensure_index(args.url, args.database, args.user, args.password, "literature_nodes", fields)
    try:
        ensure_view(args.url, args.database, args.user, args.password)
    except RuntimeError as exc:
        print(f"warning: ArangoSearch view setup failed, keyword search still works: {exc}", file=sys.stderr)
    print(f"initialized isolated aiClaw ArangoDB: {args.url} / {args.database}")


def load_kb(path: Path) -> list[dict[str, Any]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(data, list):
        return [entry for entry in data if isinstance(entry, dict)]
    if isinstance(data, dict):
        return [data]
    raise ValueError(f"Unsupported knowledge base shape: {path}")


def upsert_doc(base: str, database: str, user: str, password: str, key: str, doc: dict[str, Any]) -> None:
    request_json(
        "PUT",
        db_url(base, database, f"/_api/document/literature_nodes/{quote(key)}?overwriteMode=update"),
        user,
        password,
        {**doc, "_key": key},
    )


def upsert_edge(base: str, database: str, user: str, password: str, edge: dict[str, Any]) -> None:
    key_source = f"{edge.get('_from')}->{edge.get('_to')}:{edge.get('type')}"
    key = safe_key(hashlib.sha256(key_source.encode("utf-8")).hexdigest())
    request_json(
        "PUT",
        db_url(base, database, f"/_api/document/citation_edges/{quote(key)}?overwriteMode=update"),
        user,
        password,
        {**edge, "_key": key},
    )


def ingest(args: argparse.Namespace) -> None:
    guard_separate_brain(args.url, args.database, args.allow_shared_brain)
    entries = load_kb(Path(args.source))
    if args.dry_run:
        print(f"dry-run: would ingest {len(entries)} entries into {args.url} / {args.database}")
        return
    init_schema(args)
    now = datetime.now(timezone.utc).isoformat()
    count = 0
    edge_count = 0
    for index, entry in enumerate(entries):
        raw_key = str(entry.get("id") or entry.get("_key") or entry.get("title") or f"entry_{index:04d}")
        key = safe_key(raw_key)
        doc = dict(entry)
        doc.setdefault("ingested_by", "aiclaw_auto_arango.py")
        doc["aiclaw_ingested_at"] = now
        upsert_doc(args.url, args.database, args.user, args.password, key, doc)
        count += 1
        for inspiration in entry.get("inspiring_nodes") or []:
            target = safe_key(str(inspiration))
            edge = {
                "_from": f"literature_nodes/{key}",
                "_to": f"literature_nodes/{target}",
                "type": "derived_from_unconscious_literature",
                "created_at": now,
            }
            upsert_edge(args.url, args.database, args.user, args.password, edge)
            edge_count += 1
    print(f"ingested {count} nodes and {edge_count} edges into {args.url} / {args.database}")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--url", default=env("AICLAW_ARANGO_URL", DEFAULT_URL))
    parser.add_argument("--database", default=env("AICLAW_ARANGO_DB", DEFAULT_DB))
    parser.add_argument("--user", default=env("AICLAW_ARANGO_USER", DEFAULT_USER))
    parser.add_argument("--password", default=env("AICLAW_ARANGO_PASSWORD", DEFAULT_PASSWORD))
    parser.add_argument("--allow-shared-brain", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("init")
    ingest_parser = sub.add_parser("ingest")
    ingest_parser.add_argument("--source", default=str(Path(env("AICLAW_KNOWLEDGE_BASE", str(DEFAULT_KB)))))
    return parser


def main() -> int:
    args = build_parser().parse_args()
    if args.command == "init":
        init_schema(args)
    elif args.command == "ingest":
        ingest(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
