from __future__ import annotations

import base64
import json
from dataclasses import dataclass
from typing import Any
from urllib.error import HTTPError
from urllib.parse import quote
from urllib.request import Request, urlopen

from igf.config.model import ArangoConfig


@dataclass(frozen=True)
class ArangoHttpTarget:
    endpoint: str
    database: str
    username: str
    password: str


def target_from_config(config: ArangoConfig) -> ArangoHttpTarget:
    return ArangoHttpTarget(
        endpoint=config.endpoint.rstrip("/"),
        database=config.database,
        username=config.user,
        password=config.password,
    )


def auth_header(username: str, password: str) -> str:
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"


def db_url(target: ArangoHttpTarget, path: str) -> str:
    return f"{target.endpoint}/_db/{quote(target.database)}/{path.lstrip('/')}"


def sys_url(target: ArangoHttpTarget, path: str) -> str:
    return f"{target.endpoint}/{path.lstrip('/')}"


def request_json(
    method: str,
    url: str,
    target: ArangoHttpTarget,
    payload: dict[str, Any] | None = None,
    *,
    timeout: float = 30,
) -> dict[str, Any]:
    body = json.dumps(payload, ensure_ascii=True).encode("utf-8") if payload is not None else None
    req = Request(url, data=body, method=method)
    req.add_header("Authorization", auth_header(target.username, target.password))
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", "application/json")

    try:
        with urlopen(req, timeout=timeout) as response:
            raw = response.read().decode("utf-8")
    except HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {url}: {raw}") from exc
    return json.loads(raw) if raw else {}


def request_raw(
    method: str,
    url: str,
    target: ArangoHttpTarget,
    body: bytes | None = None,
    *,
    content_type: str = "application/json",
    timeout: float = 30,
) -> dict[str, Any]:
    req = Request(url, data=body, method=method)
    req.add_header("Authorization", auth_header(target.username, target.password))
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", content_type)

    try:
        with urlopen(req, timeout=timeout) as response:
            raw = response.read().decode("utf-8")
    except HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {url}: {raw}") from exc
    if not raw:
        return {}
    try:
        return json.loads(raw)
    except Exception:
        return {"raw": raw}


def ensure_database(target: ArangoHttpTarget) -> None:
    dbs = request_json("GET", sys_url(target, "/_api/database"), target)
    names = dbs.get("result") if isinstance(dbs, dict) else None
    if isinstance(names, list) and target.database in names:
        return
    request_json("POST", sys_url(target, "/_api/database"), target, {"name": target.database})


def list_collections(target: ArangoHttpTarget) -> dict[str, dict[str, Any]]:
    payload = request_json("GET", db_url(target, "/_api/collection"), target)
    out: dict[str, dict[str, Any]] = {}
    for row in payload.get("result", []) if isinstance(payload, dict) else []:
        if isinstance(row, dict):
            name = str(row.get("name", "")).strip()
            if name:
                out[name] = row
    return out


def create_collection(target: ArangoHttpTarget, name: str, *, edge: bool = False) -> None:
    request_json(
        "POST",
        db_url(target, "/_api/collection"),
        target,
        {"name": name, "type": 3 if edge else 2, "waitForSync": False},
    )


def truncate_collection(target: ArangoHttpTarget, name: str) -> None:
    request_json("PUT", db_url(target, f"/_api/collection/{quote(name)}/truncate"), target)


def drop_collection(target: ArangoHttpTarget, name: str) -> None:
    request_json("DELETE", db_url(target, f"/_api/collection/{quote(name)}"), target)


def collection_count(target: ArangoHttpTarget, collection: str) -> int:
    out = request_json("GET", db_url(target, f"/_api/collection/{quote(collection)}/count"), target)
    count = out.get("count") if isinstance(out, dict) else None
    return count if isinstance(count, int) else -1


def ensure_index(
    target: ArangoHttpTarget,
    collection: str,
    fields: list[str],
    *,
    unique: bool = False,
    sparse: bool = True,
    name: str | None = None,
) -> dict[str, Any]:
    payload = {
        "type": "persistent",
        "fields": fields,
        "unique": unique,
        "sparse": sparse,
    }
    if name:
        payload["name"] = name
    return request_json(
        "POST",
        db_url(target, f"/_api/index?collection={quote(collection)}"),
        target,
        payload,
    )


def import_jsonl(
    target: ArangoHttpTarget,
    collection: str,
    payload: bytes,
    *,
    on_duplicate: str = "replace",
    complete: bool = True,
) -> dict[str, Any]:
    complete_arg = "true" if complete else "false"
    url = db_url(
        target,
        f"/_api/import?collection={quote(collection)}&type=documents"
        f"&onDuplicate={quote(on_duplicate)}&complete={complete_arg}",
    )
    return request_raw("POST", url, target, payload, content_type="application/json")


def execute_aql(
    target: ArangoHttpTarget,
    query: str,
    bind_vars: dict[str, Any] | None = None,
    *,
    timeout: float = 30,
    batch_size: int | None = None,
) -> list[Any]:
    payload: dict[str, Any] = {"query": query, "bindVars": bind_vars or {}}
    if batch_size is not None:
        payload["batchSize"] = batch_size

    cursor = request_json(
        "POST",
        db_url(target, "/_api/cursor"),
        target,
        payload,
        timeout=timeout,
    )
    rows = list(cursor.get("result", []))
    cursor_id = cursor.get("id")

    while cursor.get("hasMore") and cursor_id:
        cursor = request_json(
            "PUT",
            db_url(target, f"/_api/cursor/{quote(str(cursor_id))}"),
            target,
            timeout=timeout,
        )
        rows.extend(cursor.get("result", []))
        cursor_id = cursor.get("id")

    return rows
