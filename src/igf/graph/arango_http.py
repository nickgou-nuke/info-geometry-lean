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
