#!/usr/bin/env python3
"""Ingest hydrated raw graph and topology overlay JSONL into ArangoDB.

This keeps the layered tensor-network model intact:

- raw nodes/edges are imported one-for-one into raw collections
- SCC/topology nodes are imported into a separate overlay collection
- projection/quotient edges are imported into a separate overlay edge collection

The script does not compute topology. Run `hydrate_arango_topology.py` first.
"""

from __future__ import annotations

import argparse
import base64
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable
from urllib.error import HTTPError
from urllib.parse import quote
from urllib.request import Request, urlopen


@dataclass(frozen=True)
class CollectionSpec:
    name: str
    path: Path
    edge: bool


@dataclass(frozen=True)
class ArangoTarget:
    endpoint: str
    database: str
    username: str
    password: str


def auth_header(username: str, password: str) -> str:
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"


def request_json(
    method: str,
    url: str,
    *,
    username: str,
    password: str,
    payload: dict[str, Any] | list[dict[str, Any]] | None = None,
) -> dict[str, Any] | list[Any]:
    body = None if payload is None else json.dumps(payload, ensure_ascii=True).encode("utf-8")
    req = Request(url, data=body, method=method)
    req.add_header("Authorization", auth_header(username, password))
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urlopen(req) as resp:
            raw = resp.read().decode("utf-8")
            return json.loads(raw) if raw else {}
    except HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {url}: {raw}") from exc


def db_url(target: ArangoTarget, path: str) -> str:
    return f"{target.endpoint.rstrip('/')}/_db/{quote(target.database)}{path}"


def ensure_database(target: ArangoTarget) -> None:
    url = f"{target.endpoint.rstrip('/')}/_api/database"
    try:
        request_json("POST", url, username=target.username, password=target.password, payload={"name": target.database})
    except RuntimeError:
        pass


def list_collections(target: ArangoTarget) -> set[str]:
    out = request_json("GET", db_url(target, "/_api/collection"), username=target.username, password=target.password)
    if isinstance(out, dict):
        return {str(c["name"]) for c in out.get("result", [])}
    return set()


def create_collection(target: ArangoTarget, spec: CollectionSpec) -> None:
    request_json(
        "POST",
        db_url(target, "/_api/collection"),
        username=target.username,
        password=target.password,
        payload={"name": spec.name, "type": 3 if spec.edge else 2, "waitForSync": False},
    )


def truncate_collection(target: ArangoTarget, name: str) -> None:
    request_json(
        "PUT",
        db_url(target, f"/_api/collection/{quote(name)}/truncate"),
        username=target.username,
        password=target.password,
    )


def iter_jsonl(path: Path, spec: CollectionSpec) -> Iterable[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            
            # Map for ig_nodes
            if spec.name == "ig_nodes":
                name = row.get("name")
                if name:
                    row["_key"] = str(name).replace("/", "_")
            elif spec.name == "ig_edges":
                src = row.get("src")
                dst = row.get("dst")
                if src and dst:
                    row["_from"] = f"ig_nodes/{str(src).replace('/', '_')}"
                    row["_to"] = f"ig_nodes/{str(dst).replace('/', '_')}"
            
            yield row


def import_batch(target: ArangoTarget, collection: str, rows: list[dict[str, Any]]) -> dict[str, int]:
    if not rows:
        return {"created": 0, "updated": 0, "errors": 0}
    url = db_url(
        target,
        f"/_api/document/{quote(collection)}?overwriteMode=replace&silent=false",
    )
    result = request_json(
        "POST",
        url,
        username=target.username,
        password=target.password,
        payload=rows,
    )
    created = updated = errors = 0
    if isinstance(result, list):
        for row in result:
            if isinstance(row, dict) and row.get("error"):
                errors += 1
            elif isinstance(row, dict) and row.get("_oldRev"):
                updated += 1
            else:
                created += 1
    elif isinstance(result, dict):
        if result.get("error"):
            errors += len(rows)
        else:
            created += len(rows)
    return {"created": created, "updated": updated, "errors": errors}


def import_jsonl_batched(target: ArangoTarget, spec: CollectionSpec, *, batch_size: int = 5000) -> dict[str, Any]:
    created = updated = errors = total = batches = 0
    batch: list[dict[str, Any]] = []
    for row in iter_jsonl(spec.path, spec):
        batch.append(row)
        if len(batch) >= batch_size:
            result = import_batch(target, spec.name, batch)
            created += result["created"]
            updated += result["updated"]
            errors += result["errors"]
            total += len(batch)
            batches += 1
            batch = []
    if batch:
        result = import_batch(target, spec.name, batch)
        created += result["created"]
        updated += result["updated"]
        errors += result["errors"]
        total += len(batch)
        batches += 1
    return {
        "error": errors > 0,
        "created": created,
        "updated": updated,
        "errors": errors,
        "total": total,
        "batches": batches,
        "method": "document_batch_replace",
    }


def collection_count(target: ArangoTarget, collection: str) -> int:
    out = request_json(
        "GET",
        db_url(target, f"/_api/collection/{quote(collection)}/count"),
        username=target.username,
        password=target.password,
    )
    count = out.get("count")
    return count if isinstance(count, int) else -1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default="http://127.0.0.1:8529")
    parser.add_argument("--database", default="infogeometry")
    parser.add_argument("--username", default="root")
    parser.add_argument("--password", default="")
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--raw-nodes-collection", default="ig_nodes")
    parser.add_argument("--raw-edges-collection", default="ig_edges")
    parser.add_argument("--overlay-nodes-collection", default="topology_overlay")
    parser.add_argument("--overlay-edges-collection", default="topology_overlay_edges")
    parser.add_argument("--drop-existing", action="store_true")
    parser.add_argument("--batch-size", type=int, default=5000)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    target = ArangoTarget(
        endpoint=str(args.endpoint),
        database=str(args.database),
        username=str(args.username),
        password=str(args.password),
    )
    input_dir = args.input_dir.resolve()
    specs = [
        CollectionSpec(str(args.raw_nodes_collection), input_dir / "decls.jsonl", False),
        CollectionSpec(str(args.raw_edges_collection), input_dir / "edges.jsonl", True),
        CollectionSpec(str(args.overlay_nodes_collection), input_dir / "topology_overlay_nodes.jsonl", False),
        CollectionSpec(str(args.overlay_edges_collection), input_dir / "topology_overlay_edges.jsonl", True),
    ]

    # Filter out missing optional specs
    specs = [s for s in specs if s.path.exists()]

    ensure_database(target)
    existing = list_collections(target)
    for spec in specs:
        if spec.name not in existing:
            create_collection(target, spec)
        elif args.drop_existing:
            truncate_collection(target, spec.name)

    imports = {
        spec.name: import_jsonl_batched(target, spec, batch_size=max(1, int(args.batch_size)))
        for spec in specs
    }
    counts = {spec.name: collection_count(target, spec.name) for spec in specs}

    report = {
        "schema": "info_geometry.arango_layered_ingest.v1",
        "endpoint": target.endpoint,
        "database": target.database,
        "input_dir": str(input_dir),
        "collections": {
            spec.name: {
                "file": str(spec.path.relative_to(input_dir)),
                "edge": spec.edge,
                "import": imports[spec.name],
                "count": counts[spec.name],
            }
            for spec in specs
        },
    }

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print(f"Layered Arango ingest report written: {args.json_out if args.json_out else '(stdout)'}")
    print(f"Counts: " + " ".join(f"{k}={v}" for k, v in counts.items()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
