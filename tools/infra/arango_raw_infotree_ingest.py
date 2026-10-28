#!/usr/bin/env python3
"""Ingest stage raw_infotree_* JSONL exports into ArangoDB.

This is intentionally separate from ``arango_layered_ingest.py``. The layered
ingester imports the lossless raw DAG dependency substrate. This script imports
the compiler-memory ``raw_infotree_*`` sidecar emitted by
``lean/DAG/RawInfoTreeExport.lean``.

The importer preserves the row tables as document collections and adds explicit
edge collections for query/navigation. It does not claim full compiler
losslessness; run ``validate_raw_infotree_export.py`` first and keep projection
leakage visible.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator
from urllib.error import HTTPError
from urllib.parse import quote
from urllib.request import Request, urlopen

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)


ROW_FILES: dict[str, str] = {
    "raw_infotree_roots": "raw_infotree_roots.jsonl",
    "raw_infotree_nodes": "raw_infotree_nodes.jsonl",
    "raw_infotree_contexts": "raw_infotree_contexts.jsonl",
    "raw_infotree_payloads": "raw_infotree_payloads.jsonl",
    "raw_infotree_payload_fields": "raw_infotree_payload_fields.jsonl",
    "raw_infotree_decl_links": "raw_infotree_decl_links.jsonl",
    "raw_infotree_env_refs": "raw_infotree_env_refs.jsonl",
    "raw_infotree_mctx_refs": "raw_infotree_mctx_refs.jsonl",
    "raw_infotree_mctx_decls": "raw_infotree_mctx_decls.jsonl",
    "raw_infotree_lctx_refs": "raw_infotree_lctx_refs.jsonl",
    "raw_infotree_lctx_decls": "raw_infotree_lctx_decls.jsonl",
    "raw_infotree_goal_states": "raw_infotree_goal_states.jsonl",
    "raw_infotree_fvar_lineage": "raw_infotree_fvar_lineage.jsonl",
    "raw_infotree_tactic_arguments": "raw_infotree_tactic_arguments.jsonl",
    "raw_infotree_messages": "raw_infotree_messages.jsonl",
    "raw_infotree_projection_leakage": "raw_infotree_projection_leakage.jsonl",
}

EDGE_COLLECTIONS = [
    "raw_infotree_tree_edges",
    "raw_infotree_root_node_edges",
    "raw_infotree_node_context_edges",
    "raw_infotree_node_payload_edges",
    "raw_infotree_payload_field_edges",
    "raw_infotree_node_decl_link_edges",
    "raw_infotree_node_env_ref_edges",
    "raw_infotree_node_mctx_ref_edges",
    "raw_infotree_mctx_decl_edges",
    "raw_infotree_source_lctx_ref_edges",
    "raw_infotree_lctx_ref_decl_edges",
    "raw_infotree_node_goal_edges",
    "raw_infotree_node_fvar_edges",
    "raw_infotree_node_argument_edges",
    "raw_infotree_node_message_edges",
    "raw_infotree_node_leakage_edges",
]

INDEX_SPECS: dict[str, list[list[str]]] = {
    "raw_infotree_roots": [["file"], ["module"]],
    "raw_infotree_nodes": [["rootKey"], ["kind"], ["payloadKey"], ["isLogical"], ["depth"], ["branchingFactor"]],
    "raw_infotree_contexts": [["nodeKey"], ["contextKind"], ["rootKey"], ["file"], ["module"]],
    "raw_infotree_payloads": [["nodeKey"], ["kind"], ["rootKey"], ["file"], ["module"]],
    "raw_infotree_payload_fields": [["payloadKey"], ["nodeKey"], ["field"], ["rootKey"], ["file"], ["module"]],
    "raw_infotree_decl_links": [["nodeKey"], ["declName"], ["rootKey"], ["file"], ["module"]],
    "raw_infotree_env_refs": [["nodeKey"], ["role"], ["rootKey"], ["file"], ["module"]],
    "raw_infotree_mctx_refs": [["nodeKey"], ["mctxKey"], ["rootKey"], ["file"], ["module"]],
    "raw_infotree_mctx_decls": [["mctxKey"], ["nodeKey"], ["mvarId"], ["userName"], ["typeHash"], ["rootKey"], ["file"], ["module"]],
    "raw_infotree_lctx_refs": [["nodeKey"], ["sourceKind", "sourceKey"], ["lctxKey"], ["rootKey"], ["file"], ["module"]],
    "raw_infotree_lctx_decls": [["lctxKey"], ["sourceKey"], ["fvarId"], ["userName"], ["typeHash"], ["rootKey"], ["file"], ["module"]],
    "raw_infotree_goal_states": [["nodeKey"], ["mvarId"], ["role"], ["rootKey"], ["file"], ["module"]],
    "raw_infotree_fvar_lineage": [["nodeKey"], ["fvarId"], ["role"], ["rootKey"]],
    "raw_infotree_tactic_arguments": [["nodeKey"], ["declName"], ["rootKey"]],
    "raw_infotree_messages": [["nodeKey"], ["severity"], ["rootKey"]],
    "raw_infotree_projection_leakage": [["nodeKey"], ["field"], ["rootKey"]],
    "raw_infotree_tree_edges": [["rootKey"], ["sourceEdgeKey"]],
    "raw_infotree_node_context_edges": [["contextKind"]],
    "raw_infotree_node_payload_edges": [["payloadKind"]],
    "raw_infotree_payload_field_edges": [["field"]],
    "raw_infotree_node_decl_link_edges": [["declName"]],
    "raw_infotree_node_env_ref_edges": [["envRole"], ["present"]],
    "raw_infotree_mctx_decl_edges": [["mctxKey"], ["mvarId"]],
    "raw_infotree_source_lctx_ref_edges": [["sourceKind", "sourceKey"], ["lctxKey"]],
    "raw_infotree_lctx_ref_decl_edges": [["lctxKey"], ["fvarId"]],
    "raw_infotree_node_goal_edges": [["role"]],
    "raw_infotree_node_fvar_edges": [["role"]],
    "raw_infotree_node_argument_edges": [["declName"]],
    "raw_infotree_node_message_edges": [["severity"]],
    "raw_infotree_node_leakage_edges": [["field"]],
}


@dataclass(frozen=True)
class CollectionSpec:
    name: str
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
    return f"{target.endpoint}/_db/{quote(target.database)}/{path.lstrip('/')}"


def sys_url(target: ArangoTarget, path: str) -> str:
    return f"{target.endpoint}/{path.lstrip('/')}"


def ensure_database(target: ArangoTarget) -> None:
    dbs = request_json(
        "GET",
        sys_url(target, "/_api/database"),
        username=target.username,
        password=target.password,
    )
    if isinstance(dbs, dict) and target.database in dbs.get("result", []):
        return
    request_json(
        "POST",
        sys_url(target, "/_api/database"),
        username=target.username,
        password=target.password,
        payload={"name": target.database},
    )


def list_collections(target: ArangoTarget) -> set[str]:
    payload = request_json(
        "GET",
        db_url(target, "/_api/collection"),
        username=target.username,
        password=target.password,
    )
    if not isinstance(payload, dict):
        return set()
    return {
        str(row.get("name"))
        for row in payload.get("result", [])
        if isinstance(row, dict) and row.get("name")
    }


def create_collection(target: ArangoTarget, spec: CollectionSpec) -> None:
    request_json(
        "POST",
        db_url(target, "/_api/collection"),
        username=target.username,
        password=target.password,
        payload={"name": spec.name, "type": 3 if spec.edge else 2, "waitForSync": False},
    )


def ensure_index(target: ArangoTarget, collection: str, fields: list[str], *, unique: bool = False, sparse: bool = True) -> dict[str, Any]:
    payload = {
        "type": "persistent",
        "fields": fields,
        "unique": unique,
        "sparse": sparse,
        "name": "idx_" + "_".join(fields).replace(".", "_"),
    }
    result = request_json(
        "POST",
        db_url(target, f"/_api/index?collection={quote(collection)}"),
        username=target.username,
        password=target.password,
        payload=payload,
    )
    return result if isinstance(result, dict) else {"result": result}


def ensure_indexes(target: ArangoTarget, collections: Iterable[str], base_names: dict[str, str] | None = None) -> dict[str, Any]:
    report: dict[str, Any] = {}
    for collection in collections:
        collection_report = []
        base_name = (base_names or {}).get(collection, collection)
        for fields in INDEX_SPECS.get(base_name, []):
            try:
                result = ensure_index(target, collection, fields)
                collection_report.append(
                    {
                        "fields": fields,
                        "error": bool(result.get("error")) if isinstance(result, dict) else False,
                        "id": result.get("id") if isinstance(result, dict) else None,
                        "isNewlyCreated": result.get("isNewlyCreated") if isinstance(result, dict) else None,
                    }
                )
            except Exception as exc:  # keep ingest report explicit rather than silently unindexed
                collection_report.append({"fields": fields, "error": True, "message": str(exc)})
        if collection_report:
            report[collection] = collection_report
    return report


def truncate_collection(target: ArangoTarget, name: str) -> None:
    request_json(
        "PUT",
        db_url(target, f"/_api/collection/{quote(name)}/truncate"),
        username=target.username,
        password=target.password,
    )


def drop_collection(target: ArangoTarget, name: str) -> None:
    request_json(
        "DELETE",
        db_url(target, f"/_api/collection/{quote(name)}"),
        username=target.username,
        password=target.password,
    )


def collection_count(target: ArangoTarget, collection: str) -> int:
    out = request_json(
        "GET",
        db_url(target, f"/_api/collection/{quote(collection)}/count"),
        username=target.username,
        password=target.password,
    )
    count = out.get("count") if isinstance(out, dict) else None
    return count if isinstance(count, int) else -1


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def count_jsonl(path: Path) -> int:
    return sum(1 for _ in iter_jsonl(path))


def prefixed_key(prefix: str, value: Any) -> str:
    text = str(value)
    safe = "".join(ch if ch.isalnum() or ch in "_:-." else "_" for ch in text)
    return f"{prefix}_{safe}"


def bounded_prefixed_key(prefix: str, value: Any, *, max_len: int = 254) -> str:
    key = prefixed_key(prefix, value)
    if len(key) <= max_len:
        return key
    digest = stable_row_hash({"prefix": prefix, "value": str(value)})
    head_budget = max_len - len(prefix) - len(digest) - 2
    if head_budget < 1:
        return f"{prefix}_{digest}"[:max_len]
    head = key[:head_budget]
    return f"{head}_{digest}"


def normalize_row(collection: str, row: dict[str, Any]) -> dict[str, Any]:
    out = dict(row)
    if collection == "raw_infotree_roots":
        out["_key"] = str(row["rootKey"])
    elif collection == "raw_infotree_nodes":
        out["_key"] = str(row["nodeKey"])
    elif collection == "raw_infotree_contexts":
        out["_key"] = str(row["contextKey"])
    elif collection == "raw_infotree_payloads":
        out["_key"] = str(row["payloadKey"])
    elif collection == "raw_infotree_payload_fields":
        out["_key"] = str(row["fieldKey"])
    elif collection == "raw_infotree_decl_links":
        out["_key"] = str(row["linkKey"])
    elif collection == "raw_infotree_env_refs":
        out["_key"] = str(row["envRefKey"])
    elif collection == "raw_infotree_mctx_refs":
        out["_key"] = str(row["mctxRefKey"])
    elif collection == "raw_infotree_mctx_decls":
        out["_key"] = str(row["declKey"])
    elif collection == "raw_infotree_lctx_refs":
        out["_key"] = str(row["lctxRefKey"])
    elif collection == "raw_infotree_lctx_decls":
        out["_key"] = str(row["lctxDeclKey"])
    elif collection == "raw_infotree_goal_states":
        out["_key"] = str(row["stateKey"])
    elif collection == "raw_infotree_fvar_lineage":
        out["_key"] = str(row["lineageKey"])
    elif collection == "raw_infotree_tactic_arguments":
        out["_key"] = str(row["argumentKey"])
    elif collection == "raw_infotree_messages":
        out["_key"] = str(row["messageKey"])
    elif collection == "raw_infotree_projection_leakage":
        node = row.get("nodeKey") if row.get("nodeKey") is not None else "root"
        out["_key"] = bounded_prefixed_key(
            "itlkg",
            f"{row.get('rootKey')}:{node}:{row.get('field')}:{stable_row_hash(row)}",
        )
    else:
        raise ValueError(f"unknown raw_infotree collection: {collection}")
    return out


def stable_row_hash(row: dict[str, Any]) -> str:
    text = json.dumps(row, sort_keys=True, ensure_ascii=True, separators=(",", ":"))
    # FNV-1a, enough for deterministic document keys without pulling extra deps.
    h = 2166136261
    for ch in text:
        h = (h ^ ord(ch)) * 16777619 % 2**64
    return f"{h:016x}"


def generation_fingerprint(input_dir: Path, build_fingerprint: str) -> str:
    """Content identity for one validated export in one declared environment."""
    digest = hashlib.sha256()
    digest.update(build_fingerprint.encode("utf-8"))
    for path in sorted(input_dir.iterdir(), key=lambda item: item.name):
        if not path.is_file() or (not path.name.endswith(".jsonl") and path.name != "metadata.json"):
            continue
        digest.update(path.name.encode("utf-8"))
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
    return digest.hexdigest()[:24]


def remap_edge_collections(row: dict[str, Any], collection_map: dict[str, str]) -> dict[str, Any]:
    """Move edge endpoints into the same immutable generation namespace."""
    out = dict(row)
    for field in ("_from", "_to"):
        collection, separator, key = str(out[field]).partition("/")
        if not separator or collection not in collection_map:
            raise ValueError(f"unexpected InfoTree edge endpoint {field}={out[field]!r}")
        out[field] = f"{collection_map[collection]}/{key}"
    return out


def import_batch(target: ArangoTarget, collection: str, rows: list[dict[str, Any]]) -> dict[str, int]:
    if not rows:
        return {"created": 0, "updated": 0, "errors": 0}
    url = db_url(target, f"/_api/document/{quote(collection)}?overwriteMode=replace&silent=false")
    result = request_json("POST", url, username=target.username, password=target.password, payload=rows)
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


def import_rows(
    target: ArangoTarget,
    collection: str,
    rows: Iterable[dict[str, Any]],
    *,
    batch_size: int,
    progress_every: int = 0,
) -> dict[str, Any]:
    created = updated = errors = total = batches = 0
    batch: list[dict[str, Any]] = []
    for row in rows:
        batch.append(row)
        if len(batch) >= batch_size:
            result = import_batch(target, collection, batch)
            created += result["created"]
            updated += result["updated"]
            errors += result["errors"]
            total += len(batch)
            batches += 1
            if progress_every > 0 and total % progress_every < batch_size:
                print(f"imported {collection}: {total}", file=sys.stderr, flush=True)
            batch = []
    if batch:
        result = import_batch(target, collection, batch)
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


def import_accounting_failures(imports: dict[str, dict[str, Any]]) -> list[str]:
    """Find collections whose response reports errors or misses submitted rows."""
    failures: list[str] = []
    for collection, result in imports.items():
        try:
            submitted = int(result["total"])
            accounted = int(result["created"]) + int(result["updated"]) + int(result["errors"])
        except (KeyError, TypeError, ValueError):
            failures.append(f"{collection}: incomplete import accounting")
            continue
        if result.get("error") or int(result.get("errors", 0)) > 0 or accounted != submitted:
            failures.append(
                f"{collection}: submitted={submitted} accounted={accounted} "
                f"errors={result.get('errors')}"
            )
    return failures


def edge_doc(collection: str, key: str, from_id: str, to_id: str, **fields: Any) -> dict[str, Any]:
    return {"_key": key, "_from": from_id, "_to": to_id, "role": collection, **fields}


def iter_edge_rows(input_dir: Path, collection: str) -> Iterator[dict[str, Any]]:
    if collection == "raw_infotree_root_node_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_nodes.jsonl"):
            root = str(row["rootKey"])
            node = str(row["nodeKey"])
            yield edge_doc(
                "root_has_node",
                prefixed_key("itern", f"{root}:{node}"),
                f"raw_infotree_roots/{root}",
                f"raw_infotree_nodes/{node}",
            )
        return

    if collection == "raw_infotree_tree_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_edges.jsonl"):
            edge_key = str(row["edgeKey"])
            yield edge_doc(
                "infotree_parent_child",
                edge_key,
                f"raw_infotree_nodes/{row['parentKey']}",
                f"raw_infotree_nodes/{row['childKey']}",
                rootKey=row.get("rootKey"),
                siblingIndex=row.get("siblingIndex"),
                sourceEdgeKey=edge_key,
            )
        return

    if collection == "raw_infotree_node_context_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_contexts.jsonl"):
            key = str(row["contextKey"])
            yield edge_doc(
                "node_has_context",
                prefixed_key("itenc", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_contexts/{key}",
                contextKind=row.get("contextKind"),
            )
        return

    if collection == "raw_infotree_node_payload_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_payloads.jsonl"):
            key = str(row["payloadKey"])
            yield edge_doc(
                "node_has_payload",
                prefixed_key("itenp", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_payloads/{key}",
                payloadKind=row.get("kind"),
            )
        return

    if collection == "raw_infotree_payload_field_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_payload_fields.jsonl"):
            key = str(row["fieldKey"])
            yield edge_doc(
                "payload_has_field",
                prefixed_key("itepf", key),
                f"raw_infotree_payloads/{row['payloadKey']}",
                f"raw_infotree_payload_fields/{key}",
                field=row.get("field"),
            )
        return

    if collection == "raw_infotree_node_decl_link_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_decl_links.jsonl"):
            key = str(row["linkKey"])
            yield edge_doc(
                "node_references_decl",
                prefixed_key("itendl", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_decl_links/{key}",
                declName=row.get("declName"),
            )
        return

    if collection == "raw_infotree_node_env_ref_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_env_refs.jsonl"):
            key = str(row["envRefKey"])
            yield edge_doc(
                "node_has_env_ref",
                prefixed_key("itener", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_env_refs/{key}",
                envRole=row.get("role"),
                present=row.get("present"),
            )
        return

    if collection == "raw_infotree_node_mctx_ref_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_mctx_refs.jsonl"):
            key = str(row["mctxRefKey"])
            yield edge_doc(
                "node_has_mctx_ref",
                prefixed_key("itenmr", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_mctx_refs/{key}",
            )
        return

    if collection == "raw_infotree_mctx_decl_edges":
        mctx_refs_by_key: dict[str, list[str]] = {}
        for row in iter_jsonl(input_dir / "raw_infotree_mctx_refs.jsonl"):
            mctx_key = str(row.get("mctxKey") or row.get("mctxRefKey"))
            mctx_refs_by_key.setdefault(mctx_key, []).append(str(row["mctxRefKey"]))
        for row in iter_jsonl(input_dir / "raw_infotree_mctx_decls.jsonl"):
            key = str(row["declKey"])
            mctx_key = str(row.get("mctxKey") or row.get("mctxRefKey"))
            for ref_key in mctx_refs_by_key.get(mctx_key, []):
                yield edge_doc(
                    "mctx_ref_has_decl",
                    prefixed_key("itemd", stable_row_hash({"mctxRefKey": ref_key, "declKey": key})),
                    f"raw_infotree_mctx_refs/{ref_key}",
                    f"raw_infotree_mctx_decls/{key}",
                    mvarId=row.get("mvarId"),
                    mctxKey=mctx_key,
                )
        return

    if collection == "raw_infotree_source_lctx_ref_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_lctx_refs.jsonl"):
            key = str(row["lctxRefKey"])
            source_kind = str(row.get("sourceKind"))
            source_key = str(row.get("sourceKey"))
            lctx_key = str(row.get("lctxKey"))
            if source_kind == "mctx_decl":
                from_id = f"raw_infotree_mctx_decls/{source_key}"
            else:
                from_id = f"raw_infotree_nodes/{row['nodeKey']}"
            yield edge_doc(
                "source_has_lctx_ref",
                prefixed_key("iteslr", key),
                from_id,
                f"raw_infotree_lctx_refs/{key}",
                sourceKind=source_kind,
                sourceKey=source_key,
                lctxKey=lctx_key,
                lctxSize=row.get("lctxSize"),
            )
        return

    if collection == "raw_infotree_lctx_ref_decl_edges":
        lctx_refs_by_key: dict[str, list[str]] = {}
        for row in iter_jsonl(input_dir / "raw_infotree_lctx_refs.jsonl"):
            lctx_key = str(row.get("lctxKey"))
            lctx_refs_by_key.setdefault(lctx_key, []).append(str(row["lctxRefKey"]))
        for row in iter_jsonl(input_dir / "raw_infotree_lctx_decls.jsonl"):
            key = str(row["lctxDeclKey"])
            lctx_key = str(row["sourceKey"])
            for ref_key in lctx_refs_by_key.get(lctx_key, []):
                yield edge_doc(
                    "lctx_ref_has_decl",
                    prefixed_key("itelrd", stable_row_hash({"lctxRefKey": ref_key, "lctxDeclKey": key})),
                    f"raw_infotree_lctx_refs/{ref_key}",
                    f"raw_infotree_lctx_decls/{key}",
                    lctxKey=lctx_key,
                    fvarId=row.get("fvarId"),
                )
        return

    if collection == "raw_infotree_node_goal_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_goal_states.jsonl"):
            key = str(row["stateKey"])
            yield edge_doc(
                "node_has_goal_state",
                prefixed_key("itengs", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_goal_states/{key}",
                role=row.get("role"),
                mvarId=row.get("mvarId"),
            )
        return

    if collection == "raw_infotree_node_fvar_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_fvar_lineage.jsonl"):
            key = str(row["lineageKey"])
            yield edge_doc(
                "node_has_fvar_lineage",
                prefixed_key("itenfl", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_fvar_lineage/{key}",
                role=row.get("role"),
                fvarId=row.get("fvarId"),
            )
        return

    if collection == "raw_infotree_node_argument_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_tactic_arguments.jsonl"):
            key = str(row["argumentKey"])
            yield edge_doc(
                "node_has_tactic_argument",
                prefixed_key("itenta", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_tactic_arguments/{key}",
                declName=row.get("declName"),
            )
        return

    if collection == "raw_infotree_node_message_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_messages.jsonl"):
            key = str(row["messageKey"])
            node_key = row.get("nodeKey")
            if node_key is None:
                continue
            yield edge_doc(
                "node_has_message",
                prefixed_key("itenmsg", key),
                f"raw_infotree_nodes/{node_key}",
                f"raw_infotree_messages/{key}",
                severity=row.get("severity"),
            )
        return

    if collection == "raw_infotree_node_leakage_edges":
        for row in iter_jsonl(input_dir / "raw_infotree_projection_leakage.jsonl"):
            leakage_key = normalize_row("raw_infotree_projection_leakage", row)["_key"]
            node_key = row.get("nodeKey")
            if node_key is None:
                continue
            yield edge_doc(
                "node_has_projection_leakage",
                bounded_prefixed_key("itenl", leakage_key),
                f"raw_infotree_nodes/{node_key}",
                f"raw_infotree_projection_leakage/{leakage_key}",
                field=row.get("field"),
            )
        return

    raise ValueError(f"unknown raw_infotree edge collection: {collection}")


def raw_edge_counts(input_dir: Path) -> dict[str, int]:
    counts = {
        "raw_infotree_root_node_edges": count_jsonl(input_dir / "raw_infotree_nodes.jsonl"),
        "raw_infotree_tree_edges": count_jsonl(input_dir / "raw_infotree_edges.jsonl"),
        "raw_infotree_node_context_edges": count_jsonl(input_dir / "raw_infotree_contexts.jsonl"),
        "raw_infotree_node_payload_edges": count_jsonl(input_dir / "raw_infotree_payloads.jsonl"),
        "raw_infotree_payload_field_edges": count_jsonl(input_dir / "raw_infotree_payload_fields.jsonl"),
        "raw_infotree_node_decl_link_edges": count_jsonl(input_dir / "raw_infotree_decl_links.jsonl"),
        "raw_infotree_node_env_ref_edges": count_jsonl(input_dir / "raw_infotree_env_refs.jsonl"),
        "raw_infotree_node_mctx_ref_edges": count_jsonl(input_dir / "raw_infotree_mctx_refs.jsonl"),
        "raw_infotree_source_lctx_ref_edges": count_jsonl(input_dir / "raw_infotree_lctx_refs.jsonl"),
        "raw_infotree_node_goal_edges": count_jsonl(input_dir / "raw_infotree_goal_states.jsonl"),
        "raw_infotree_node_fvar_edges": count_jsonl(input_dir / "raw_infotree_fvar_lineage.jsonl"),
        "raw_infotree_node_argument_edges": count_jsonl(input_dir / "raw_infotree_tactic_arguments.jsonl"),
    }
    counts["raw_infotree_node_message_edges"] = sum(
        1 for row in iter_jsonl(input_dir / "raw_infotree_messages.jsonl")
        if row.get("nodeKey") is not None
    )
    counts["raw_infotree_node_leakage_edges"] = sum(
        1 for row in iter_jsonl(input_dir / "raw_infotree_projection_leakage.jsonl")
        if row.get("nodeKey") is not None
    )

    mctx_ref_counts: dict[str, int] = {}
    for row in iter_jsonl(input_dir / "raw_infotree_mctx_refs.jsonl"):
        mctx_key = str(row.get("mctxKey") or row.get("mctxRefKey"))
        mctx_ref_counts[mctx_key] = mctx_ref_counts.get(mctx_key, 0) + 1
    counts["raw_infotree_mctx_decl_edges"] = sum(
        mctx_ref_counts.get(str(row.get("mctxKey") or row.get("mctxRefKey")), 0)
        for row in iter_jsonl(input_dir / "raw_infotree_mctx_decls.jsonl")
    )

    lctx_ref_counts: dict[str, int] = {}
    for row in iter_jsonl(input_dir / "raw_infotree_lctx_refs.jsonl"):
        lctx_key = str(row.get("lctxKey"))
        lctx_ref_counts[lctx_key] = lctx_ref_counts.get(lctx_key, 0) + 1
    counts["raw_infotree_lctx_ref_decl_edges"] = sum(
        lctx_ref_counts.get(str(row.get("sourceKey")), 0)
        for row in iter_jsonl(input_dir / "raw_infotree_lctx_decls.jsonl")
    )
    return {name: counts.get(name, 0) for name in EDGE_COLLECTIONS}


def raw_row_edges(input_dir: Path) -> dict[str, list[dict[str, Any]]]:
    edges: dict[str, list[dict[str, Any]]] = {name: [] for name in EDGE_COLLECTIONS}
    for collection in EDGE_COLLECTIONS:
        edges[collection].extend(iter_edge_rows(input_dir, collection))
    return edges

def _legacy_raw_row_edges(input_dir: Path) -> dict[str, list[dict[str, Any]]]:
    edges: dict[str, list[dict[str, Any]]] = {name: [] for name in EDGE_COLLECTIONS}

    for row in iter_jsonl(input_dir / "raw_infotree_nodes.jsonl"):
        root = str(row["rootKey"])
        node = str(row["nodeKey"])
        edges["raw_infotree_root_node_edges"].append(
            edge_doc(
                "root_has_node",
                prefixed_key("itern", f"{root}:{node}"),
                f"raw_infotree_roots/{root}",
                f"raw_infotree_nodes/{node}",
            )
        )

    for row in iter_jsonl(input_dir / "raw_infotree_edges.jsonl"):
        edge_key = str(row["edgeKey"])
        edges["raw_infotree_tree_edges"].append(
            edge_doc(
                "infotree_parent_child",
                edge_key,
                f"raw_infotree_nodes/{row['parentKey']}",
                f"raw_infotree_nodes/{row['childKey']}",
                rootKey=row.get("rootKey"),
                siblingIndex=row.get("siblingIndex"),
                sourceEdgeKey=edge_key,
            )
        )

    for row in iter_jsonl(input_dir / "raw_infotree_contexts.jsonl"):
        key = str(row["contextKey"])
        edges["raw_infotree_node_context_edges"].append(
            edge_doc(
                "node_has_context",
                prefixed_key("itenc", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_contexts/{key}",
                contextKind=row.get("contextKind"),
            )
        )

    for row in iter_jsonl(input_dir / "raw_infotree_payloads.jsonl"):
        key = str(row["payloadKey"])
        edges["raw_infotree_node_payload_edges"].append(
            edge_doc(
                "node_has_payload",
                prefixed_key("itenp", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_payloads/{key}",
                payloadKind=row.get("kind"),
            )
        )

    for row in iter_jsonl(input_dir / "raw_infotree_payload_fields.jsonl"):
        key = str(row["fieldKey"])
        edges["raw_infotree_payload_field_edges"].append(
            edge_doc(
                "payload_has_field",
                prefixed_key("itepf", key),
                f"raw_infotree_payloads/{row['payloadKey']}",
                f"raw_infotree_payload_fields/{key}",
                field=row.get("field"),
            )
        )

    for row in iter_jsonl(input_dir / "raw_infotree_decl_links.jsonl"):
        key = str(row["linkKey"])
        edges["raw_infotree_node_decl_link_edges"].append(
            edge_doc(
                "node_references_decl",
                prefixed_key("itendl", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_decl_links/{key}",
                declName=row.get("declName"),
            )
        )

    for row in iter_jsonl(input_dir / "raw_infotree_env_refs.jsonl"):
        key = str(row["envRefKey"])
        edges["raw_infotree_node_env_ref_edges"].append(
            edge_doc(
                "node_has_env_ref",
                prefixed_key("itener", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_env_refs/{key}",
                envRole=row.get("role"),
                present=row.get("present"),
            )
        )

    for row in iter_jsonl(input_dir / "raw_infotree_mctx_refs.jsonl"):
        key = str(row["mctxRefKey"])
        edges["raw_infotree_node_mctx_ref_edges"].append(
            edge_doc(
                "node_has_mctx_ref",
                prefixed_key("itenmr", key),
                f"raw_infotree_nodes/{row['nodeKey']}",
                f"raw_infotree_mctx_refs/{key}",
            )
        )

    mctx_refs_by_key: dict[str, list[str]] = {}
    for row in iter_jsonl(input_dir / "raw_infotree_mctx_refs.jsonl"):
        mctx_key = str(row.get("mctxKey") or row.get("mctxRefKey"))
        mctx_refs_by_key.setdefault(mctx_key, []).append(str(row["mctxRefKey"]))

    for row in iter_jsonl(input_dir / "raw_infotree_mctx_decls.jsonl"):
        key = str(row["declKey"])
        mctx_key = str(row.get("mctxKey") or row.get("mctxRefKey"))
        for ref_key in mctx_refs_by_key.get(mctx_key, []):
            edges["raw_infotree_mctx_decl_edges"].append(
                edge_doc(
                    "mctx_ref_has_decl",
                    prefixed_key("itemd", stable_row_hash({"mctxRefKey": ref_key, "declKey": key})),
                    f"raw_infotree_mctx_refs/{ref_key}",
                    f"raw_infotree_mctx_decls/{key}",
                    mvarId=row.get("mvarId"),
                    mctxKey=mctx_key,
                )
            )

    lctx_refs_by_key: dict[str, list[str]] = {}
    for row in iter_jsonl(input_dir / "raw_infotree_lctx_refs.jsonl"):
        key = str(row["lctxRefKey"])
        source_kind = str(row.get("sourceKind"))
        source_key = str(row.get("sourceKey"))
        lctx_key = str(row.get("lctxKey"))
        if source_kind == "mctx_decl":
            from_id = f"raw_infotree_mctx_decls/{source_key}"
        else:
            from_id = f"raw_infotree_nodes/{row['nodeKey']}"
        lctx_refs_by_key.setdefault(lctx_key, []).append(key)
        edges["raw_infotree_source_lctx_ref_edges"].append(
            edge_doc(
                "source_has_lctx_ref",
                prefixed_key("iteslr", key),
                from_id,
                f"raw_infotree_lctx_refs/{key}",
                sourceKind=source_kind,
                sourceKey=source_key,
                lctxKey=lctx_key,
                lctxSize=row.get("lctxSize"),
            )
        )

    for row in iter_jsonl(input_dir / "raw_infotree_lctx_decls.jsonl"):
        key = str(row["lctxDeclKey"])
        lctx_key = str(row["sourceKey"])
        for ref_key in lctx_refs_by_key.get(lctx_key, []):
            edges["raw_infotree_lctx_ref_decl_edges"].append(
                edge_doc(
                    "lctx_ref_has_decl",
                    prefixed_key("itelrd", stable_row_hash({"lctxRefKey": ref_key, "lctxDeclKey": key})),
                    f"raw_infotree_lctx_refs/{ref_key}",
                    f"raw_infotree_lctx_decls/{key}",
                    lctxKey=lctx_key,
                    fvarId=row.get("fvarId"),
                )
            )

    for row in iter_jsonl(input_dir / "raw_infotree_projection_leakage.jsonl"):
        leakage_key = normalize_row("raw_infotree_projection_leakage", row)["_key"]
        node_key = row.get("nodeKey")
        if node_key is None:
            continue
        edges["raw_infotree_node_leakage_edges"].append(
            edge_doc(
                "node_has_projection_leakage",
                prefixed_key("itenl", leakage_key),
                f"raw_infotree_nodes/{node_key}",
                f"raw_infotree_projection_leakage/{leakage_key}",
                field=row.get("field"),
            )
        )

    return edges


def validate_export(input_dir: Path, repo_root: Path, require_lossless: bool) -> dict[str, Any]:
    validator = repo_root / "tools/infra/validate_raw_infotree_export.py"
    cmd = [sys.executable, str(validator), "--input-dir", str(input_dir)]
    if require_lossless:
        cmd.append("--require-lossless")
    proc = subprocess.run(cmd, text=True, capture_output=True)
    try:
        report = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"validator did not emit JSON\nstdout={proc.stdout}\nstderr={proc.stderr}") from exc
    if proc.returncode != 0:
        raise RuntimeError(
            f"raw_infotree validation failed with exit {proc.returncode}\n"
            f"stdout={proc.stdout}\nstderr={proc.stderr}"
        )
    return report


def preflight_input(input_dir: Path) -> dict[str, Any]:
    required = list(ROW_FILES.values()) + ["metadata.json"]
    missing = [name for name in required if not (input_dir / name).exists()]
    metadata: dict[str, Any] | None = None
    metadata_path = input_dir / "metadata.json"
    if metadata_path.exists():
        loaded = json.loads(metadata_path.read_text(encoding="utf-8"))
        metadata = loaded if isinstance(loaded, dict) else {"raw": loaded}
    source_metadata = metadata.get("source_metadata", []) if metadata else []
    if metadata and metadata.get("schema") == "info_geometry.raw_infotree_export.v1":
        source_metadata = [metadata]
    provenance = [
        row.get("sourceProvenance") for row in source_metadata
        if isinstance(row, dict) and isinstance(row.get("sourceProvenance"), dict)
    ] if isinstance(source_metadata, list) else []
    return {
        "ok": not missing,
        "missing_files": missing,
        "metadata_schema": metadata.get("schema") if metadata else None,
        "metadata_stage": metadata.get("stage") if metadata else None,
        "metadata_file_count": metadata.get("file_count") if metadata else None,
        "source_provenance_count": len(provenance),
        "source_provenance": provenance,
    }


def parse_args() -> argparse.Namespace:
    load_repo_arango_env()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password("alexandria_root"))
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--drop-existing", action="store_true")
    parser.add_argument("--build-fingerprint", help="Enable immutable generation ingest bound to this Lean/Lake environment.")
    parser.add_argument("--batch-size", type=int, default=5000)
    parser.add_argument("--skip-validation", action="store_true")
    parser.add_argument("--skip-indexes", action="store_true", help="Do not create Arango persistent indexes after collection setup.")
    parser.add_argument("--require-lossless", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--progress-every", type=int, default=100000, help="Print import progress every N streamed rows; set 0 to disable.")
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/infotree/arango_raw_infotree_ingest_report.json"))
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    input_dir = args.input_dir.resolve()
    batch_size = max(1, int(args.batch_size))

    preflight = preflight_input(input_dir)
    if not preflight["ok"]:
        raise RuntimeError(f"raw_infotree input preflight failed: missing {preflight['missing_files']}")

    validation = None
    if not args.skip_validation:
        validation = validate_export(input_dir, repo_root, bool(args.require_lossless))

    row_counts = {
        collection: count_jsonl(input_dir / filename)
        for collection, filename in ROW_FILES.items()
    }
    edge_counts = raw_edge_counts(input_dir)
    generation_id = generation_fingerprint(input_dir, args.build_fingerprint) if args.build_fingerprint else None
    if generation_id and args.drop_existing:
        raise SystemExit("--drop-existing cannot be combined with immutable --build-fingerprint ingest")
    collection_map = {
        name: f"{name}_g_{generation_id}" if generation_id else name
        for name in list(ROW_FILES) + EDGE_COLLECTIONS
    }
    all_specs = [CollectionSpec(collection_map[name], False) for name in ROW_FILES]
    all_specs += [CollectionSpec(collection_map[name], True) for name in EDGE_COLLECTIONS]

    report: dict[str, Any] = {
        "schema": "info_geometry.arango_raw_infotree_ingest.v1",
        "input_dir": str(input_dir),
        "database": str(args.database),
        "preflight": preflight,
        "validation": validation,
        "row_counts": row_counts,
        "edge_counts": edge_counts,
        "generation_id": generation_id,
        "build_fingerprint": args.build_fingerprint,
        "collections": [spec.name for spec in all_specs],
        "dry_run": bool(args.dry_run),
    }

    if not args.dry_run:
        target = ArangoTarget(
            endpoint=str(args.endpoint).rstrip("/"),
            database=str(args.database),
            username=str(args.username),
            password=str(args.password),
        )
        ensure_database(target)
        existing = list_collections(target)
        if generation_id and any(spec.name in existing for spec in all_specs):
            raise RuntimeError(
                f"immutable InfoTree generation {generation_id} already exists; "
                "do not overwrite it—use a distinct environment or export"
            )
        for spec in all_specs:
            if spec.name in existing and args.drop_existing:
                drop_collection(target, spec.name)
                create_collection(target, spec)
            elif spec.name not in existing:
                create_collection(target, spec)

        imports: dict[str, Any] = {}
        for collection, filename in ROW_FILES.items():
            path = input_dir / filename
            rows = (normalize_row(collection, row) for row in iter_jsonl(path))
            target_collection = collection_map[collection]
            imports[target_collection] = import_rows(
                target,
                target_collection,
                rows,
                batch_size=batch_size,
                progress_every=max(0, int(args.progress_every)),
            )
        for collection in EDGE_COLLECTIONS:
            rows = iter_edge_rows(input_dir, collection)
            if generation_id:
                rows = (remap_edge_collections(row, collection_map) for row in rows)
            target_collection = collection_map[collection]
            imports[target_collection] = import_rows(
                target,
                target_collection,
                rows,
                batch_size=batch_size,
                progress_every=max(0, int(args.progress_every)),
            )

        report["imports"] = imports
        import_failures = import_accounting_failures(imports)
        report["import_accounting_failures"] = import_failures
        if import_failures:
            raise RuntimeError(
                "raw_infotree import accounting failed; refusing generation completion: "
                + "; ".join(import_failures)
            )
        if not args.skip_indexes:
            report["indexes"] = ensure_indexes(
                target, (spec.name for spec in all_specs),
                {collection_map[name]: name for name in collection_map},
            )
        report["live_counts"] = {spec.name: collection_count(target, spec.name) for spec in all_specs}
        if generation_id:
            metadata_collection = "raw_infotree_generations"
            if metadata_collection not in existing:
                create_collection(target, CollectionSpec(metadata_collection, False))
            generation_doc = {
                "_key": generation_id,
                "schema": "info_geometry.raw_infotree_generation.v1",
                "status": "complete",
                "buildFingerprint": args.build_fingerprint,
                "exportMetadata": preflight,
                "sourceProvenance": preflight["source_provenance"],
                "validation": validation,
                "collections": collection_map,
                "rowCounts": row_counts,
                "edgeCounts": edge_counts,
                "liveCounts": report["live_counts"],
            }
            request_json(
                "POST", db_url(target, f"/_api/document/{metadata_collection}?waitForSync=true"),
                username=target.username, password=target.password, payload=generation_doc,
            )

    out_path = args.json_out.resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(f"Raw InfoTree Arango ingest report written: {out_path}")
    print("Rows: " + " ".join(f"{name}={count}" for name, count in row_counts.items()))
    print("Edges: " + " ".join(f"{name}={count}" for name, count in edge_counts.items()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
