#!/usr/bin/env python3
"""Ingest DumpLeanGraph syntax JSONL into ArangoDB.

The script is theorem-honest about the data boundary: it ingests syntax AST
records only.  It does not resolve identifiers, infer semantic dependencies, or
claim elaborated proof dependencies.

Default mode is a dry run, so CI/smoke tests do not need ArangoDB or
python-arango.  Use `--execute` to connect and write to ArangoDB.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Iterable


VALID_NODE_KINDS = {"node", "atom", "ident"}


def load_env_file(path: Path = Path.home() / ".config/arango/env.sh") -> None:
    """Load simple Arango `export KEY=value` defaults without requiring `source`."""
    if not path.exists():
        return
    for raw in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export "):].strip()
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip().strip('"').strip("'")
        if key and key not in os.environ:
            os.environ[key] = value


load_env_file()


def fail(message: str) -> None:
    raise SystemExit(f"ingest_syntax_to_arango: {message}")


def stable_key(*parts: str) -> str:
    raw = "\x1f".join(parts)
    digest = hashlib.sha1(raw.encode("utf-8")).hexdigest()[:16]
    safe = "_".join(parts[:2])
    safe = "".join(ch if (ch.isascii() and ch.isalnum()) or ch in "_-" else "_" for ch in safe)
    safe = safe.strip("_")[:180]
    return f"{safe}_{digest}" if safe else digest


def load_jsonl(path: Path | None) -> list[dict[str, Any]]:
    handle = sys.stdin if path is None else path.open(encoding="utf-8")
    records: list[dict[str, Any]] = []
    with handle:
        for line_number, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                fail(f"line {line_number}: invalid JSONL: {exc}")
            if record.get("layer") != "syntax":
                fail(f"line {line_number}: expected layer='syntax'")
            name = record.get("name")
            keyword = record.get("keyword")
            syntax = record.get("syntax")
            if not isinstance(name, str) or not name:
                fail(f"line {line_number}: missing declaration name")
            if not isinstance(keyword, str) or not keyword:
                fail(f"line {line_number}: missing declaration keyword")
            if not isinstance(syntax, dict):
                fail(f"line {line_number}: missing syntax object")
            records.append(record)
    if not records:
        fail("no syntax records read")
    return records


def iter_ast_nodes(
    decl_name: str,
    syntax: dict[str, Any],
    parent_key: str | None = None,
    path: tuple[int, ...] = (),
) -> Iterable[tuple[dict[str, Any], dict[str, str] | None]]:
    kind = syntax.get("kind")
    if kind not in VALID_NODE_KINDS:
        fail(f"{decl_name}:{path}: invalid syntax node kind {kind!r}")
    syntax_kind = syntax.get("syntaxKind")
    if not isinstance(syntax_kind, str):
        fail(f"{decl_name}:{path}: missing syntaxKind")
    path_str = "/".join(map(str, path)) if path else "root"
    key = stable_key(decl_name, path_str, kind, syntax_kind)
    doc: dict[str, Any] = {
        "_key": key,
        "declName": decl_name,
        "path": path_str,
        "nodeKind": kind,
        "syntaxKind": syntax_kind,
        "range": syntax.get("range"),
    }
    if kind == "atom":
        doc["value"] = syntax.get("value", "")
    elif kind == "ident":
        doc["raw"] = syntax.get("raw", "")
    yield doc, None if parent_key is None else {
        "_key": stable_key("ast_child", parent_key, key),
        "_from": f"syntax_nodes/{parent_key}",
        "_to": f"syntax_nodes/{key}",
    }

    children = syntax.get("children", [])
    if children is None:
        children = []
    if not isinstance(children, list):
        fail(f"{decl_name}:{path}: children must be a list")
    for index, child in enumerate(children):
        if not isinstance(child, dict):
            fail(f"{decl_name}:{path}/{index}: child must be an object")
        yield from iter_ast_nodes(decl_name, child, key, path + (index,))


def arango_http_request(args: argparse.Namespace, method: str, path: str, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    url = f"{args.host.rstrip('/')}/_db/{args.database}{path}"
    data = None if payload is None else json.dumps(payload).encode("utf-8")
    request = urllib.request.Request(url, data=data, method=method, headers={"Content-Type": "application/json"})
    token = base64.b64encode(f"{args.user}:{args.password}".encode("utf-8")).decode("ascii")
    request.add_header("Authorization", f"Basic {token}")
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            raw = response.read().decode("utf-8")
            return json.loads(raw) if raw else {}
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", "replace")
        # Document create with conflict is OK when overwriteMode is unavailable.
        fail(f"HTTP {exc.code} {path}: {detail}")
    except urllib.error.URLError as exc:
        fail(f"HTTP connection failed for {path}: {exc}")


def ensure_collection_http(args: argparse.Namespace, name: str, edge: bool = False) -> None:
    collections = arango_http_request(args, "GET", "/_api/collection").get("result", [])
    if any(c.get("name") == name for c in collections):
        return
    arango_http_request(args, "POST", "/_api/collection", {"name": name, "type": 3 if edge else 2})


def put_doc_http(args: argparse.Namespace, collection: str, doc: dict[str, Any]) -> None:
    key = doc.get("_key")
    if not isinstance(key, str) or not key:
        fail(f"document for {collection} missing _key")
    path = f"/_api/document/{collection}?overwriteMode=replace"
    arango_http_request(args, "POST", path, doc)


def ingest_http(records: list[dict[str, Any]], args: argparse.Namespace) -> tuple[int, int, int]:
    for collection, edge in [
        ("syntax_decls", False), ("syntax_nodes", False),
        ("ast_child", True), ("decl_root", True),
    ]:
        ensure_collection_http(args, collection, edge=edge)

    decl_count = len(records)
    node_count = 0
    edge_count = 0
    for record in records:
        name = record["name"]
        keyword = record["keyword"]
        decl_key = stable_key("decl", name)
        root_key: str | None = None
        put_doc_http(args, "syntax_decls", {
            "_key": decl_key,
            "name": name,
            "keyword": keyword,
            "range": record.get("syntax", {}).get("range"),
            "layer": "syntax",
        })
        for node_doc, edge_doc in iter_ast_nodes(name, record["syntax"]):
            if root_key is None:
                root_key = node_doc["_key"]
            node_count += 1
            put_doc_http(args, "syntax_nodes", node_doc)
            if edge_doc is not None:
                edge_count += 1
                put_doc_http(args, "ast_child", edge_doc)
        if root_key is not None:
            edge_count += 1
            put_doc_http(args, "decl_root", {
                "_key": stable_key("decl_root", decl_key, root_key),
                "_from": f"syntax_decls/{decl_key}",
                "_to": f"syntax_nodes/{root_key}",
            })
    return decl_count, node_count, edge_count


def setup_arango(args: argparse.Namespace):
    try:
        from arango import ArangoClient  # type: ignore
    except ImportError as exc:
        fail("python-arango is required for --execute; install with `pip install python-arango`")
        raise exc

    client = ArangoClient(hosts=args.host)
    sys_db = client.db("_system", username=args.user, password=args.password)
    if not sys_db.has_database(args.database):
        sys_db.create_database(args.database)
    db = client.db(args.database, username=args.user, password=args.password)

    for collection in ["syntax_decls", "syntax_nodes"]:
        if not db.has_collection(collection):
            db.create_collection(collection)

    if not db.has_graph(args.graph):
        graph = db.create_graph(args.graph)
    else:
        graph = db.graph(args.graph)

    if not graph.has_edge_definition("ast_child"):
        graph.create_edge_definition(
            edge_collection="ast_child",
            from_vertex_collections=["syntax_nodes"],
            to_vertex_collections=["syntax_nodes"],
        )
    if not graph.has_edge_definition("decl_root"):
        graph.create_edge_definition(
            edge_collection="decl_root",
            from_vertex_collections=["syntax_decls"],
            to_vertex_collections=["syntax_nodes"],
        )
    return db, graph


def ingest(records: list[dict[str, Any]], args: argparse.Namespace) -> tuple[int, int, int]:
    if args.execute_http:
        return ingest_http(records, args)

    decl_count = len(records)
    node_count = 0
    edge_count = 0

    if args.execute:
        db, graph = setup_arango(args)
        decls = db.collection("syntax_decls")
        nodes = db.collection("syntax_nodes")
        ast_edges = graph.edge_collection("ast_child")
        root_edges = graph.edge_collection("decl_root")
    else:
        decls = nodes = ast_edges = root_edges = None

    for record in records:
        name = record["name"]
        keyword = record["keyword"]
        decl_key = stable_key("decl", name)
        root_key: str | None = None
        decl_doc = {
            "_key": decl_key,
            "name": name,
            "keyword": keyword,
            "range": record.get("syntax", {}).get("range"),
            "layer": "syntax",
        }
        if decls is not None:
            decls.insert(decl_doc, overwrite=True)

        for node_doc, edge_doc in iter_ast_nodes(name, record["syntax"]):
            if root_key is None:
                root_key = node_doc["_key"]
            node_count += 1
            if nodes is not None:
                nodes.insert(node_doc, overwrite=True)
            if edge_doc is not None:
                edge_count += 1
                if ast_edges is not None:
                    try:
                        ast_edges.insert(edge_doc)
                    except Exception:
                        ast_edges.update(edge_doc)
        if root_key is not None:
            edge_count += 1
            if root_edges is not None:
                edge_doc = {
                    "_key": stable_key("decl_root", decl_key, root_key),
                    "_from": f"syntax_decls/{decl_key}",
                    "_to": f"syntax_nodes/{root_key}",
                }
                try:
                    root_edges.insert(edge_doc)
                except Exception:
                    root_edges.update(edge_doc)

    return decl_count, node_count, edge_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("jsonl", nargs="?", type=Path, help="DumpLeanGraph JSONL file; stdin if omitted")
    parser.add_argument("--execute", action="store_true", help="write to ArangoDB with python-arango; default is dry-run only")
    parser.add_argument("--execute-http", action="store_true", help="write to ArangoDB via HTTP API; no python-arango dependency")
    parser.add_argument("--host", default=os.getenv("ARANGO_URL") or os.getenv("ARANGO_ENDPOINT") or os.getenv("ARANGO_HOST", "http://127.0.0.1:8530"))
    parser.add_argument("--user", default=os.getenv("ARANGO_USERNAME") or os.getenv("ARANGO_USER", "root"))
    parser.add_argument("--password", default=os.getenv("ARANGO_PASSWORD", ""))
    parser.add_argument("--database", default=os.getenv("ARANGO_DATABASE") or os.getenv("ARANGO_DB", "infogeometry"))
    parser.add_argument("--graph", default=os.getenv("ARANGO_GRAPH", "LeanSyntaxGraph"))
    args = parser.parse_args()

    records = load_jsonl(args.jsonl)
    decls, nodes, edges = ingest(records, args)
    mode = "executed-http" if args.execute_http else ("executed" if args.execute else "dry-run")
    print(f"{mode}: declarations={decls} syntax_nodes={nodes} edges={edges}", file=sys.stderr)


if __name__ == "__main__":
    main()
