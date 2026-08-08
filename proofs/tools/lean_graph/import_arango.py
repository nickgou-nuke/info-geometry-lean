#!/usr/bin/env python3
"""Import the GEPA Lean universe graph into ArangoDB.

Schema:
  vertices: lean_decls, syntax_nodes
  edges:    references, ast_child, has_syntax

Default mode is a dry run: it validates input and reports graph sizes without
requiring ArangoDB or python-arango.  Use `--execute` to write to ArangoDB.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any, Iterable


VALID_NODE_KINDS = {"node", "atom", "ident"}


def fail(message: str) -> None:
    raise SystemExit(f"import_arango: {message}")


def load_env_file(path: Path | None) -> None:
    if path is None or not path.exists():
        return
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export ") :].strip()
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip().strip('"').strip("'")
        if key and key not in os.environ:
            os.environ[key] = value


def load_default_arango_env(explicit: Path | None) -> None:
    candidates = []
    if explicit is not None:
        candidates.append(explicit)
    for name in ("ARANGO_ENV_FILE", "HIVE_ARANGO_ENV_FILE"):
        value = os.environ.get(name)
        if value:
            candidates.append(Path(value))
    candidates.extend([
        Path("/home/goutev/.config/arango/env.sh"),
        Path(__file__).resolve().parent / "env.sh",
        Path("/home/goutev/auto/configs/local/hive_arango.env"),
    ])
    for candidate in candidates:
        load_env_file(candidate)
    if "ARANGO_PASSWORD" not in os.environ and "ARANGO_PASS" in os.environ:
        os.environ["ARANGO_PASSWORD"] = os.environ["ARANGO_PASS"]
    if "ARANGO_PASS" not in os.environ and "ARANGO_PASSWORD" in os.environ:
        os.environ["ARANGO_PASS"] = os.environ["ARANGO_PASSWORD"]
    if "ARANGO_USER" not in os.environ and "ARANGO_USERNAME" in os.environ:
        os.environ["ARANGO_USER"] = os.environ["ARANGO_USERNAME"]
    if "ARANGO_USERNAME" not in os.environ and "ARANGO_USER" in os.environ:
        os.environ["ARANGO_USERNAME"] = os.environ["ARANGO_USER"]
    if "ARANGO_HOST" not in os.environ and "ARANGO_ENDPOINT" in os.environ:
        os.environ["ARANGO_HOST"] = os.environ["ARANGO_ENDPOINT"]
    if "ARANGO_URL" not in os.environ and "ARANGO_ENDPOINT" in os.environ:
        os.environ["ARANGO_URL"] = os.environ["ARANGO_ENDPOINT"]
    if "ARANGO_DB" not in os.environ and "ARANGO_DATABASE" in os.environ:
        os.environ["ARANGO_DB"] = os.environ["ARANGO_DATABASE"]


def stable_key(*parts: str) -> str:
    raw = "\x1f".join(parts)
    digest = hashlib.sha1(raw.encode("utf-8")).hexdigest()[:16]
    safe = "_".join(parts[:2])
    safe = "".join(ch if (ch.isascii() and ch.isalnum()) or ch in "_-" else "_" for ch in safe)
    safe = safe.strip("_")[:180]
    return f"{safe}_{digest}" if safe else digest


def decl_key(name: str) -> str:
    safe = name.replace(".", "_").replace("`", "_").replace("«", "").replace("»", "")
    # Replace any character not allowed in ArangoDB keys: [a-zA-Z0-9_:-]
    result: list[str] = []
    for ch in safe:
        if ch.isascii() and (ch.isalnum() or ch in "_:-"):
            result.append(ch)
        else:
            result.append("_")
    return "".join(result).strip("_")[:200]


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                fail(f"{path}:{line_number}: invalid JSONL: {exc}")
            records.append(record)
    if not records:
        fail(f"{path}: no records")
    return records


def validate_syntax_tree(name: str, node: Any, path: tuple[int, ...] = ()) -> None:
    if not isinstance(node, dict):
        fail(f"{name}:{path}: syntax node must be object")
    kind = node.get("kind")
    if kind not in VALID_NODE_KINDS:
        fail(f"{name}:{path}: invalid syntax node kind {kind!r}")
    if not isinstance(node.get("syntaxKind"), str):
        fail(f"{name}:{path}: syntaxKind must be string")
    children = node.get("children", [])
    if children is None:
        children = []
    if not isinstance(children, list):
        fail(f"{name}:{path}: children must be list")
    for index, child in enumerate(children):
        validate_syntax_tree(name, child, path + (index,))


def load_bridge(path: Path) -> list[dict[str, Any]]:
    records = load_jsonl(path)
    for index, record in enumerate(records, start=1):
        if record.get("layer") != "syntax_env_bridge":
            fail(f"{path}:{index}: expected layer='syntax_env_bridge'")
        name = record.get("name")
        if not isinstance(name, str) or not name:
            fail(f"{path}:{index}: missing name")
        if not isinstance(record.get("matched"), bool):
            fail(f"{path}:{index}: matched must be boolean")
        syntax = record.get("syntax")
        if not isinstance(syntax, dict):
            fail(f"{path}:{index}: syntax must be object")
        if record.get("matched") and not isinstance(record.get("env"), dict):
            fail(f"{path}:{index}: matched bridge record missing env object")
        syntax_tree = record.get("syntaxTree")
        if syntax_tree is not None:
            validate_syntax_tree(name, syntax_tree)
    return records


def load_syntax_jsonl(path: Path) -> dict[str, dict[str, Any]]:
    records: dict[str, dict[str, Any]] = {}
    for index, record in enumerate(load_jsonl(path), start=1):
        if record.get("layer") != "syntax":
            fail(f"{path}:{index}: expected layer='syntax'")
        name = record.get("name")
        if not isinstance(name, str) or not name:
            fail(f"{path}:{index}: missing syntax name")
        syntax = record.get("syntax")
        if not isinstance(syntax, dict):
            fail(f"{path}:{index}: missing syntax tree")
        validate_syntax_tree(name, syntax)
        records[name] = record
    return records


def load_env_json(path: Path) -> dict[str, dict[str, Any]]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail(f"{path}: invalid environment JSON: {exc}")
    if not isinstance(raw, list):
        fail(f"{path}: expected environment JSON array")
    records: dict[str, dict[str, Any]] = {}
    for index, record in enumerate(raw):
        if not isinstance(record, dict):
            fail(f"{path}:{index}: env record must be object")
        name = record.get("name")
        if not isinstance(name, str) or not name:
            fail(f"{path}:{index}: missing env name")
        records[name] = record
    return records


def bridge_from_syntax_env(syntax_path: Path, env_path: Path) -> list[dict[str, Any]]:
    syntax_records = load_syntax_jsonl(syntax_path)
    env_records = load_env_json(env_path)
    all_names = sorted(set(syntax_records) | set(env_records))
    bridged: list[dict[str, Any]] = []
    for name in all_names:
        syntax = syntax_records.get(name)
        env = env_records.get(name)
        bridged.append({
            "layer": "syntax_env_bridge",
            "name": name,
            "matched": env is not None,
            "syntax": {
                "keyword": syntax.get("keyword") if syntax is not None else "env_only",
                "range": syntax.get("syntax", {}).get("range") if syntax is not None else None,
            },
            "env": None if env is None else {
                "kind": env.get("kind"),
                "deps": env.get("deps", []),
            },
            "syntaxTree": syntax.get("syntax") if syntax is not None else None,
        })
    if not bridged:
        fail("syntax/env bridge produced no records")
    return bridged


def iter_ast_nodes(
    decl_name: str,
    syntax: dict[str, Any],
    parent_key: str | None = None,
    path: tuple[int, ...] = (),
) -> Iterable[tuple[dict[str, Any], dict[str, str] | None]]:
    path_str = "/".join(map(str, path)) if path else "root"
    kind = syntax["kind"]
    syntax_kind = syntax["syntaxKind"]
    key = stable_key("syntax", decl_name, path_str, kind, syntax_kind)
    doc: dict[str, Any] = {
        "_key": key,
        "declName": decl_name,
        "path": path_str,
        "nodeKind": kind,
        "syntaxKind": syntax_kind,
        "range": syntax.get("range"),
    }
    if kind == "atom":
        doc["atom"] = syntax.get("value", "")
    elif kind == "ident":
        doc["ident"] = syntax.get("raw", "")
    yield doc, None if parent_key is None else {
        "_key": stable_key("ast_child", parent_key, key),
        "_from": f"syntax_nodes/{parent_key}",
        "_to": f"syntax_nodes/{key}",
    }

    children = syntax.get("children", []) or []
    for index, child in enumerate(children):
        yield from iter_ast_nodes(decl_name, child, key, path + (index,))


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

    for collection in ["lean_decls", "syntax_nodes"]:
        if not db.has_collection(collection):
            db.create_collection(collection)

    if not db.has_graph(args.graph):
        graph = db.create_graph(args.graph)
    else:
        graph = db.graph(args.graph)

    edge_defs = {
        "references": (["lean_decls"], ["lean_decls"]),
        "ast_child": (["syntax_nodes"], ["syntax_nodes"]),
        "has_syntax": (["lean_decls"], ["syntax_nodes"]),
        "decl_root": (["lean_decls"], ["syntax_nodes"]),
    }
    for edge_name, (from_cols, to_cols) in edge_defs.items():
        if not graph.has_edge_definition(edge_name):
            graph.create_edge_definition(
                edge_collection=edge_name,
                from_vertex_collections=from_cols,
                to_vertex_collections=to_cols,
            )
    return db, graph


def import_records(records: list[dict[str, Any]], args: argparse.Namespace) -> dict[str, int]:
    counts = {
        "bridge_records": len(records),
        "lean_decls": 0,
        "matched_syntax_env": 0,
        "syntax_only": 0,
        "syntax_roots": 0,
        "syntax_nodes": 0,
        "references": 0,
        "ast_child": 0,
        "has_syntax": 0,
        "decl_root": 0,
    }

    if args.execute:
        db, graph = setup_arango(args)
        lean_decls = db.collection("lean_decls")
        syntax_nodes = db.collection("syntax_nodes")
        references = graph.edge_collection("references")
        ast_child = graph.edge_collection("ast_child")
        has_syntax = graph.edge_collection("has_syntax")
        decl_root = graph.edge_collection("decl_root")
    else:
        lean_decls = syntax_nodes = references = ast_child = has_syntax = decl_root = None

    for record in records:
        if not record["matched"]:
            counts["syntax_only"] += 1
            continue
        counts["lean_decls"] += 1
        name = record["name"]
        env = record["env"]
        source_key = decl_key(name)
        decl_doc = {
            "_key": source_key,
            "name": name,
            "kind": env.get("kind", "unknown"),
            "syntaxKeyword": record["syntax"].get("keyword"),
            "module": name.split(".")[0],
            "range": record["syntax"].get("range"),
        }
        if lean_decls is not None:
            lean_decls.insert(decl_doc, overwrite=True)

        for dep in env.get("deps", []):
            dep_key = decl_key(dep)
            counts["references"] += 1
            if lean_decls is not None:
                try:
                    lean_decls.insert({"_key": dep_key, "name": dep, "module": dep.split(".")[0]})
                except Exception:
                    pass  # full declaration metadata may already exist
            if references is not None:
                try:
                    references.insert({
                        "_key": stable_key("references", name, dep),
                        "_from": f"lean_decls/{source_key}",
                        "_to": f"lean_decls/{dep_key}",
                    })
                except Exception:
                    pass  # edge already exists

        syntax_tree = record.get("syntaxTree")
        if syntax_tree is None:
            continue
        counts["matched_syntax_env"] += 1
        root_key: str | None = None
        counts["syntax_roots"] += 1
        for node_doc, edge_doc in iter_ast_nodes(name, syntax_tree):
            if root_key is None:
                root_key = node_doc["_key"]
            counts["syntax_nodes"] += 1
            if syntax_nodes is not None:
                syntax_nodes.insert(node_doc, overwrite=True)
            if edge_doc is not None:
                counts["ast_child"] += 1
                if ast_child is not None:
                    try:
                        ast_child.insert(edge_doc)
                    except Exception:
                        pass  # edge already exists, skip
        if root_key is not None:
            counts["has_syntax"] += 1
            counts["decl_root"] += 1
            edge_doc = {
                "_key": stable_key("has_syntax", name, root_key),
                "_from": f"lean_decls/{source_key}",
                "_to": f"syntax_nodes/{root_key}",
            }
            if has_syntax is not None:
                try:
                    has_syntax.insert(edge_doc)
                except Exception:
                    pass  # edge already exists, skip
            if decl_root is not None:
                try:
                    decl_root.insert({**edge_doc, "_key": stable_key("decl_root", name, root_key)})
                except Exception:
                    pass
    return counts


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("bridge_jsonl", nargs="?", type=Path, help="syntax_env_bridge JSONL; use join_syntax_env.py --include-syntax-tree")
    parser.add_argument("--syntax-jsonl", type=Path, help="DumpLeanGraph syntax JSONL; alternative to bridge_jsonl")
    parser.add_argument("--env-json", type=Path, help="ExtractGraph environment JSON; used with --syntax-jsonl")
    parser.add_argument("--execute", action="store_true", help="write to ArangoDB; default is dry-run")
    parser.add_argument("--env-file", type=Path, default=None, help="optional shell env file with ARANGO_* settings")
    parser.add_argument("--host", default=None)
    parser.add_argument("--user", default=None)
    parser.add_argument("--password", default=None)
    parser.add_argument("--database", default=None)
    parser.add_argument("--graph", default=None)
    args = parser.parse_args()
    load_default_arango_env(args.env_file)
    if args.host is None:
        args.host = os.getenv("ARANGO_URL") or os.getenv("ARANGO_ENDPOINT") or os.getenv("ARANGO_HOST") or "http://localhost:8529"
    if args.user is None:
        args.user = os.getenv("ARANGO_USERNAME") or os.getenv("ARANGO_USER") or "root"
    if args.password is None:
        args.password = os.getenv("ARANGO_PASSWORD") or os.getenv("ARANGO_PASS") or "password"
    if args.database is None:
        args.database = os.getenv("ARANGO_DATABASE") or os.getenv("ARANGO_DB") or "info_geometry"
    if args.graph is None:
        args.graph = os.getenv("ARANGO_GRAPH") or "LeanUniverseGraph"

    if args.bridge_jsonl is not None:
        records = load_bridge(args.bridge_jsonl)
    elif args.syntax_jsonl is not None and args.env_json is not None:
        records = bridge_from_syntax_env(args.syntax_jsonl, args.env_json)
    else:
        fail("provide either bridge_jsonl or both --syntax-jsonl and --env-json")
    counts = import_records(records, args)
    mode = "executed" if args.execute else "dry-run"
    print(f"{mode}: " + " ".join(f"{key}={value}" for key, value in counts.items()), file=sys.stderr)


if __name__ == "__main__":
    main()
