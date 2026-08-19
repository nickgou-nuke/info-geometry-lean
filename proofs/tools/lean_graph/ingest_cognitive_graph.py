#!/usr/bin/env python3
"""Ingest the compiled-theory AST/InfoTree overlay into the agent brain ArangoDB.

This is the second-ArangoDB cognitive graph lane. It is deliberately separate
from the theorem-authoritative Lean build: this script only records extracted
artifacts, source hashes, normalized source hashes, and dependency/DAG edges so
agents can query what remains vacuum-like and where external papers/code attach.

Default mode is a dry run. Add --execute to write to ArangoDB.

Default target:
  host:     http://localhost:8531
  database: agent_brain
  graph:    CompiledTheoryCognitiveGraph

Collections:
  lean_theorems      canonical declarations/theorems/deferred_interfaces from AST graph JSON
  ast_nodes          optional normalized AST/InfoTree nodes from syntax JSONL
  source_documents   external papers, markdown, bib, code, PDF metadata
  infotree_edges     declaration dependency/reference edges
  ast_child          syntax/InfoTree child edges
  source_links       source-document/code-to-theory similarity/provenance edges
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[3]
DEFAULT_GRAPH_JSON = ROOT / "all_lean_ast_graph.json"
DEFAULT_AST_JSON = ROOT / "proofs" / "ast_graph.json"
DEFAULT_INVENTORY_JSON = ROOT / "docs" / "INFOTREE_ARANGO_INVENTORY.json"

VERTEX_COLLECTIONS = ["lean_theorems", "ast_nodes", "source_documents"]
EDGE_COLLECTIONS = ["infotree_edges", "ast_child", "source_links"]
GRAPH_NAME = "CompiledTheoryCognitiveGraph"

VACUUM_TRIVIAL_RE = re.compile(
    r"\b(theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}?:\s*True\s*:=\s*trivial\b"
)
VACUUM_DEF_ZERO_RE = re.compile(r"\bdef\s+([A-Za-z0-9_'.]+)[^=]*?:\s*(?:Prop|ℕ|ℤ|ℚ|ℝ|ℂ|Q)\s*:=\s*0\b")
SORRY_RE = re.compile(r"\b(sorry|admit)\b")
COMMENT_BLOCK_RE = re.compile(r"/-[\s\S]*?-/")
COMMENT_LINE_RE = re.compile(r"--.*")
SPACE_RE = re.compile(r"\s+")
IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\b")


def is_relative_to(path: Path, parent: Path) -> bool:
    try:
        path.resolve().relative_to(parent.resolve())
        return True
    except ValueError:
        return False


def rel_to_root(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT.resolve()))
    except ValueError:
        return str(path)


def fail(message: str) -> None:
    raise SystemExit(f"ingest_cognitive_graph: {message}")


def load_env_file(path: Path | None) -> None:
    if path is None or not path.exists():
        return
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
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
    candidates: list[Path] = []
    if explicit is not None:
        candidates.append(explicit)
    for name in ("ARANGO_ENV_FILE", "HIVE_ARANGO_ENV_FILE", "AGENT_BRAIN_ARANGO_ENV_FILE"):
        if os.environ.get(name):
            candidates.append(Path(os.environ[name]))
    candidates.extend([
        Path("/home/goutev/.config/arango/env.sh"),
        ROOT / "configs" / "local" / "hive_arango.env",
    ])
    for candidate in candidates:
        load_env_file(candidate)
    aliases = [
        ("ARANGO_PASSWORD", "ARANGO_PASS"),
        ("ARANGO_USER", "ARANGO_USERNAME"),
        ("ARANGO_URL", "ARANGO_ENDPOINT"),
        ("ARANGO_HOST", "ARANGO_ENDPOINT"),
        ("ARANGO_DB", "ARANGO_DATABASE"),
    ]
    for left, right in aliases:
        if left not in os.environ and right in os.environ:
            os.environ[left] = os.environ[right]
        if right not in os.environ and left in os.environ:
            os.environ[right] = os.environ[left]


def safe_key(value: str, max_prefix: int = 180) -> str:
    digest = hashlib.sha1(value.encode("utf-8", errors="replace")).hexdigest()[:16]
    prefix = re.sub(r"[^A-Za-z0-9_:-]", "_", value).strip("_")[:max_prefix]
    return f"{prefix}_{digest}" if prefix else digest


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8", errors="replace")).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def normalize_source(text: str) -> str:
    """Heuristic source normalization for stable agent-side hashing.

    This is intentionally labelled as source_normalized_hash. It is not a
    replacement for Lean's elaborated Expr/InfoTree de-Bruijn representation;
    it is the graph-side companion hash used when compiled InfoTree records are
    not available as structured JSON.
    """
    text = COMMENT_BLOCK_RE.sub(" ", text)
    text = COMMENT_LINE_RE.sub(" ", text)
    text = SPACE_RE.sub(" ", text).strip()
    return text


def binder_shape(text: str) -> str:
    """Very conservative identifier abstraction for approximate De Bruijn shape."""
    keywords = {
        "theorem", "lemma", "def", "class", "structure", "inductive", "where", "by", "fun",
        "forall", "let", "in", "match", "with", "if", "then", "else", "True", "False",
        "Prop", "Type", "Sort", "sorry", "admit", "trivial", "rfl", "exact", "intro",
    }
    names: dict[str, str] = {}
    next_id = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal next_id
        token = match.group(0)
        if token in keywords or token[0].isupper():
            return token
        if token not in names:
            names[token] = f"v{next_id}"
            next_id += 1
        return names[token]

    return IDENT_RE.sub(repl, normalize_source(text))


def resolve_source_file(file_value: str | None) -> Path | None:
    if not file_value:
        return None
    raw = Path(file_value)
    candidates = []
    if raw.is_absolute():
        candidates.append(raw)
    candidates.extend([ROOT / raw, ROOT / "proofs" / raw])
    for candidate in candidates:
        if candidate.exists() and candidate.is_file():
            return candidate
    return None


def snippet_from_node(node: dict[str, Any]) -> tuple[str, str | None]:
    path = resolve_source_file(node.get("file") or node.get("path"))
    if path is None:
        return json.dumps(node, sort_keys=True, ensure_ascii=False), None
    text = path.read_text(encoding="utf-8", errors="replace")
    span = node.get("span")
    if isinstance(span, list) and len(span) == 2 and all(isinstance(x, int) for x in span):
        start, end = max(0, span[0]), max(0, span[1])
        if start < end <= len(text):
            return text[start:end], rel_to_root(path)
    return text, rel_to_root(path)


def classify_status(content: str) -> str:
    if VACUUM_TRIVIAL_RE.search(content) or VACUUM_DEF_ZERO_RE.search(content):
        return "Generalized_Sorry"
    if SORRY_RE.search(content):
        return "Contains_Sorry"
    return "Extracted"


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8", errors="replace"))


def load_compiled_theory(graph_json: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    if not graph_json.exists():
        fail(f"compiled theory graph JSON not found: {graph_json}")
    data = load_json(graph_json)
    if isinstance(data, list):
        raw_nodes = data
        raw_edges = []
        for node in raw_nodes:
            for dep in node.get("deps", []):
                raw_edges.append({"source": node.get("name"), "target": dep, "type": "depends_on"})
    elif isinstance(data, dict):
        raw_nodes = data.get("nodes", [])
        raw_edges = data.get("edges", data.get("links", []))
    else:
        fail(f"unsupported graph JSON root in {graph_json}")

    nodes: list[dict[str, Any]] = []
    id_to_key: dict[str, str] = {}
    name_to_key: dict[str, str] = {}
    for raw in raw_nodes:
        node_id = raw.get("id") or raw.get("name")
        name = raw.get("name") or node_id
        if not isinstance(node_id, str) or not isinstance(name, str):
            continue
        content, resolved_file = snippet_from_node(raw)
        normalized = normalize_source(content)
        db_shape = binder_shape(content)
        key = safe_key(node_id)
        doc = {
            "_key": key,
            "canonical_id": node_id,
            "lean_name": name,
            "kind": raw.get("kind") or raw.get("type") or "unknown",
            "type": raw.get("type") or raw.get("kind") or "unknown",
            "file": resolved_file or raw.get("file") or raw.get("path"),
            "span": raw.get("span"),
            "status": classify_status(content),
            "raw_source_hash": sha256_text(content),
            "source_normalized_hash": sha256_text(normalized),
            "de_bruijn_hash": sha256_text(db_shape),
            "normalization": "comments/positions/whitespace stripped; binder-name abstraction heuristic",
            "source_layer": "compiled_theory_ast_graph",
        }
        nodes.append(doc)
        id_to_key[node_id] = key
        name_to_key[name] = key

    edges: list[dict[str, Any]] = []
    for raw in raw_edges:
        source = raw.get("source") or raw.get("from") or raw.get("from_node")
        target = raw.get("target") or raw.get("to") or raw.get("to_node")
        if not isinstance(source, str) or not isinstance(target, str):
            continue
        source_key = id_to_key.get(source) or name_to_key.get(source)
        target_key = id_to_key.get(target) or name_to_key.get(target)
        if source_key is None or target_key is None:
            continue
        relation = raw.get("type") or raw.get("relation") or "depends_on"
        edges.append({
            "_key": safe_key(f"{source_key}->{relation}->{target_key}"),
            "_from": f"lean_theorems/{source_key}",
            "_to": f"lean_theorems/{target_key}",
            "relation": relation,
            "source_layer": "compiled_theory_ast_graph",
        })
    return nodes, edges


def load_parsed_ast_overlay(ast_json: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    if not ast_json.exists():
        return [], []
    data = load_json(ast_json)
    raw_nodes = data.get("nodes", []) if isinstance(data, dict) else []
    raw_edges = data.get("edges", data.get("links", [])) if isinstance(data, dict) else []
    name_to_key: dict[str, str] = {}
    nodes: list[dict[str, Any]] = []
    for raw in raw_nodes:
        name = raw.get("name")
        if not isinstance(name, str) or not name:
            continue
        key = safe_key(f"parsed::{name}")
        name_to_key[name] = key
        content = json.dumps(raw, sort_keys=True, ensure_ascii=False)
        nodes.append({
            "_key": key,
            "name": name,
            "kind": raw.get("kind") or raw.get("type") or "unknown",
            "type": raw.get("type") or raw.get("kind") or "unknown",
            "de_bruijn_hash": sha256_text(binder_shape(content)),
            "source_normalized_hash": sha256_text(normalize_source(content)),
            "source_layer": "parsed_ast_overlay",
        })
    edges: list[dict[str, Any]] = []
    for raw in raw_edges:
        source = raw.get("source") or raw.get("from") or raw.get("from_node")
        target = raw.get("target") or raw.get("to") or raw.get("to_node")
        if source in name_to_key and target in name_to_key:
            s, t = name_to_key[source], name_to_key[target]
            relation = raw.get("relation") or raw.get("type") or "depends_on"
            edges.append({
                "_key": safe_key(f"parsed::{s}->{relation}->{t}"),
                "_from": f"lean_theorems/{s}",
                "_to": f"lean_theorems/{t}",
                "relation": relation,
                "source_layer": "parsed_ast_overlay",
            })
    return nodes, edges


def iter_external_files(paths: list[Path], max_bytes: int) -> Iterable[Path]:
    suffixes = {".md", ".txt", ".bib", ".lean", ".py", ".sage", ".m2", ".json", ".pdf"}
    skip_parts = {".git", ".venv", "node_modules", ".lake", "__pycache__"}
    seen: set[Path] = set()
    for root in paths:
        if not root.exists():
            continue
        candidates = [root] if root.is_file() else root.rglob("*")
        for path in candidates:
            if not path.is_file() or path in seen:
                continue
            rel_parts = set(path.relative_to(ROOT).parts) if is_relative_to(path, ROOT) else set(path.parts)
            if rel_parts & skip_parts:
                continue
            if path.suffix.lower() not in suffixes:
                continue
            try:
                if path.stat().st_size > max_bytes and path.suffix.lower() != ".pdf":
                    continue
            except OSError:
                continue
            seen.add(path)
            yield path


def load_source_documents(external_paths: list[Path], max_bytes: int) -> list[dict[str, Any]]:
    docs: list[dict[str, Any]] = []
    for path in iter_external_files(external_paths, max_bytes=max_bytes):
        rel = rel_to_root(path)
        try:
            file_hash = sha256_file(path)
        except OSError:
            continue
        doc: dict[str, Any] = {
            "_key": safe_key(f"source::{rel}"),
            "path": rel,
            "suffix": path.suffix.lower(),
            "bytes": path.stat().st_size,
            "sha256": file_hash,
            "source_layer": "external_papers_and_code",
        }
        if path.suffix.lower() != ".pdf" and path.stat().st_size <= max_bytes:
            text = path.read_text(encoding="utf-8", errors="replace")
            doc["source_normalized_hash"] = sha256_text(normalize_source(text))
            doc["preview"] = normalize_source(text)[:500]
        docs.append(doc)
    return docs


def load_inventory_documents(inventory_json: Path) -> list[dict[str, Any]]:
    if not inventory_json.exists():
        return []
    data = load_json(inventory_json)
    if not isinstance(data, list):
        return []
    docs: list[dict[str, Any]] = []
    for item in data:
        path = item.get("path")
        if not isinstance(path, str):
            continue
        key = safe_key(f"inventory::{item.get('repo', 'auto')}::{path}")
        docs.append({
            "_key": key,
            "path": path,
            "repo": item.get("repo", "auto"),
            "role": item.get("role"),
            "note": item.get("note"),
            "tags": item.get("tags", []),
            "source_layer": "infotree_inventory",
        })
    return docs


def auth_header(user: str, password: str) -> str:
    token = base64.b64encode(f"{user}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"


@dataclass
class ArangoArgs:
    url: str
    database: str
    user: str
    password: str
    graph: str
    timeout: float


def request(args: ArangoArgs, method: str, path: str, body: Any | None = None, *, system: bool = False) -> Any:
    if system:
        url = args.url.rstrip("/") + path
    else:
        url = args.url.rstrip("/") + f"/_db/{urllib.parse.quote(args.database)}" + path
    data = None if body is None else json.dumps(body).encode("utf-8")
    headers = {"Authorization": auth_header(args.user, args.password)}
    if body is not None:
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=args.timeout) as resp:
            raw = resp.read().decode("utf-8")
            return json.loads(raw) if raw else {}
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", "replace")
        raise RuntimeError(f"HTTP {exc.code} {method} {url}: {detail}") from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(f"connection failed for {url}: {exc}") from exc


def ensure_database(args: ArangoArgs) -> None:
    try:
        request(args, "POST", "/_api/database", {"name": args.database}, system=True)
    except RuntimeError as exc:
        text = str(exc)
        if "duplicate name" in text or "1207" in text or "409" in text or "403" in text:
            return
        raise


def ensure_collection(args: ArangoArgs, name: str, edge: bool = False) -> None:
    try:
        request(args, "GET", f"/_api/collection/{urllib.parse.quote(name)}")
        return
    except RuntimeError as exc:
        if "404" not in str(exc):
            raise
    request(args, "POST", "/_api/collection", {"name": name, "type": 3 if edge else 2})


def ensure_graph(args: ArangoArgs) -> None:
    try:
        request(args, "GET", f"/_api/gharial/{urllib.parse.quote(args.graph)}")
        return
    except RuntimeError as exc:
        if "404" not in str(exc):
            raise
    edge_defs = [
        {"collection": "infotree_edges", "from": ["lean_theorems"], "to": ["lean_theorems"]},
        {"collection": "ast_child", "from": ["ast_nodes"], "to": ["ast_nodes"]},
        {"collection": "source_links", "from": ["source_documents"], "to": ["lean_theorems", "ast_nodes", "source_documents"]},
    ]
    request(args, "POST", "/_api/gharial", {"name": args.graph, "edgeDefinitions": edge_defs})


def put_many(args: ArangoArgs, collection: str, docs: list[dict[str, Any]], batch_size: int = 500) -> None:
    for offset in range(0, len(docs), batch_size):
        batch = docs[offset:offset + batch_size]
        request(args, "POST", f"/_api/document/{urllib.parse.quote(collection)}?overwriteMode=replace", batch)


def execute_ingest(args: ArangoArgs, payload: dict[str, list[dict[str, Any]]]) -> None:
    ensure_database(args)
    for collection in VERTEX_COLLECTIONS:
        ensure_collection(args, collection, edge=False)
    for collection in EDGE_COLLECTIONS:
        ensure_collection(args, collection, edge=True)
    ensure_graph(args)
    for collection in ["lean_theorems", "ast_nodes", "source_documents", "infotree_edges", "ast_child", "source_links"]:
        docs = payload.get(collection, [])
        if docs:
            put_many(args, collection, docs)


def main() -> None:
    parser = argparse.ArgumentParser(description="Ingest compiled Lean AST/InfoTree and external sources into agent_brain ArangoDB")
    parser.add_argument("--graph-json", type=Path, default=DEFAULT_GRAPH_JSON)
    parser.add_argument("--ast-json", type=Path, default=DEFAULT_AST_JSON)
    parser.add_argument("--inventory-json", type=Path, default=DEFAULT_INVENTORY_JSON)
    parser.add_argument("--external-root", type=Path, action="append", default=[], help="extra paper/code root to index; repeatable")
    parser.add_argument("--max-doc-bytes", type=int, default=2_000_000)
    parser.add_argument("--execute", action="store_true", help="write to ArangoDB; default is dry-run")
    parser.add_argument("--env-file", type=Path, default=None)
    parser.add_argument("--url", default=None)
    parser.add_argument("--database", default=None)
    parser.add_argument("--user", default=None)
    parser.add_argument("--password", default=None)
    parser.add_argument("--graph", default=None)
    parser.add_argument("--timeout", type=float, default=30.0)
    args = parser.parse_args()

    load_default_arango_env(args.env_file)
    url = args.url or os.getenv("AGENT_BRAIN_ARANGO_URL") or os.getenv("ARANGO_URL") or os.getenv("ARANGO_ENDPOINT") or "http://localhost:8531"
    database = args.database or os.getenv("AGENT_BRAIN_ARANGO_DB") or os.getenv("ARANGO_DB") or "agent_brain"
    user = args.user or os.getenv("AGENT_BRAIN_ARANGO_USER") or os.getenv("ARANGO_USER") or "root"
    password = args.password if args.password is not None else (
        os.getenv("AGENT_BRAIN_ARANGO_PASSWORD") or os.getenv("ARANGO_PASSWORD") or os.getenv("ARANGO_PASS") or ""
    )
    graph = args.graph or os.getenv("AGENT_BRAIN_ARANGO_GRAPH") or GRAPH_NAME

    lean_nodes, lean_edges = load_compiled_theory(args.graph_json)
    parsed_nodes, parsed_edges = load_parsed_ast_overlay(args.ast_json)

    default_external_roots = [ROOT / "external_refs", ROOT / "docs", ROOT]
    external_roots = args.external_root or default_external_roots
    source_docs = load_source_documents(external_roots, max_bytes=args.max_doc_bytes)
    inventory_docs = load_inventory_documents(args.inventory_json)
    source_by_key = {doc["_key"]: doc for doc in source_docs}
    for doc in inventory_docs:
        source_by_key[doc["_key"]] = doc
    source_docs = list(source_by_key.values())

    payload = {
        "lean_theorems": lean_nodes + parsed_nodes,
        "ast_nodes": [],
        "source_documents": source_docs,
        "infotree_edges": lean_edges + parsed_edges,
        "ast_child": [],
        "source_links": [],
    }

    print(
        "prepared cognitive graph payload: "
        f"lean_theorems={len(payload['lean_theorems'])} "
        f"infotree_edges={len(payload['infotree_edges'])} "
        f"source_documents={len(payload['source_documents'])} "
        f"target={url}/{database} graph={graph}",
        file=sys.stderr,
    )

    status_counts: dict[str, int] = {}
    for doc in payload["lean_theorems"]:
        status = str(doc.get("status", doc.get("type", "unknown")))
        status_counts[status] = status_counts.get(status, 0) + 1
    print(f"status counts: {json.dumps(status_counts, sort_keys=True)}", file=sys.stderr)

    if not args.execute:
        print("dry-run: add --execute to write the second ArangoDB cognitive graph", file=sys.stderr)
        return

    execute_ingest(ArangoArgs(url=url, database=database, user=user, password=password, graph=graph, timeout=args.timeout), payload)
    print("execute: cognitive graph upsert complete", file=sys.stderr)


if __name__ == "__main__":
    main()
