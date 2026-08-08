#!/usr/bin/env python3
"""Import docs/lean_module_graph.json into ArangoDB as a module import graph.

Creates/uses:
  vertex collection: lean_modules
  edge collection:   lean_imports
  graph:             LeanModuleImportGraph

Defaults can be overridden by env or flags:
  ARANGO_URL / ARANGO_HOST       default http://localhost:8529
  ARANGO_DB                      default info_geometry
  ARANGO_USER                    default root
  ARANGO_PASSWORD                default ""
  ARANGO_MODULE_GRAPH            default LeanModuleImportGraph

Dry-run by default. Add --execute to write via ArangoDB HTTP API.
No python-arango dependency required.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[3]
DEFAULT_JSON = ROOT / "docs" / "lean_module_graph.json"


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
        Path.home() / "GITHUB/info-geometry-lean/configs/local/hive_arango.env",
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


def safe_key(s: str) -> str:
    # Arango keys permit many punctuation chars, but keep this portable.
    return re.sub(r"[^A-Za-z0-9_:-]", "_", s)


def auth_header(user: str, password: str) -> str:
    token = base64.b64encode(f"{user}:{password}".encode()).decode()
    return f"Basic {token}"


def request(args: argparse.Namespace, method: str, path: str, body: Any | None = None) -> Any:
    url = args.url.rstrip("/") + path
    data = None if body is None else json.dumps(body).encode()
    headers = {"Authorization": auth_header(args.user, args.password)}
    if body is not None:
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=args.timeout) as resp:
            raw = resp.read().decode()
            return json.loads(raw) if raw else {}
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode(errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {method} {path}: {detail}") from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(f"Connection failed for {url}: {exc}") from exc


def db_path(args: argparse.Namespace, suffix: str) -> str:
    return f"/_db/{urllib.parse.quote(args.database)}/{suffix.lstrip('/')}"


def ensure_database(args: argparse.Namespace) -> None:
    # Database creation is a system endpoint; ignore already-exists errors.
    try:
        request(args, "POST", "/_api/database", {"name": args.database})
        print(f"created database {args.database}", file=sys.stderr)
    except RuntimeError as exc:
        msg = str(exc)
        if "duplicate name" in msg or "1207" in msg or "409" in msg:
            return
        # If using a non-root user lacking system DB permission, database may already exist.
        if "403" in msg:
            return
        raise


def collection_exists(args: argparse.Namespace, name: str) -> bool:
    try:
        request(args, "GET", db_path(args, f"/_api/collection/{urllib.parse.quote(name)}"))
        return True
    except RuntimeError as exc:
        if "404" in str(exc):
            return False
        raise


def ensure_collection(args: argparse.Namespace, name: str, edge: bool = False) -> None:
    if collection_exists(args, name):
        return
    request(args, "POST", db_path(args, "/_api/collection"), {"name": name, "type": 3 if edge else 2})
    print(f"created collection {name}", file=sys.stderr)


def ensure_index(args: argparse.Namespace, collection: str, fields: list[str], name: str) -> None:
    body = {"type": "persistent", "fields": fields, "name": name, "unique": False, "sparse": False}
    try:
        request(args, "POST", db_path(args, f"/_api/index?collection={urllib.parse.quote(collection)}"), body)
    except RuntimeError as exc:
        if "duplicate" not in str(exc).lower():
            raise


def ensure_graph(args: argparse.Namespace) -> None:
    try:
        request(args, "GET", db_path(args, f"/_api/gharial/{urllib.parse.quote(args.graph)}"))
        return
    except RuntimeError as exc:
        if "404" not in str(exc):
            raise
    body = {
        "name": args.graph,
        "edgeDefinitions": [
            {
                "collection": args.edge_collection,
                "from": [args.vertex_collection],
                "to": [args.vertex_collection],
            }
        ],
    }
    request(args, "POST", db_path(args, "/_api/gharial"), body)
    print(f"created graph {args.graph}", file=sys.stderr)


def put_doc(args: argparse.Namespace, collection: str, doc: dict[str, Any]) -> None:
    # POST with overwriteMode=replace is idempotent: insert if missing, replace if present.
    path = db_path(args, f"/_api/document/{urllib.parse.quote(collection)}?overwriteMode=replace")
    request(args, "POST", path, doc)


def load_graph(path: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    data = json.loads(path.read_text())
    nodes = data.get("nodes", [])
    edges = data.get("edges", [])
    return nodes, edges


def main() -> None:
    ap = argparse.ArgumentParser(description="Import Lean module import graph into ArangoDB")
    ap.add_argument("json_path", nargs="?", default=str(DEFAULT_JSON))
    ap.add_argument("--execute", action="store_true", help="write to ArangoDB; default is dry-run")
    ap.add_argument("--env-file", type=Path, default=None, help="optional shell env file with ARANGO_* settings")
    ap.add_argument("--url", default=None)
    ap.add_argument("--database", default=None)
    ap.add_argument("--user", default=None)
    ap.add_argument("--password", default=None)
    ap.add_argument("--graph", default=None)
    ap.add_argument("--vertex-collection", default="lean_modules")
    ap.add_argument("--edge-collection", default="lean_imports")
    ap.add_argument("--timeout", type=float, default=20.0)
    args = ap.parse_args()

    load_default_arango_env(args.env_file)
    if args.url is None:
        args.url = os.getenv("ARANGO_URL") or os.getenv("ARANGO_ENDPOINT") or os.getenv("ARANGO_HOST") or "http://localhost:8529"
    if args.database is None:
        args.database = os.getenv("ARANGO_DB") or os.getenv("ARANGO_DATABASE") or "info_geometry"
    if args.user is None:
        args.user = os.getenv("ARANGO_USER") or os.getenv("ARANGO_USERNAME") or "root"
    if args.password is None:
        args.password = os.getenv("ARANGO_PASSWORD") or os.getenv("ARANGO_PASS") or ""
    if args.graph is None:
        args.graph = os.getenv("ARANGO_MODULE_GRAPH") or "LeanModuleImportGraph"

    nodes, edges = load_graph(Path(args.json_path))
    print(f"module graph: nodes={len(nodes)} edges={len(edges)}")

    if not args.execute:
        cats = sorted({n.get("category", "") for n in nodes})
        print(f"dry-run only. categories={len(cats)} graph={args.graph}")
        print("add --execute to create collections/graph and import documents")
        return

    ensure_database(args)
    ensure_collection(args, args.vertex_collection, edge=False)
    ensure_collection(args, args.edge_collection, edge=True)
    ensure_graph(args)
    ensure_index(args, args.vertex_collection, ["category"], "idx_category")
    ensure_index(args, args.vertex_collection, ["path"], "idx_path")
    ensure_index(args, args.edge_collection, ["from", "to"], "idx_from_to_names")

    for n in nodes:
        key = safe_key(n["id"])
        doc = {
            "_key": key,
            "name": n["id"],
            "path": n.get("path"),
            "category": n.get("category"),
            "localImports": n.get("imports", []),
            "localImportCount": len(n.get("imports", [])),
            "kind": "lean_module",
        }
        put_doc(args, args.vertex_collection, doc)

    for e in edges:
        src = safe_key(e["from"])
        tgt = safe_key(e["to"])
        doc = {
            "_key": safe_key(f"{src}__imports__{tgt}"),
            "_from": f"{args.vertex_collection}/{src}",
            "_to": f"{args.vertex_collection}/{tgt}",
            "from": e["from"],
            "to": e["to"],
            "kind": "imports",
        }
        put_doc(args, args.edge_collection, doc)

    print(f"imported Lean module graph into {args.database}/{args.graph}: nodes={len(nodes)} edges={len(edges)}")


if __name__ == "__main__":
    main()
