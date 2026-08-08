#!/usr/bin/env python3
"""Ingest syntax/environment bridge JSONL into ArangoDB.

Default mode is a dry run that validates the bridge schema and reports counts.
Use `--execute` to connect to ArangoDB and create edges from syntax declarations
to elaborated environment declarations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any


def fail(message: str) -> None:
    raise SystemExit(f"ingest_bridge_to_arango: {message}")


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


def stable_key(*parts: str) -> str:
    raw = "\x1f".join(parts)
    digest = hashlib.sha1(raw.encode("utf-8")).hexdigest()[:16]
    safe = "_".join(parts[:2])
    safe = "".join(ch if ch.isalnum() or ch in "_-" else "_" for ch in safe)
    safe = safe.strip("_")[:180]
    return f"{safe}_{digest}" if safe else digest


def env_decl_key(name: str) -> str:
    return name.replace(".", "_")


def load_bridge_jsonl(path: Path | None) -> list[dict[str, Any]]:
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
            validate_bridge_record(record, line_number)
            records.append(record)
    if not records:
        fail("no bridge records read")
    return records


def validate_bridge_record(record: dict[str, Any], line_number: int) -> None:
    if record.get("layer") != "syntax_env_bridge":
        fail(f"line {line_number}: expected layer='syntax_env_bridge'")
    name = record.get("name")
    if not isinstance(name, str) or not name:
        fail(f"line {line_number}: missing declaration name")
    matched = record.get("matched")
    if not isinstance(matched, bool):
        fail(f"line {line_number}: matched must be boolean")
    syntax = record.get("syntax")
    if not isinstance(syntax, dict):
        fail(f"line {line_number}: syntax must be object")
    keyword = syntax.get("keyword")
    if not isinstance(keyword, str) or not keyword:
        fail(f"line {line_number}: syntax.keyword must be nonempty string")
    env = record.get("env")
    if matched:
        if not isinstance(env, dict):
            fail(f"line {line_number}: matched record must have env object")
        if not isinstance(env.get("kind"), str) or not env.get("kind"):
            fail(f"line {line_number}: env.kind must be nonempty string")
        deps = env.get("deps")
        if not isinstance(deps, list) or not all(isinstance(dep, str) for dep in deps):
            fail(f"line {line_number}: env.deps must be string list")
    elif env is not None:
        fail(f"line {line_number}: unmatched record must have env=null")


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

    for collection in ["syntax_decls", "declarations"]:
        if not db.has_collection(collection):
            db.create_collection(collection)
    if not db.has_collection("syntax_elaborates_to"):
        db.create_collection("syntax_elaborates_to", edge=True)

    if not db.has_graph(args.graph):
        graph = db.create_graph(args.graph)
    else:
        graph = db.graph(args.graph)
    if not graph.has_edge_definition("syntax_elaborates_to"):
        graph.create_edge_definition(
            edge_collection="syntax_elaborates_to",
            from_vertex_collections=["syntax_decls"],
            to_vertex_collections=["declarations"],
        )
    return db, graph


def ingest(records: list[dict[str, Any]], args: argparse.Namespace) -> tuple[int, int, int]:
    matched = [record for record in records if record["matched"]]
    unmatched_count = len(records) - len(matched)

    if args.execute:
        db, graph = setup_arango(args)
        syntax_decls = db.collection("syntax_decls")
        env_decls = db.collection("declarations")
        bridge_edges = graph.edge_collection("syntax_elaborates_to")
    else:
        syntax_decls = env_decls = bridge_edges = None

    for record in matched:
        name = record["name"]
        syntax_key = stable_key("decl", name)
        env_key = env_decl_key(name)
        edge_doc = {
            "_key": stable_key("syntax_env_bridge", name),
            "_from": f"syntax_decls/{syntax_key}",
            "_to": f"declarations/{env_key}",
            "name": name,
            "syntaxKeyword": record["syntax"]["keyword"],
            "envKind": record["env"]["kind"],
            "envDeps": record["env"].get("deps", []),
        }
        if syntax_decls is not None:
            syntax_decls.insert(
                {
                    "_key": syntax_key,
                    "name": name,
                    "keyword": record["syntax"]["keyword"],
                    "range": record["syntax"].get("range"),
                    "layer": "syntax",
                },
                overwrite=True,
            )
        if env_decls is not None:
            env_decls.insert(
                {
                    "_key": env_key,
                    "name": name,
                    "kind": record["env"]["kind"],
                    "module": name.split(".")[0],
                },
                overwrite=True,
            )
        if bridge_edges is not None:
            bridge_edges.insert(edge_doc, overwrite=True)

    return len(records), len(matched), unmatched_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("jsonl", nargs="?", type=Path, help="bridge JSONL file; stdin if omitted")
    parser.add_argument("--execute", action="store_true", help="write to ArangoDB; default is dry-run only")
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
        args.graph = os.getenv("ARANGO_GRAPH") or "LeanSyntaxGraph"

    records = load_bridge_jsonl(args.jsonl)
    total, matched, unmatched = ingest(records, args)
    mode = "executed" if args.execute else "dry-run"
    print(
        f"{mode}: bridge_records={total} matched={matched} unmatched={unmatched}",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
