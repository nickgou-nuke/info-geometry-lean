#!/usr/bin/env python3
"""ArangoDB causal-apex memory interface for InfoGeometry agents.

This tool is an opt-in GraphRAG/nervous-system layer.  It does not replace the
Lean kernel, DAG exporter, or owner files.  Its records are navigation memory:
useful for recalling causal context, never proof evidence.

Defaults follow the existing repo Arango conventions:
- database/endpoint/user/password come from ``configs/local/hive_arango.env`` or
  ARANGO_* environment variables via ``tools.infra.arango_env``;
- Lean declaration vertices are looked up in ``ig_nodes`` by ``name`` or ``_key``;
- causal memory is written to separate ``causal_apex`` and
  ``causal_memory_edges`` collections.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.arango_env import (  # type: ignore
        arango_database,
        arango_endpoint,
        arango_password,
        arango_username,
        load_repo_arango_env,
    )
else:
    from .arango_env import (
        arango_database,
        arango_endpoint,
        arango_password,
        arango_username,
        load_repo_arango_env,
    )


WRITE_AQL_RE = re.compile(r"\b(INSERT|UPDATE|UPSERT|REMOVE|REPLACE)\b", re.IGNORECASE)


@dataclass(frozen=True)
class ArangoTarget:
    endpoint: str
    database: str
    username: str
    password: str


class ArangoError(RuntimeError):
    pass


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


def default_target() -> ArangoTarget:
    load_repo_arango_env(_repo_root())
    return ArangoTarget(
        endpoint=(os.environ.get("ARANGO_ENDPOINT") or os.environ.get("ARANGO_URL") or arango_endpoint()).rstrip("/"),
        database=os.environ.get("ARANGO_DB") or os.environ.get("ARANGO_DATABASE") or arango_database(),
        username=os.environ.get("ARANGO_USER") or arango_username(),
        password=os.environ.get("ARANGO_PASSWORD") or os.environ.get("ARANGO_PASS") or arango_password(),
    )


def auth_header(target: ArangoTarget) -> str | None:
    if target.username == "" and target.password == "":
        return None
    token = base64.b64encode(f"{target.username}:{target.password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"


class ArangoCausalMemory:
    def __init__(self, target: ArangoTarget):
        self.target = target

    def _url(self, path: str) -> str:
        return f"{self.target.endpoint}/_db/{urllib.parse.quote(self.target.database)}/{path.lstrip('/')}"

    def request_json(
        self,
        method: str,
        path: str,
        payload: dict[str, Any] | None = None,
        *,
        timeout: int = 20,
    ) -> dict[str, Any]:
        data = None if payload is None else json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(self._url(path), data=data, method=method)
        req.add_header("Content-Type", "application/json")
        auth = auth_header(self.target)
        if auth:
            req.add_header("Authorization", auth)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                body = resp.read().decode("utf-8")
                return json.loads(body) if body else {}
        except urllib.error.HTTPError as exc:
            body = exc.read().decode("utf-8", errors="replace")
            try:
                parsed = json.loads(body)
            except json.JSONDecodeError:
                parsed = {"error": True, "errorMessage": body}
            raise ArangoError(f"HTTP {exc.code} {exc.reason}: {parsed}") from exc
        except urllib.error.URLError as exc:
            raise ArangoError(f"ArangoDB unreachable at {self.target.endpoint}: {exc}") from exc

    def collection_exists(self, name: str) -> bool:
        try:
            self.request_json("GET", f"_api/collection/{urllib.parse.quote(name)}")
            return True
        except ArangoError:
            return False

    def ensure_collection(self, name: str, *, edge: bool = False) -> None:
        if self.collection_exists(name):
            return
        payload = {"name": name, "type": 3 if edge else 2}
        self.request_json("POST", "_api/collection", payload)

    def execute_aql(
        self,
        query: str,
        bind_vars: dict[str, Any] | None = None,
        *,
        allow_write: bool = False,
        batch_size: int = 1000,
    ) -> dict[str, Any]:
        if not allow_write and WRITE_AQL_RE.search(query):
            raise ArangoError("Refusing write AQL without --allow-write")
        payload = {"query": query, "bindVars": bind_vars or {}, "batchSize": batch_size}
        first = self.request_json("POST", "_api/cursor", payload)
        result = list(first.get("result", []))
        cursor_id = first.get("id")
        has_more = bool(first.get("hasMore"))
        while has_more and cursor_id:
            page = self.request_json("PUT", f"_api/cursor/{cursor_id}", None)
            result.extend(page.get("result", []))
            has_more = bool(page.get("hasMore"))
            cursor_id = page.get("id", cursor_id)
        first["result"] = result
        first["hasMore"] = False
        return first

    def commit_apex(
        self,
        *,
        intent: str,
        files: list[str],
        deps: list[str],
        rules: list[str],
        commands: list[str],
        result: str | None,
        apex_collection: str,
        edge_collection: str,
        decl_collection: str,
        create_collections: bool,
    ) -> dict[str, Any]:
        if create_collections:
            self.ensure_collection(apex_collection, edge=False)
            self.ensure_collection(edge_collection, edge=True)

        query = """
        LET dep_docs = (
          FOR dep IN @deps
            LET by_key = DOCUMENT(@@decl_collection, dep)
            LET by_name = FIRST(
              FOR d IN @@decl_collection
                FILTER d.name == dep OR d._key == dep
                LIMIT 1
                RETURN d
            )
            LET doc = by_key != null ? by_key : by_name
            RETURN { dep: dep, doc: doc }
        )
        LET apex = FIRST(
          INSERT {
            type: "CausalApex",
            schema: "info_geometry.causal_apex.v1",
            intent: @intent,
            files_touched: @files,
            dependencies_requested: @deps,
            dependencies_resolved: dep_docs[* FILTER CURRENT.doc != null].dep,
            dependencies_unresolved: dep_docs[* FILTER CURRENT.doc == null].dep,
            rules: @rules,
            verification_commands: @commands,
            result: @result,
            created_unix_ms: DATE_NOW(),
            created_iso: DATE_ISO8601(DATE_NOW())
          } INTO @@apex_collection
          RETURN NEW
        )
        LET edges = (
          FOR row IN dep_docs
            FILTER row.doc != null
            INSERT {
              _from: apex._id,
              _to: row.doc._id,
              type: "DEPENDS_ON_PAST",
              role: "causal_reactivation_dependency",
              dep: row.dep,
              created_unix_ms: DATE_NOW()
            } INTO @@edge_collection
            RETURN NEW
        )
        RETURN { apex: apex, edges_created: LENGTH(edges), unresolved: apex.dependencies_unresolved }
        """
        bind_vars = {
            "@decl_collection": decl_collection,
            "@apex_collection": apex_collection,
            "@edge_collection": edge_collection,
            "intent": intent,
            "files": files,
            "deps": deps,
            "rules": rules,
            "commands": commands,
            "result": result,
        }
        return self.execute_aql(query, bind_vars, allow_write=True)


def parse_json_arg(raw: str | None) -> dict[str, Any]:
    if not raw:
        return {}
    try:
        obj = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"--bind-vars must be JSON: {exc}") from exc
    if not isinstance(obj, dict):
        raise SystemExit("--bind-vars must decode to an object")
    return obj


def add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--endpoint", default=None, help="Override ARANGO_ENDPOINT/ARANGO_URL")
    parser.add_argument("--database", default=None, help="Override ARANGO_DB/ARANGO_DATABASE")
    parser.add_argument("--user", default=None, help="Override ARANGO_USER")
    parser.add_argument("--password", default=None, help="Override ARANGO_PASSWORD/ARANGO_PASS")


def target_from_args(args: argparse.Namespace) -> ArangoTarget:
    base = default_target()
    return ArangoTarget(
        endpoint=(args.endpoint or base.endpoint).rstrip("/"),
        database=args.database or base.database,
        username=args.user if args.user is not None else base.username,
        password=args.password if args.password is not None else base.password,
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="ArangoDB causal-apex memory interface")
    add_common_args(parser)
    sub = parser.add_subparsers(dest="command", required=True)

    q = sub.add_parser("query", help="Run AQL. Read-only unless --allow-write is supplied.")
    q.add_argument("aql", help="AQL query string")
    q.add_argument("--bind-vars", default=None, help="JSON object of bind variables")
    q.add_argument("--allow-write", action="store_true", help="Permit INSERT/UPDATE/UPSERT/REMOVE/REPLACE AQL")
    q.add_argument("--batch-size", type=int, default=1000)

    c = sub.add_parser("commit-apex", help="Write a causal apex memory node and dependency edges")
    c.add_argument("--intent", required=True, help="Purified summary of the context apex")
    c.add_argument("--files", nargs="*", default=[], help="Files read/edited/validated")
    c.add_argument("--deps", nargs="*", default=[], help="Declaration names or _keys to link if present")
    c.add_argument("--rules", nargs="*", default=[], help="Operational rules active in this context")
    c.add_argument("--commands", nargs="*", default=[], help="Verification commands run")
    c.add_argument("--result", default=None, help="Verified result or suspension status")
    c.add_argument("--decl-collection", default=os.environ.get("ARANGO_DECL_COLLECTION", "ig_nodes"))
    c.add_argument("--apex-collection", default=os.environ.get("ARANGO_APEX_COLLECTION", "causal_apex"))
    c.add_argument("--edge-collection", default=os.environ.get("ARANGO_MEMORY_EDGE_COLLECTION", "causal_memory_edges"))
    c.add_argument("--no-create-collections", action="store_true", help="Do not create causal collections if missing")

    args = parser.parse_args(argv)
    client = ArangoCausalMemory(target_from_args(args))

    try:
        if args.command == "query":
            out = client.execute_aql(
                args.aql,
                parse_json_arg(args.bind_vars),
                allow_write=args.allow_write,
                batch_size=args.batch_size,
            )
        elif args.command == "commit-apex":
            out = client.commit_apex(
                intent=args.intent,
                files=args.files,
                deps=args.deps,
                rules=args.rules,
                commands=args.commands,
                result=args.result,
                apex_collection=args.apex_collection,
                edge_collection=args.edge_collection,
                decl_collection=args.decl_collection,
                create_collections=not args.no_create_collections,
            )
        else:  # pragma: no cover
            parser.error(f"unknown command {args.command}")
    except ArangoError as exc:
        print(json.dumps({"ok": False, "error": str(exc)}, indent=2), file=sys.stderr)
        return 2

    print(json.dumps({"ok": True, "target": client.target.database, "output": out}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
