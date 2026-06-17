#!/usr/bin/env python3
"""Optimize and smoke-test AST AQL queries for the local LeanTrail/GEPA graph.

This is the repo-local version of the `/home/goutev/auto` GEPA AST-AQL lane. It
uses the same Arango environment variables/config file as `arango_dump.py`, adds
persistent indexes for AST search fields, and runs bounded smoke queries.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Dict, List


def _read_arango_env_file() -> Dict[str, str]:
    env_path = Path.home() / ".config" / "arango" / "env.sh"
    values: Dict[str, str] = {}
    if not env_path.exists():
        return values
    for line in env_path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = line.strip()
        if line.startswith("export ") and "=" in line:
            k, v = line[len("export "):].split("=", 1)
            values[k.strip()] = v.strip().strip('"').strip("'")
    return values


_ENV_FILE = _read_arango_env_file()


def _env_default(*names: str, fallback: str) -> str:
    for name in names:
        if os.environ.get(name):
            return os.environ[name]
        if _ENV_FILE.get(name):
            return _ENV_FILE[name]
    return fallback


class ArangoHTTP:
    def __init__(self, endpoint: str, database: str, username: str, password: str):
        self.endpoint = endpoint.rstrip("/")
        self.database = database
        self.username = username
        self.password = password
        self.auth = "Basic " + base64.b64encode(f"{username}:{password}".encode()).decode()

    def request(self, path: str, payload: Dict[str, Any] | None = None, method: str = "POST") -> Dict[str, Any]:
        data = None if payload is None else json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            f"{self.endpoint}/_db/{self.database}{path}",
            data=data,
            headers={"Content-Type": "application/json", "Authorization": self.auth},
            method=method,
        )
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                return json.load(r)
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            raise RuntimeError(f"Arango HTTP {exc.code}: {detail}") from exc

    def aql(self, query: str, bind_vars: Dict[str, Any] | None = None) -> tuple[List[Any], float]:
        started = time.time()
        res = self.request("/_api/cursor", {
            "query": query,
            "bindVars": bind_vars or {},
            "batchSize": 10000,
        })
        if res.get("error"):
            raise RuntimeError(json.dumps(res, indent=2))
        rows = list(res.get("result", []))
        cursor = res.get("id")
        while res.get("hasMore") and cursor:
            res = self.request(f"/_api/cursor/{cursor}", method="PUT")
            if res.get("error"):
                raise RuntimeError(json.dumps(res, indent=2))
            rows.extend(res.get("result", []))
            cursor = res.get("id")
        return rows, time.time() - started

    def ensure_persistent_index(self, collection: str, fields: List[str]) -> Dict[str, Any]:
        return self.request(f"/_api/index?collection={collection}", {
            "type": "persistent",
            "fields": fields,
            "unique": False,
            "sparse": True,
        })


def optimize(db: ArangoHTTP) -> None:
    indexes = {
        "syntax_nodes": [
            ["declName"],
            ["atom"],
            ["ident"],
            ["value"],
            ["raw"],
            ["syntaxKind"],
            ["nodeKind"],
            ["declName", "path"],
        ],
        "syntax_decls": [["name"], ["keyword"]],
    }
    for coll, field_sets in indexes.items():
        for fields in field_sets:
            res = db.ensure_persistent_index(coll, fields)
            print(f"index {coll}{fields}: {res.get('isNewlyCreated', False)}")


def smoke(db: ArangoHTTP, decl: str, depth: int) -> None:
    queries = [
        ("counts", """
          RETURN {
            syntax_nodes: LENGTH(FOR n IN syntax_nodes RETURN 1),
            ast_child: LENGTH(FOR e IN ast_child RETURN 1),
            syntax_decls: LENGTH(FOR d IN syntax_decls RETURN 1),
            decl_root: LENGTH(FOR e IN decl_root RETURN 1)
          }
        """, {}),
        ("atom_first_sorry_scan", """
          FOR n IN syntax_nodes
            FILTER n.atom == "sorry" OR n.ident == "sorry" OR n.value == "sorry" OR n.raw == "sorry"
            LIMIT 20
            RETURN {decl: n.declName, range: n.range, token: FIRST([n.atom, n.ident, n.value, n.raw][* FILTER CURRENT != null])}
        """, {}),
        ("atom_first_tactic_scan", """
          FOR n IN syntax_nodes
            FILTER n.atom IN @tactics OR n.ident IN @tactics OR n.value IN @tactics OR n.raw IN @tactics
            LIMIT 20
            RETURN {decl: n.declName, range: n.range, tactic: FIRST([n.atom, n.ident, n.value, n.raw][* FILTER CURRENT != null])}
        """, {"tactics": ["simp", "rw", "exact", "simpa", "unfold", "dsimp"]}),
        ("bounded_decl_ast_cone", """
          FOR root IN syntax_nodes
            FILTER root.declName == @decl AND root.path == "root"
            LIMIT 1
            LET descendants = (
              FOR v IN 1..@depth OUTBOUND root ast_child
                OPTIONS {uniqueVertices: "path", bfs: true}
                RETURN v._id
            )
            RETURN {decl: root.declName, depth: @depth, descendants: LENGTH(descendants)}
        """, {"decl": decl, "depth": depth}),
    ]
    for name, q, bind in queries:
        rows, elapsed = db.aql(q, bind)
        print(f"\n{name}: {elapsed:.3f}s")
        print(json.dumps(rows[:3], indent=2, ensure_ascii=False))


def main() -> int:
    ap = argparse.ArgumentParser(description="Optimize/smoke-test AST AQL for LeanTrail GEPA graph")
    ap.add_argument("--endpoint", default=_env_default("ARANGO_ENDPOINT", "ARANGO_URL", fallback="http://127.0.0.1:8530"))
    ap.add_argument("--database", default=_env_default("ARANGO_DATABASE", "ARANGO_DB", fallback="infogeometry"))
    ap.add_argument("--username", default=_env_default("ARANGO_USERNAME", "ARANGO_USER", fallback="root"))
    ap.add_argument("--password", default=_env_default("ARANGO_PASSWORD", fallback=""))
    ap.add_argument("--decl", default="AffineDynkinGoutevTonev.affine_delta_cartan_quadratic_zero")
    ap.add_argument("--depth", type=int, default=10)
    ap.add_argument("--no-index", action="store_true", help="Only run smoke queries; do not create indexes")
    args = ap.parse_args()

    db = ArangoHTTP(args.endpoint, args.database, args.username, args.password)
    if not args.no_index:
        optimize(db)
    smoke(db, args.decl, args.depth)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
