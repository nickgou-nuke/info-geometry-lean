#!/usr/bin/env python3
"""DAG/LeanTrail-first causal-apex memory interface for InfoGeometry agents.

This tool is an opt-in GraphRAG/nervous-system layer.  It does not replace the
Lean kernel, DAG exporter, or owner files.  Its records are navigation memory:
useful for recalling causal context, never proof evidence.

Defaults follow the existing repo Arango conventions:
- database/endpoint/user/password come from ``configs/local/hive_arango.env`` or
  ARANGO_* environment variables via ``tools.infra.arango_env``;
- the authoritative refresh lane is ``dagRefresh`` / ``dagDoctor`` /
  ``artifacts/dag/index`` with raw/lossless overlays and LeanTrail navigation;
- ``ig_nodes`` / ``ig_edges`` are a stale-prone compact retrieval projection,
  never the proof-topology authority;
- causal memory is written to separate ``causal_apex`` and
  ``causal_memory_edges`` collections;
- bounded theorem/repo preflight is available through the ``preflight``
  subcommand only when a caller explicitly accepts projection-cache semantics.
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
    from tools.infra.openclaw_lean_brain_ingest import hash_embedding  # type: ignore
    from tools.infra.leansearch_local import search_records as _leansearch  # type: ignore
else:
    from .arango_env import (
        arango_database,
        arango_endpoint,
        arango_password,
        arango_username,
        load_repo_arango_env,
    )
    from .openclaw_lean_brain_ingest import hash_embedding
    from .leansearch_local import search_records as _leansearch


WRITE_AQL_RE = re.compile(r"\b(INSERT|UPDATE|UPSERT|REMOVE|REPLACE)\b", re.IGNORECASE)
COLLECTION_NAME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_-]*$")
LOCAL_TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']{1,}")


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


def validate_collection_name(name: str, label: str = "collection") -> str:
    """Reject malformed collection names before they reach AQL bindings."""
    if not COLLECTION_NAME_RE.fullmatch(name):
        raise ArangoError(f"Invalid {label}: {name!r}")
    return name


def normalize_embedding(raw: Any) -> list[float]:
    """Parse and validate a non-empty numeric embedding vector."""
    if not isinstance(raw, list) or not raw:
        raise ArangoError("prompt embedding must be a non-empty JSON array of numbers")
    out: list[float] = []
    for idx, value in enumerate(raw):
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            raise ArangoError(f"prompt embedding entry {idx} is not numeric")
        out.append(float(value))
    return out


def parse_embedding_arg(raw: str) -> list[float]:
    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"--prompt-embedding must be JSON: {exc}") from exc
    try:
        return normalize_embedding(parsed)
    except ArangoError as exc:
        raise SystemExit(str(exc)) from exc


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

    def preflight(
        self,
        *,
        name: str,
        decl_collection: str,
        edge_collection: str,
        depth: int,
        limit: int,
    ) -> dict[str, Any]:
        query = """
        LET anchor = FIRST(
          FOR d IN @@decl_collection
            FILTER d.name == @name OR d._key == @name
            LIMIT 1
            RETURN d
        )
        LET out_rows = anchor == null ? [] : (
          FOR v, e, p IN 1..@depth OUTBOUND anchor @@edge_collection
            OPTIONS { bfs: true, uniqueVertices: "global" }
            LIMIT @limit
            RETURN {
              vertex_id: v._id,
              vertex_key: v._key,
              vertex_name: HAS(v, "name") ? v.name : null,
              edge_kind: HAS(e, "kind") ? e.kind : null,
              depth: LENGTH(p.edges)
            }
        )
        LET in_rows = anchor == null ? [] : (
          FOR v, e, p IN 1..@depth INBOUND anchor @@edge_collection
            OPTIONS { bfs: true, uniqueVertices: "global" }
            LIMIT @limit
            RETURN {
              vertex_id: v._id,
              vertex_key: v._key,
              vertex_name: HAS(v, "name") ? v.name : null,
              edge_kind: HAS(e, "kind") ? e.kind : null,
              depth: LENGTH(p.edges)
            }
        )
        RETURN {
          anchor: anchor == null ? null : {
            id: anchor._id,
            key: anchor._key,
            name: HAS(anchor, "name") ? anchor.name : null,
            graphKind: HAS(anchor, "graphKind") ? anchor.graphKind : null,
            kind: HAS(anchor, "kind") ? anchor.kind : null,
            module: HAS(anchor, "module") ? anchor.module : null
          },
          outbound: out_rows,
          inbound: in_rows,
          meta: {
            depth: @depth,
            per_direction_limit: @limit,
            decl_collection: @decl_collection,
            edge_collection: @edge_collection
          }
        }
        """
        bind_vars = {
            "@decl_collection": decl_collection,
            "decl_collection": decl_collection,
            "@edge_collection": edge_collection,
            "edge_collection": edge_collection,
            "name": name,
            "depth": depth,
            "limit": limit,
        }
        out = self.execute_aql(query, bind_vars, allow_write=False)
        out["authority"] = {
            "level": "projection_cache_not_authority",
            "preferred": [
                "tools/infra/dag_refresh.py",
                "tools/infra/dag_doctor.py",
                "artifacts/dag/index/decls.jsonl",
                "artifacts/dag/index/edges.jsonl",
                "leantrail",
            ],
            "warning": "ig_* AQL output is navigation only; Lean source and managed DAG artifacts decide truth.",
        }
        return out

    def execute_graph_attention(
        self,
        prompt_embedding: list[float],
        decl_collection: str = "ig_nodes",
        edge_collection: str = "ig_edges",
        limit: int = 5,
        depth: int = 2,
    ) -> dict[str, Any]:
        """Run explicit read-only Q·K attention over embedded projection nodes.

        This is stale-prone retrieval/navigation only.  Prefer local-attention
        or local-neighborhood for theorem work unless the Arango projection was
        just rebuilt from the managed DAG lane.
        """
        validate_collection_name(decl_collection, "decl_collection")
        validate_collection_name(edge_collection, "edge_collection")
        prompt = normalize_embedding(prompt_embedding)
        query = """
        LET query_dim = LENGTH(@prompt_embedding)
        FOR node IN @@decl_collection
          FILTER HAS(node, "embedding")
          FILTER IS_LIST(node.embedding)
          FILTER LENGTH(node.embedding) == query_dim
          LET attention_score = COSINE_SIMILARITY(@prompt_embedding, node.embedding)
          SORT attention_score DESC
          LIMIT @limit
          LET value_graph = (
            FOR v, e, p IN 1..@depth OUTBOUND node @@edge_collection
              OPTIONS { bfs: true, uniqueVertices: "path" }
              LIMIT @context_limit
              RETURN {
                node_id: v._id,
                node_key: v._key,
                node_name: HAS(v, "name") ? v.name : null,
                relationship: HAS(e, "kind") ? e.kind : (HAS(e, "type") ? e.type : null),
                file: HAS(v, "file") ? v.file : null,
                depth: LENGTH(p.edges)
              }
          )
          RETURN {
            anchor_node: node._id,
            anchor_key: node._key,
            anchor_name: HAS(node, "name") ? node.name : null,
            attention_score: attention_score,
            file: HAS(node, "file") ? node.file : null,
            downstream_context: value_graph
          }
        """
        bind_vars = {
            "@decl_collection": decl_collection,
            "@edge_collection": edge_collection,
            "prompt_embedding": prompt,
            "limit": max(1, int(limit)),
            "depth": max(1, int(depth)),
            "context_limit": max(1, int(limit)) * max(1, int(depth)) * 8,
        }
        out = self.execute_aql(query, bind_vars, allow_write=False)
        out["authority"] = {
            "level": "projection_cache_not_authority",
            "preferred": [
                "local-attention",
                "local-search",
                "local-neighborhood",
                "artifacts/dag/index",
                "leantrail",
            ],
            "warning": "attention-preflight over ig_* is a projection-cache query, not authoritative graph truth.",
        }
        return out

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


def local_dag_paths(index_dir: str | Path | None = None) -> tuple[Path, Path]:
    base = Path(index_dir) if index_dir else _repo_root() / "artifacts" / "dag" / "index"
    return base / "decls.jsonl", base / "edges.jsonl"


def leantrail_paths(leantrail_dir: str | Path | None = None) -> dict[str, Path]:
    base = Path(leantrail_dir) if leantrail_dir else _repo_root() / "artifacts" / "leantrail"
    return {
        "snapshot": base / "graph_snapshot.json",
        "metadata": base / "arango" / "metadata.json",
        "nodes": base / "arango" / "ig_nodes.jsonl",
        "edges": base / "arango" / "ig_edges.jsonl",
    }


def artifact_status(path: Path) -> dict[str, Any]:
    exists = path.exists()
    out: dict[str, Any] = {"path": str(path), "exists": exists}
    if exists:
        stat = path.stat()
        out["bytes"] = stat.st_size
        out["mtime_unix"] = int(stat.st_mtime)
    return out


def load_local_decl_rows(index_dir: str | Path | None = None) -> list[dict[str, Any]]:
    decls_path, _ = local_dag_paths(index_dir)
    if not decls_path.exists():
        raise FileNotFoundError(f"local DAG declaration index not found: {decls_path}")
    rows: list[dict[str, Any]] = []
    with decls_path.open(encoding="utf-8") as handle:
        for line in handle:
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(row, dict):
                rows.append(row)
    return rows


def local_search(needle: str, *, index_dir: str | Path | None = None, limit: int = 30) -> list[dict[str, Any]]:
    needle_l = needle.lower()
    hits: list[dict[str, Any]] = []
    for row in load_local_decl_rows(index_dir):
        hay = " ".join(str(row.get(k, "")) for k in ("name", "module", "file", "kind")).lower()
        if needle_l in hay:
            hits.append({k: row.get(k) for k in ("name", "kind", "module", "file", "line")})
            if len(hits) >= limit:
                break
    return hits


def local_query_tokens(query: str) -> list[str]:
    raw = " ".join(re.sub(r"([a-z])([A-Z])", r"\1 \2", part) for part in query.replace(".", " ").replace("_", " ").split())
    seen: set[str] = set()
    out: list[str] = []
    for tok in LOCAL_TOKEN_RE.findall(raw.lower()):
        if tok not in seen:
            seen.add(tok)
            out.append(tok)
    return out


def local_attention(
    query: str,
    *,
    index_dir: str | Path | None = None,
    limit: int = 10,
    depth: int = 1,
) -> dict[str, Any]:
    """DAG-native lexical attention over artifacts/dag/index.

    This intentionally avoids live ``ig_nodes`` / ``ig_edges``.  It is a bounded
    navigation pass over current DAG declaration rows, with optional hydration
    from current DAG edge rows.
    """
    q_tokens = local_query_tokens(query)
    hits: list[tuple[float, dict[str, Any], list[str]]] = []
    for row in load_local_decl_rows(index_dir):
        name = str(row.get("name") or "")
        hay_fields = {
            "name": name,
            "module": str(row.get("module") or ""),
            "file": str(row.get("file") or ""),
            "kind": str(row.get("kind") or ""),
            "doc": str(row.get("doc") or ""),
        }
        hay = " ".join(hay_fields.values()).lower()
        name_l = name.lower()
        matched = [tok for tok in q_tokens if tok in hay]
        if not matched:
            continue
        score = 0.0
        for tok in matched:
            score += 6.0 if tok in name_l else 1.0
            if tok in hay_fields["module"].lower():
                score += 2.0
            if tok == hay_fields["kind"].lower():
                score += 1.0
        hits.append((score, row, matched))
    hits.sort(key=lambda item: (-item[0], str(item[1].get("name") or "")))
    hydrated = []
    for rank, (score, row, matched) in enumerate(hits[: max(1, limit)], start=1):
        name = str(row.get("name") or "")
        neighborhood = local_neighborhood(name, index_dir=index_dir, depth=depth, limit=40) if name else {}
        hydrated.append({
            "rank": rank,
            "score": score,
            "matchedTokens": matched,
            "name": name,
            "kind": row.get("kind"),
            "module": row.get("module"),
            "file": row.get("file"),
            "line": row.get("line"),
            "neighborhood": neighborhood,
        })
    return {
        "schema": "info_geometry.local_dag_attention.v1",
        "authority": "artifacts/dag/index navigation; Lean owner files decide truth",
        "query": query,
        "queryTokens": q_tokens,
        "source": "artifacts/dag/index/{decls,edges}.jsonl",
        "hits": hydrated,
    }


def local_neighborhood(
    name: str,
    *,
    index_dir: str | Path | None = None,
    depth: int = 1,
    limit: int = 80,
) -> dict[str, Any]:
    decl_rows = load_local_decl_rows(index_dir)
    decls = {str(row.get("name")): row for row in decl_rows if row.get("name")}
    _, edges_path = local_dag_paths(index_dir)
    if not edges_path.exists():
        raise FileNotFoundError(f"local DAG edge index not found: {edges_path}")

    exact = name if name in decls else None
    if exact is None:
        matches = [n for n in decls if name.lower() in n.lower()]
        if len(matches) == 1:
            exact = matches[0]
        else:
            return {"query": name, "resolved": None, "candidates": matches[:limit], "edges": []}

    frontier = {exact}
    seen = {exact}
    found_edges: list[dict[str, Any]] = []
    for _ in range(max(1, depth)):
        next_frontier: set[str] = set()
        with edges_path.open(encoding="utf-8") as handle:
            for line in handle:
                if not line.strip():
                    continue
                try:
                    row = json.loads(line)
                except json.JSONDecodeError:
                    continue
                src = str(row.get("src", ""))
                dst = str(row.get("dst", ""))
                if src in frontier or dst in frontier:
                    found_edges.append({"src": src, "dst": dst, "kind": row.get("kind")})
                    if len(found_edges) >= limit:
                        break
                    for node in (src, dst):
                        if node and node not in seen:
                            seen.add(node)
                            next_frontier.add(node)
        if len(found_edges) >= limit or not next_frontier:
            break
        frontier = next_frontier

    root_row = decls.get(exact, {})
    return {
        "query": name,
        "resolved": exact,
        "root": {k: root_row.get(k) for k in ("name", "kind", "module", "file", "line")},
        "node_count_seen": len(seen),
        "edges": found_edges,
    }


def local_preflight(
    query: str,
    *,
    index_dir: str | Path | None = None,
    leantrail_dir: str | Path | None = None,
    records_path: str | Path | None = None,
    depth: int = 1,
    limit: int = 10,
) -> dict[str, Any]:
    decls_path, edges_path = local_dag_paths(index_dir)
    leantrail = leantrail_paths(leantrail_dir)
    records = Path(records_path) if records_path else _repo_root() / "artifacts" / "leansearch_local" / "records.jsonl"

    search_hits = local_search(query, index_dir=index_dir, limit=max(1, int(limit)))
    attention = local_attention(
        query,
        index_dir=index_dir,
        limit=max(1, int(limit)),
        depth=max(1, int(depth)),
    )
    neighborhood: dict[str, Any] | None = None
    if search_hits:
        top_name = search_hits[0].get("name")
        if isinstance(top_name, str) and top_name:
            neighborhood = local_neighborhood(
                top_name,
                index_dir=index_dir,
                depth=max(1, int(depth)),
                limit=max(1, int(limit)),
            )

    return {
        "query": query,
        "authority": {
            "level": "dag_leantrail_navigation",
            "preferred": [
                "dagDoctor",
                "dagRefresh",
                "artifacts/dag/index/decls.jsonl",
                "artifacts/dag/index/edges.jsonl",
                "artifacts/leantrail/graph_snapshot.json",
                "artifacts/leantrail/arango/ig_nodes.jsonl",
                "artifacts/leantrail/arango/ig_edges.jsonl",
                "lean/ owner files + lake env lean",
            ],
            "warning": "Use DAG/LeanTrail for navigation and Lean source for truth; ig_* Arango collections are only a compact retrieval projection.",
        },
        "artifacts": {
            "dag": {
                "decls": artifact_status(decls_path),
                "edges": artifact_status(edges_path),
            },
            "leantrail": {name: artifact_status(path) for name, path in leantrail.items()},
            "leansearch_local": artifact_status(records),
        },
        "local_search": search_hits,
        "local_attention": attention,
        "local_neighborhood": neighborhood,
    }


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
    parser = argparse.ArgumentParser(description="DAG/LeanTrail-first causal-apex memory interface")
    add_common_args(parser)
    sub = parser.add_subparsers(dest="command", required=True)

    q = sub.add_parser("query", help="Run AQL. Read-only unless --allow-write is supplied.")
    q.add_argument("aql", help="AQL query string")
    q.add_argument("--bind-vars", default=None, help="JSON object of bind variables")
    q.add_argument("--allow-write", action="store_true", help="Permit INSERT/UPDATE/UPSERT/REMOVE/REPLACE AQL")
    q.add_argument("--batch-size", type=int, default=1000)

    ls = sub.add_parser("local-search", help="Search the local DAG index for a declaration")
    ls.add_argument("needle", help="Unique substring to search for")
    ls.add_argument("--index-dir", default=None, help="Override artifacts/dag/index")
    ls.add_argument("--limit", type=int, default=30)

    ln = sub.add_parser("local-neighborhood", help="Traverse current local DAG edges around a declaration")
    ln.add_argument("name", help="Exact declaration name, or unique substring")
    ln.add_argument("--index-dir", default=None, help="Override artifacts/dag/index")
    ln.add_argument("--depth", type=int, default=1)
    ln.add_argument("--limit", type=int, default=80)

    lp = sub.add_parser(
        "local-preflight",
        help="Run a DAG/LeanTrail-first navigation preflight without requiring live Arango",
    )
    lp.add_argument("query", help="Natural-language, declaration, module, or file query")
    lp.add_argument("--index-dir", default=None, help="Override artifacts/dag/index")
    lp.add_argument("--leantrail-dir", default=None, help="Override artifacts/leantrail")
    lp.add_argument("--records", default=None, help="Override artifacts/leansearch_local/records.jsonl")
    lp.add_argument("--depth", type=int, default=1)
    lp.add_argument("--limit", type=int, default=10)

    p = sub.add_parser(
        "preflight",
        help="Run a bounded declaration-neighborhood preflight on the legacy/projection Arango graph.",
    )
    p.add_argument("--name", required=True, help="Declaration name or projection-node _key")
    p.add_argument("--decl-collection", default=os.environ.get("ARANGO_DECL_COLLECTION", "ig_nodes"))
    p.add_argument("--edge-collection", default=os.environ.get("ARANGO_PREFLIGHT_EDGE_COLLECTION", "ig_edges"))
    p.add_argument("--depth", type=int, default=2)
    p.add_argument("--limit", type=int, default=25)
    p.add_argument(
        "--use-projection-cache",
        action="store_true",
        help="Required acknowledgement: query stale-prone ig_* projection cache instead of DAG/LeanTrail.",
    )

    ap = sub.add_parser(
        "attention-preflight",
        help="Explicit vector cross-correlation over legacy/projection Arango nodes",
    )
    ap_group = ap.add_mutually_exclusive_group(required=True)
    ap_group.add_argument("--prompt-embedding", default=None, help="JSON array of floats representing the query vector")
    ap_group.add_argument("--text-query", default=None, help="Plain text query; auto-generates hash embedding via openclaw_lean_brain_ingest.hash_embedding")
    ap.add_argument("--embedding-dim", type=int, default=384, help="Dimension for hash_embedding when using --text-query")
    ap.add_argument("--decl-collection", default=os.environ.get("ARANGO_DECL_COLLECTION", "ig_nodes"))
    ap.add_argument("--edge-collection", default=os.environ.get("ARANGO_PREFLIGHT_EDGE_COLLECTION", "ig_edges"))
    ap.add_argument("--depth", type=int, default=2)
    ap.add_argument("--limit", type=int, default=5)
    ap.add_argument(
        "--use-projection-cache",
        action="store_true",
        help="Required acknowledgement: query stale-prone ig_* projection cache instead of DAG/LeanTrail.",
    )

    la = sub.add_parser("local-attention", help="Offline DAG-native structural attention over artifacts/dag/index (no Arango needed)")
    la.add_argument("query", help="Natural-language or Lean declaration query")
    la.add_argument("--index-dir", default=None, help="Override artifacts/dag/index")
    la.add_argument("--depth", type=int, default=1, help="DAG neighborhood hydration depth for each hit")
    la.add_argument("--limit", type=int, default=10)
    la.add_argument("--records", default=None, help="Legacy: search prebuilt leansearch_local records instead of DAG rows")

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
    arango_commands = {"query", "preflight", "attention-preflight", "commit-apex"}
    client = ArangoCausalMemory(target_from_args(args)) if args.command in arango_commands else None

    try:
        if args.command == "query":
            assert client is not None
            out = client.execute_aql(
                args.aql,
                parse_json_arg(args.bind_vars),
                allow_write=args.allow_write,
                batch_size=args.batch_size,
            )
        elif args.command == "local-search":
            out = {
                "source": "artifacts/dag/index/decls.jsonl",
                "hits": local_search(args.needle, index_dir=args.index_dir, limit=args.limit),
            }
        elif args.command == "local-neighborhood":
            out = {
                "source": "artifacts/dag/index/{decls,edges}.jsonl",
                "neighborhood": local_neighborhood(
                    args.name,
                    index_dir=args.index_dir,
                    depth=args.depth,
                    limit=args.limit,
                ),
            }
        elif args.command == "local-preflight":
            out = local_preflight(
                args.query,
                index_dir=args.index_dir,
                leantrail_dir=args.leantrail_dir,
                records_path=args.records,
                depth=max(1, int(args.depth)),
                limit=max(1, int(args.limit)),
            )
        elif args.command == "preflight":
            if not args.use_projection_cache:
                raise SystemExit(
                    "preflight queries ig_* projection cache; use local-neighborhood/local-attention for DAG, "
                    "or pass --use-projection-cache explicitly"
                )
            assert client is not None
            out = client.preflight(
                name=args.name,
                decl_collection=args.decl_collection,
                edge_collection=args.edge_collection,
                depth=max(1, int(args.depth)),
                limit=max(1, int(args.limit)),
            )
        elif args.command == "attention-preflight":
            if not args.use_projection_cache:
                raise SystemExit(
                    "attention-preflight queries ig_* projection cache; use local-attention for DAG, "
                    "or pass --use-projection-cache explicitly"
                )
            assert client is not None
            if args.text_query:
                embedding = hash_embedding(args.text_query, dim=args.embedding_dim)
            else:
                embedding = parse_embedding_arg(args.prompt_embedding)
            out = client.execute_graph_attention(
                prompt_embedding=embedding,
                decl_collection=args.decl_collection,
                edge_collection=args.edge_collection,
                limit=max(1, int(args.limit)),
                depth=max(1, int(args.depth)),
            )
        elif args.command == "local-attention":
            if args.records:
                records_path = Path(args.records)
                out = {
                    "source": str(records_path),
                    "engine": "leansearch_local_tfidf_legacy_records",
                    "warning": "Prebuilt records may be stale; prefer default DAG mode unless just rebuilt from artifacts/dag/index.",
                    "result": _leansearch(records_path=records_path, query=args.query, top_k=args.limit),
                }
            else:
                out = local_attention(
                    args.query,
                    index_dir=args.index_dir,
                    limit=max(1, int(args.limit)),
                    depth=max(1, int(args.depth)),
                )
        elif args.command == "commit-apex":
            assert client is not None
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

    target = client.target.database if client is not None else "local"
    print(json.dumps({"ok": True, "target": target, "output": out}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
