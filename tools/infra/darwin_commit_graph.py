#!/usr/bin/env python3
"""Darwin commit-evolution taxonomy for ArangoDB.

Builds a dual-view graph:
- commit_nodes / commit_edges: repository commit history as evolutionary taxonomy
- commit_decl_edges: causal links from commits to decls DNA nodes

Boundaries:
- read-only by default; write only to commit_* collections
- never truncates decls/edges/raw_infotree_* collections
- uses repo arango env loader; no invented credential handling
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path
from typing import Iterable

from tools.infra.arango_env import (
    load_repo_arango_env,
    normalized_darwin_arango_env,
)

try:
    from arango.client import ArangoClient
except ImportError as e:
    raise SystemExit(f"python-arango not installed: {e}")


REPO_ROOT = Path(__file__).resolve().parents[2]


def _run_git(args: list[str]) -> str:
    raw = subprocess.check_output(
        ["git", *args], cwd=REPO_ROOT, stderr=subprocess.DEVNULL
    )
    # history blobs are not guaranteed UTF-8; parsing is navigation-grade
    return raw.decode("utf-8", errors="replace")


def _run_git_bytes(args: list[str]) -> bytes:
    return subprocess.check_output(
        ["git", *args], cwd=REPO_ROOT, stderr=subprocess.DEVNULL
    )


def _ensure_collections(db, database: str) -> None:
    for name, is_edge in (
        ("commit_nodes", False),
        ("commit_edges", True),
        ("commit_decl_edges", True),
        ("taxonomy_ranks", False),
    ):
        if db.has_collection(name):
            continue
        db.create_collection(name, edge=is_edge)
        print(f"[darwin] created collection {name}")


def _diff_record(commit: str) -> tuple[str, list[str], dict[str, list[str]]]:
    """Patch record for one commit: (diffHash, changed paths, added lines per path).

    ``git diff-tree -p`` is required: without ``-p`` no ``diff --git`` sections
    are emitted and path parsing would silently return an empty taxonomy for
    every commit.  ``--root`` keeps the initial commit visible.
    """
    raw = _run_git_bytes(["diff-tree", "-p", "--no-commit-id", "-r", "--root", commit])
    diff_hash = hashlib.sha256(raw).hexdigest()[:16] if raw else ""
    text = raw.decode("utf-8", errors="replace")
    paths: list[str] = []
    added_by_path: dict[str, list[str]] = {}
    current_path = ""
    for line in text.splitlines():
        if line.startswith("diff --git "):
            parts = line.split()
            if len(parts) >= 5:
                current_path = parts[3].removeprefix("b/") or parts[2].removeprefix("a/")
                if current_path and current_path not in paths:
                    paths.append(current_path)
        elif line.startswith("+++ "):
            current_path = line[4:].strip().removeprefix("b/")
        elif current_path and line.startswith("+") and not line.startswith("+++"):
            added_by_path.setdefault(current_path, []).append(line[1:])
    return diff_hash, paths, added_by_path


_LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|partial|unsafe|private|protected)\s+)*"
    r"(?:theorem|lemma|def|abbrev|axiom|opaque|structure|inductive|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*)"
)
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)\s*$")
_END_RE = re.compile(r"^\s*end\s+([A-Za-z0-9_.]+)\s*$")


def _module_name(path: str) -> str | None:
    if not path.endswith(".lean"):
        return None
    stripped = path[: -len(".lean")]
    if stripped.startswith("lean/"):
        stripped = stripped[len("lean/"):]
    module = stripped.replace("/", ".")
    return module if module else None


def _decl_names_in_added(added_lines: Iterable[str], module: str) -> list[str]:
    """Full declaration names extracted from patch-added lines, namespace-aware."""
    names: list[str] = []
    namespace_stack: list[str] = []
    for line in added_lines:
        if line.lstrip().startswith("--") or line.lstrip().startswith("/-"):
            continue
        ns_match = _NAMESPACE_RE.match(line)
        if ns_match:
            namespace_stack.append(ns_match.group(1))
            continue
        end_match = _END_RE.match(line)
        if end_match and namespace_stack and end_match.group(1) == namespace_stack[-1]:
            namespace_stack.pop()
            continue
        decl_match = _LEAN_DECL_RE.match(line)
        if decl_match:
            base = decl_match.group(1)
            if namespace_stack:
                names.append(".".join(namespace_stack) + "." + base)
            else:
                names.append(module + "." + base)
    return names


_RANK_ORDER = [
    "Domain",
    "Kingdom",
    "Phylum",
    "Class",
    "Order",
    "Family",
    "Genus",
    "Species",
]


def _classify_rank(message: str, paths: list[str], parents: list[str]) -> str:
    msg = message.lower()
    if any(k in msg for k in ["merge", "merge branch", "merge remote"]):
        return "Kingdom"
    if len(parents) > 1:
        return "Kingdom"
    if any(p.startswith("lean/InfoGeometry/") for p in paths) and len(paths) >= 3:
        return "Phylum"
    module_hits = [p for p in paths if re.match(r"^lean/InfoGeometry/[^/]+/", p)]
    if module_hits:
        return "Class"
    if any(k in msg for k in ["feat", "fix", "refactor", "formalize"]):
        return "Order"
    if any(k in msg for k in ["archetype", "theorem", "lemma"]):
        return "Family"
    if len(paths) == 1:
        return "Genus"
    return "Species"


def _rank_index(rank: str) -> int:
    try:
        return _RANK_ORDER.index(rank)
    except ValueError:
        return len(_RANK_ORDER)


def iter_commits() -> Iterable[dict]:
    log = _run_git([
        "log", "--all", "--topo-order", "--reverse",
        "--format=%H|%P|%an|%ae|%ad|%s",
    ])
    for line in log.splitlines():
        if not line.strip():
            continue
        parts = line.split("|", 5)
        if len(parts) != 6:
            continue
        commit, parents, author, email, date, message = parts
        diff, paths, _added = _diff_record(commit)
        rank = _classify_rank(message, paths, [p for p in parents.split() if p])
        yield {
            "_key": commit,
            "hash": commit,
            "parents": [p for p in parents.split() if p],
            "author": author,
            "email": email,
            "date": date,
            "message": message,
            "diffHash": diff,
            "taxonRank": rank,
            "taxonRankIndex": _rank_index(rank),
            "modulePaths": paths,
            "leanVerified": False,
        }


def import_commit_nodes(db, *, drop_existing: bool = False) -> int:
    if drop_existing and db.has_collection("commit_nodes"):
        db.collection("commit_nodes").truncate()
        db.collection("commit_edges").truncate()
        db.collection("commit_decl_edges").truncate()
        db.collection("taxonomy_ranks").truncate()
    _ensure_collections(db, db.name)
    count = 0
    by_key: dict[str, dict] = {}
    for doc in iter_commits():
        db.collection("commit_nodes").insert(doc, overwrite=True, sync=False)
        by_key[doc["_key"]] = doc
        count += 1
    edges: list[dict] = []
    for doc in by_key.values():
        src = doc["_key"]
        for parent in doc.get("parents", []):
            if parent in by_key:
                edges.append({
                    "_key": f"{src}->{parent}",
                    "_from": f"commit_nodes/{src}",
                    "_to": f"commit_nodes/{parent}",
                    "edgeKind": "parent_of",
                })
    if edges:
        db.collection("commit_edges").import_bulk(edges, overwrite=True, on_duplicate="replace", sync=False)
    taxonomy: dict[tuple[str, str], dict] = {}
    for doc in by_key.values():
        rank = doc.get("taxonRank", "Species")
        name = doc.get("message", "")[:80].replace("\n", " ")
        key = (rank, name)
        if key not in taxonomy:
            taxonomy[key] = {
                "_key": f"{rank}::{re.sub(r'[^A-Za-z0-9_-]+','_',name)[:60]}",
                "rank": rank,
                "rankIndex": _rank_index(rank),
                "name": name,
                "commitCount": 0,
            }
        taxonomy[key]["commitCount"] += 1
    if taxonomy:
        db.collection("taxonomy_ranks").import_bulk(list(taxonomy.values()), overwrite=True, on_duplicate="replace", sync=False)
    print(f"[darwin] imported {count} commit nodes")
    return count


def attach_decl_edges(db, *, max_edges: int = 50000, max_files_per_commit: int = 8,
                      max_lines_per_commit: int = 8000) -> int:
    """Bridge commits to the declaration DNA they introduced.

    Each edge is grounded in a patch-added declaration line of
    ``git diff-tree -p`` and resolves to a live ``decls`` vertex by exact
    fully-qualified name query. No key recipe is guessed; names absent from
    the current census (deleted or moved declarations) are counted as extinct
    DNA and emit no edge. Write target stays inside commit_decl_edges.
    """
    if not db.has_collection("decls") or not db.has_collection("commit_nodes"):
        raise SystemExit("required collections decls/commit_nodes missing")
    edge_coll = "commit_decl_edges"
    if not db.has_collection(edge_coll):
        db.create_collection(edge_coll, edge=True)

    touched: list[tuple[str, list[str]]] = []
    for doc in db.collection("commit_nodes").all():
        lean_paths = [p for p in doc.get("modulePaths", []) if p.endswith(".lean")]
        if lean_paths:
            touched.append((doc["_key"], lean_paths[:max_files_per_commit]))

    needed_modules = sorted(
        {_module_name(p) for _, paths in touched for p in paths} - {None}
    )
    module_cache: dict[str, dict[str, str]] = {}
    for module in needed_modules:
        rows = db.aql.execute(
            "FOR d IN decls FILTER d.module == @m RETURN {key: d._key, name: d.name}",
            bind_vars={"m": module},
        )
        module_cache[module] = {r["name"]: r["key"] for r in rows}

    batch: list[dict] = []
    seen: set[str] = set()
    stats = {"extinct": 0}
    total = 0

    def flush() -> None:
        nonlocal batch, total
        if batch:
            db.collection(edge_coll).import_bulk(
                batch, overwrite=True, on_duplicate="replace", sync=False
            )
            total += len(batch)
            batch = []

    for commit, lean_paths in touched:
        if total >= max_edges:
            break
        _, _, added_by_path = _diff_record(commit)
        for path in lean_paths:
            if total >= max_edges:
                break
            module = _module_name(path)
            if module is None:
                continue
            resolve = module_cache.get(module)
            if resolve is None:
                continue
            added_lines = added_by_path.get(path)
            if not added_lines:
                continue
            for name in _decl_names_in_added(added_lines[:max_lines_per_commit], module):
                key = resolve.get(name)
                if key is None:
                    stats["extinct"] += 1
                    continue
                edge_key = f"{commit}::{key}"
                if edge_key in seen:
                    continue
                seen.add(edge_key)
                batch.append({
                    "_key": edge_key,
                    "_from": f"commit_nodes/{commit}",
                    "_to": f"decls/{key}",
                    "edgeKind": "touches",
                    "declName": name,
                    "modulePath": path,
                })
                if len(batch) >= 5000:
                    flush()
        if batch and total + len(batch) >= max_edges:
            break
    flush()
    print(
        f"[darwin] attached {total} commit->decls DNA edges "
        f"(extinct resolutions: {stats['extinct']})"
    )
    return total


def query_darwin(db) -> None:
    for label, query in [
        ("taxonomy counts", """
        FOR r IN taxonomy_ranks
          SORT r.rankIndex
          RETURN {rank: r.rank, name: r.name, commits: r.commitCount}
        """),
        ("paths from alpha6-style apex", """
        FOR c IN commit_nodes
          FILTER 'alpha6' IN c.message
          RETURN {hash: c._key, rank: c.taxonRank, message: c.message}
        """),
        ("commit-decl bridge sample", """
        FOR e IN commit_decl_edges
          LIMIT 20
          RETURN {from: e._from, to: e._to}
        """),
    ]:
        print(f"=== {label} ===")
        try:
            rows = list(db.aql.execute(query))
            for row in rows:
                print(row)
        except Exception as e:
            print(f"query failed: {e}")


def main() -> int:
    import argparse
    parser = argparse.ArgumentParser(description="Darwin commit-evolution taxonomy importer")
    parser.add_argument("--drop-existing", action="store_true", help="drop commit_* collections before import")
    parser.add_argument("--database", help="Override the resolved Darwin commit database")
    parser.add_argument("--no-query", action="store_true", help="skip post-import queries")
    parser.add_argument("--attach-decl-edges", action="store_true", help="attach commit->path edges")
    parser.add_argument("--max-edges", type=int, default=50000)
    args = parser.parse_args()
    load_repo_arango_env(REPO_ROOT)
    config = normalized_darwin_arango_env()
    client = ArangoClient(hosts=config["endpoint"])
    db = client.db(
        args.database or config["database"],
        username=config["user"],
        password=config["password"],
    )
    import_commit_nodes(db, drop_existing=args.drop_existing)
    if args.attach_decl_edges:
        attach_decl_edges(db, max_edges=args.max_edges)
    if not args.no_query:
        query_darwin(db)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
