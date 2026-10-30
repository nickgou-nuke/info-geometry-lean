#!/usr/bin/env python3
"""Darwin commit history and weak change facets for ArangoDB.

Builds a dual-view graph:
- commit_nodes / commit_parent_edges_v2: exact Git history and ordered parent→child edges
- changeLabels: non-hierarchical weak classifications of commit changes
- commit_decl_edges: causal links from commits to decls DNA nodes

Boundaries:
- read-only by default; write only to commit_* collections
- never truncates decls/edges/raw_infotree_* collections
- uses repo arango env loader; no invented credential handling
"""
from __future__ import annotations

import hashlib
import json
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
PARENT_EDGE_COLLECTION = "commit_parent_edges_v2"


def _run_git_bytes(args: list[str]) -> bytes:
    return subprocess.check_output(
        ["git", *args], cwd=REPO_ROOT, stderr=subprocess.DEVNULL
    )


def _ensure_collections(db, database: str) -> None:
    for name, is_edge in (
        ("commit_nodes", False),
        (PARENT_EDGE_COLLECTION, True),
        ("commit_decl_edges", True),
    ):
        if db.has_collection(name):
            continue
        db.create_collection(name, edge=is_edge)
        print(f"[darwin] created collection {name}")


def _diff_record(commit: str) -> tuple[str, list[str], dict[str, list[str]]]:
    """Optional patch record used only by declaration-line attachment.

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


def _changed_paths(commit: str) -> tuple[str, list[str]]:
    """Read path metadata only; do not materialize historical patch contents."""
    raw = _run_git_bytes([
        "diff-tree", "--no-commit-id", "--root", "-r", "-m", "--no-renames",
        "--name-only", "-z", commit,
    ])
    paths = [part.decode("utf-8", errors="replace")
             for part in raw.split(b"\0") if part]
    return hashlib.sha256(raw).hexdigest(), list(dict.fromkeys(paths))


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


def _change_labels(message: str, paths: list[str]) -> list[dict]:
    """Reuse the repo's multi-label weak rules; no rank or ancestry inference."""
    from tools.infra.evolution_taxonomy import classify

    return classify(message, "", paths)


def iter_commits() -> Iterable[dict]:
    process = subprocess.Popen([
        "git",
        "log", "--all", "--topo-order", "--reverse",
        "--format=%H%x1f%P%x1f%an%x1f%ae%x1f%aI%x1f%s",
    ], cwd=REPO_ROOT, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
        text=True, encoding="utf-8", errors="replace")
    assert process.stdout is not None
    for line in process.stdout:
        line = line.rstrip("\n")
        if not line:
            continue
        parts = line.split("\x1f", 5)
        if len(parts) != 6:
            continue
        commit, parents, author, email, date, message = parts
        path_change_hash, paths = _changed_paths(commit)
        yield {
            "_key": commit,
            "hash": commit,
            "parents": [p for p in parents.split() if p],
            "author": author,
            "email": email,
            "date": date,
            "message": message,
            "pathChangeHash": path_change_hash,
            "changeLabels": _change_labels(message, paths),
            "changeLabelMethod": "weak-rule-v3",
            "modulePaths": paths,
        }
    return_code = process.wait()
    if return_code:
        raise subprocess.CalledProcessError(return_code, process.args)


def iter_parent_edges(commits: Iterable[dict], known_commit_keys: set[str]) -> Iterable[dict]:
    """Yield ordered parent-to-child Git edges among exported commits."""
    for child_doc in commits:
        child = child_doc["_key"]
        for parent_slot, parent in enumerate(child_doc.get("parents", [])):
            if parent not in known_commit_keys:
                continue
            yield {
                "_key": f"{parent}__{child}__p{parent_slot}",
                "_from": f"commit_nodes/{parent}",
                "_to": f"commit_nodes/{child}",
                "edgeKind": "parent_of",
                "parent_slot": parent_slot,
            }


def iter_git_parent_edges(known_commit_keys: set[str]) -> Iterable[dict]:
    """Stream parent edges from Git metadata without rebuilding patch records."""
    process = subprocess.Popen(
        ["git", "log", "--all", "--topo-order", "--reverse",
         "--format=%H %P"],
        cwd=REPO_ROOT, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
        text=True, encoding="ascii", errors="replace",
    )
    assert process.stdout is not None
    for line in process.stdout:
        fields = line.split()
        if not fields:
            continue
        child, *parents = fields
        if child not in known_commit_keys:
            continue
        for parent_slot, parent in enumerate(parents):
            if parent not in known_commit_keys:
                continue
            yield {
                "_key": f"{parent}__{child}__p{parent_slot}",
                "_from": f"commit_nodes/{parent}",
                "_to": f"commit_nodes/{child}",
                "edgeKind": "parent_of",
                "parent_slot": parent_slot,
            }
    return_code = process.wait()
    if return_code:
        raise subprocess.CalledProcessError(return_code, process.args)


def import_commit_nodes(db, *, drop_existing: bool = False) -> int:
    if drop_existing and db.has_collection("commit_nodes"):
        db.collection("commit_nodes").truncate()
        if db.has_collection(PARENT_EDGE_COLLECTION):
            db.collection(PARENT_EDGE_COLLECTION).truncate()
        db.collection("commit_decl_edges").truncate()
        # taxonomy_ranks is a legacy heuristic collection. Leave it untouched;
        # this importer no longer writes or truncates biological-rank records.
    _ensure_collections(db, db.name)
    count = 0
    known_commit_keys: set[str] = set()
    for doc in iter_commits():
        db.collection("commit_nodes").insert(doc, overwrite=True, sync=False)
        known_commit_keys.add(doc["_key"])
        count += 1
    edge_batch: list[dict] = []
    for edge in iter_git_parent_edges(known_commit_keys):
        edge_batch.append(edge)
        if len(edge_batch) >= 5000:
            db.collection(PARENT_EDGE_COLLECTION).import_bulk(
                edge_batch, overwrite=True, on_duplicate="replace", sync=False
            )
            edge_batch = []
    if edge_batch:
        db.collection(PARENT_EDGE_COLLECTION).import_bulk(
            edge_batch, overwrite=True, on_duplicate="replace", sync=False
        )
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
        ("weak change-category counts", """
        FOR c IN commit_nodes
          FOR label IN c.changeLabels
          COLLECT category = label.category, categoryId = label.categoryId
          WITH COUNT INTO commits
          SORT category
          RETURN {category, categoryId, commits}
        """),
        ("paths from alpha6-style apex", """
        FOR c IN commit_nodes
          FILTER 'alpha6' IN c.message
          RETURN {hash: c._key, changeLabels: c.changeLabels, message: c.message}
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
