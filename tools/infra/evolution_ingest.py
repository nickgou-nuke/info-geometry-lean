#!/usr/bin/env python3
"""Batch-ingest streamed commit JSONL into a dedicated Arango evolution graph.

The input file is read twice in bounded batches: first to create commit
vertices, then to create parent edges after all vertices exist. Credentials use
the repository Arango environment loader; no secret is embedded in source.
Writes are append/upsert by default. ``--replace`` explicitly truncates only
the six ``evo_*`` collections owned by this importer.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import sys
from itertools import islice
from pathlib import Path
from typing import Iterator, TextIO

REPO_ROOT = Path(__file__).resolve().parents[2]
for import_root in (REPO_ROOT, REPO_ROOT / "src"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from tools.infra.arango_env import (  # noqa: E402
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)


def _records(stream: TextIO) -> Iterator[dict]:
    for line_number, line in enumerate(stream, 1):
        if not line.strip():
            continue
        try:
            yield json.loads(line)
        except json.JSONDecodeError as exc:
            raise ValueError(f"invalid JSONL at line {line_number}: {exc}") from exc


def _batches(records: Iterator[dict], size: int) -> Iterator[list[dict]]:
    while batch := list(islice(records, size)):
        yield batch


def _open_records(path: Path) -> TextIO:
    return path.open("r", encoding="utf-8")


def _ensure(db, name: str, *, edge: bool = False, replace: bool = False) -> None:
    if db.has_collection(name):
        if replace:
            db.collection(name).truncate()
        return
    db.create_collection(name, edge=edge)


def _import(db, collection: str, batch: list[dict]) -> None:
    if batch:
        result = db.collection(collection).import_bulk(
            batch, overwrite=False, on_duplicate="replace", sync=False
        )
        if int(result.get("errors", 0) or 0) > 0:
            raise RuntimeError(f"Arango import errors in {collection}: {result}")


def _path_key(row: dict) -> str:
    encoded = row.get("path_base64")
    raw = (base64.b64decode(encoded, validate=True) if encoded is not None
           else row.get("path", "").encode("utf-8"))
    return hashlib.sha256(raw).hexdigest()


def _ingest_file_stream(db, path: Path, *, collection: str, edge: bool,
                        batch_size: int, transform, replace: bool = False) -> int:
    _ensure(db, collection, edge=edge)
    batch: list[dict] = []
    total = 0
    with _open_records(path) as stream:
        for row in _records(stream):
            batch.append(transform(row))
            if len(batch) >= batch_size:
                _import(db, collection, batch)
                total += len(batch)
                batch = []
    if batch:
        _import(db, collection, batch)
        total += len(batch)
    return total


def ingest(db, commit_path: Path, label_path: Path | None = None,
           paths_path: Path | None = None, numstat_path: Path | None = None,
           *, batch_size: int = 1000, replace: bool = False) -> dict[str, int]:
    """Write commit/label vertices, then lineage edges, using O(batch) RAM."""
    names = ("evo_commits", "evo_labels", "evo_parent_edges",
             "evo_files", "evo_commit_files", "evo_file_numstats")
    _ensure(db, names[0], replace=replace)
    _ensure(db, names[1], replace=replace)
    _ensure(db, names[2], edge=True, replace=replace)
    _ensure(db, names[3], replace=replace)
    _ensure(db, names[4], edge=True, replace=replace)
    _ensure(db, names[5], replace=replace)
    counts = {"commits": 0, "labels": 0, "parent_edges": 0,
              "files": 0, "commit_files": 0, "file_numstats": 0}

    commit_stream = _open_records(commit_path)
    label_stream = _open_records(label_path) if label_path else None
    try:
        commit_records = _records(commit_stream)
        label_records = _records(label_stream) if label_stream else None
        for commits in _batches(commit_records, batch_size):
            if any(row.get("type") != "commit" for row in commits):
                raise ValueError("commit input contains a non-commit record")
            label_batch: list[dict] = []
            if label_records is not None:
                for commit in commits:
                    try:
                        label = next(label_records)
                    except StopIteration as exc:
                        raise ValueError("label JSONL ended before commit JSONL") from exc
                    if label.get("sha") != commit.get("sha"):
                        raise ValueError("label/commit order or SHA mismatch")
                    label_batch.append({"_key": label["sha"], **label})
            _import(db, names[0], [{"_key": row["sha"], **row} for row in commits])
            if label_batch:
                _import(db, names[1], label_batch)
            counts["commits"] += len(commits)
            counts["labels"] += len(label_batch)
        if label_records is not None and next(label_records, None) is not None:
            raise ValueError("label JSONL contains rows after the commit stream")
    finally:
        commit_stream.close()
        if label_stream:
            label_stream.close()

    # Second disk pass establishes all parent->child edges after vertex import.
    with _open_records(commit_path) as stream:
        edge_batch: list[dict] = []
        for commit in _records(stream):
            child = commit["sha"]
            for parent_slot, parent in enumerate(commit.get("parents", [])):
                edge_batch.append({
                    "_key": f"{parent}__{child}",
                    "_from": f"evo_commits/{parent}",
                    "_to": f"evo_commits/{child}",
                    "edgeKind": "parent_of",
                    "parent_slot": parent_slot,
                })
                if len(edge_batch) >= batch_size:
                    _import(db, names[2], edge_batch)
                    counts["parent_edges"] += len(edge_batch)
                    edge_batch = []
        if edge_batch:
            _import(db, names[2], edge_batch)
            counts["parent_edges"] += len(edge_batch)
    if paths_path:
        def file_doc(row: dict) -> dict:
            key = _path_key(row)
            doc = {"_key": key, "path": row.get("path"),
                   "path_base64": row.get("path_base64")}
            return doc

        counts["files"] = _ingest_file_stream(
            db, paths_path, collection="evo_files", edge=False,
            batch_size=batch_size, transform=file_doc,
        )

        def commit_file_edge(row: dict) -> dict:
            pkey = _path_key(row)
            edge_key = hashlib.sha256(
                f"{row['sha']}:{row.get('change_type', '')}:{pkey}".encode()
            ).hexdigest()
            return {"_key": edge_key, "_from": f"evo_commits/{row['sha']}",
                    "_to": f"evo_files/{pkey}", "edgeKind": "changes_file",
                    "change_type": row.get("change_type"),
                    "similarity": row.get("similarity"),
                    "old_path": row.get("old_path"),
                    "old_path_base64": row.get("old_path_base64")}

        counts["commit_files"] = _ingest_file_stream(
            db, paths_path, collection="evo_commit_files", edge=True,
            batch_size=batch_size, transform=commit_file_edge,
        )
    if numstat_path:
        def numstat_doc(row: dict) -> dict:
            pkey = _path_key(row)
            return {"_key": hashlib.sha256(f"{row['sha']}:{pkey}".encode()).hexdigest(),
                    "sha": row["sha"], "file_key": pkey,
                    "additions": row.get("additions"), "deletions": row.get("deletions"),
                    "change_type": row.get("change_type")}

        counts["file_numstats"] = _ingest_file_stream(
            db, numstat_path, collection="evo_file_numstats", edge=False,
            batch_size=batch_size, transform=numstat_doc,
        )
    return counts


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("commits", type=Path)
    parser.add_argument("--labels", type=Path)
    parser.add_argument("--paths", type=Path, help="commit-file JSONL from the extractor")
    parser.add_argument("--numstat", type=Path, help="file-numstat JSONL from the extractor")
    parser.add_argument("--batch-size", type=int, default=1000)
    parser.add_argument("--database", default=None)
    parser.add_argument("--replace", action="store_true",
                        help="truncate only the six evo_* collections")
    args = parser.parse_args()
    if args.batch_size < 1:
        parser.error("--batch-size must be positive")
    load_repo_arango_env(REPO_ROOT)
    try:
        from arango import ArangoClient
    except ImportError as exc:
        raise SystemExit(f"python-arango is required: {exc}") from exc
    endpoint = os.environ.get("DARWIN_ARANGO_ENDPOINT", arango_endpoint())
    database = args.database or os.environ.get("DARWIN_ARANGO_DATABASE", arango_database())
    client = ArangoClient(hosts=endpoint)
    db = client.db(database, username=arango_username(), password=arango_password())
    counts = ingest(db, args.commits, args.labels, args.paths, args.numstat,
                    batch_size=args.batch_size, replace=args.replace)
    print(json.dumps({"database": database, **counts}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
