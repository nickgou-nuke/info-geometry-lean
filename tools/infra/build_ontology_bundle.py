#!/usr/bin/env python3
"""Build a source-bound, immutable Auto-Ontology bundle offline.

The input is a file-based declaration export from ``refresh_decl_graph.py``.
Output separates declaration terms, module memberships, and compiler dependency
relations. The command never connects to ArangoDB or PostgreSQL and refuses to
overwrite a bundle. SQLite staging keeps memory bounded for repository-scale
JSONL exports.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import tempfile
from typing import Any, Iterator

from build import compute_lean_source_hash, compute_olean_content_hash
from decl_projection import DEFAULT_DEPLOYMENT_UUID, Source, source_digest
from igf.graph.decl_schema import decl_key, edge_key

BUNDLE_SCHEMA = "info_geometry.auto_ontology_bundle.v1"
INDEX_SCHEMA_VERSION = 3


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _read_jsonl(path: Path) -> Iterator[tuple[int, dict[str, Any]]]:
    with path.open(encoding="utf-8") as stream:
        for line_no, raw in enumerate(stream, 1):
            text = raw.strip()
            if not text:
                continue
            try:
                value = json.loads(text)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_no}: invalid JSON: {exc.msg}") from exc
            if not isinstance(value, dict):
                raise ValueError(f"{path}:{line_no}: expected a JSON object")
            yield line_no, value


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _write_jsonl(path: Path, rows: Iterator[dict[str, Any]]) -> str:
    digest = hashlib.sha256()
    with path.open("wb") as stream:
        for row in rows:
            data = (_canonical_json(row) + "\n").encode("utf-8")
            stream.write(data)
            digest.update(data)
    return digest.hexdigest()


def _publish_new_directory(temporary: Path, output_dir: Path) -> None:
    """Publish the completed bundle atomically; never replace existing work."""
    output_dir = output_dir.resolve()
    if output_dir.exists():
        raise FileExistsError(f"refusing to replace existing bundle: {output_dir}")
    if temporary.stat().st_dev != output_dir.parent.stat().st_dev:
        raise ValueError("temporary bundle must share the destination filesystem")
    if output_dir.exists():
        raise FileExistsError(f"bundle appeared while writing: {output_dir}")
    os.rename(temporary, output_dir)


def _insert_declarations(connection: sqlite3.Connection, path: Path) -> int:
    count = 0
    for line_no, row in _read_jsonl(path):
        name = row.get("name")
        if not isinstance(name, str) or not name.strip():
            raise ValueError(f"{path}:{line_no}: declaration name is empty or missing")
        key = row.get("_key", row.get("key", decl_key(name)))
        if key != decl_key(name):
            raise ValueError(f"{path}:{line_no}: declaration key mismatch for {name!r}")
        module = row.get("module") or "Unknown"
        doc = row.get("doc") or ""
        kind = row.get("kind") or ""
        rel_file = row.get("relFile") or row.get("file") or ""
        line = row.get("line") or 0
        if not all(isinstance(value, str) for value in (module, doc, kind, rel_file)):
            raise ValueError(f"{path}:{line_no}: module/doc/kind/source path must be strings")
        if not isinstance(line, int) or isinstance(line, bool) or line < 0:
            raise ValueError(f"{path}:{line_no}: source line must be a nonnegative integer")
        normalized = {**row, "_key": key, "name": name, "module": module}
        try:
            connection.execute(
                "INSERT INTO declarations(key,name,module,doc,kind,rel_file,line,payload) "
                "VALUES(?,?,?,?,?,?,?,?)",
                (key, name, module, doc, kind, rel_file, line, _canonical_json(normalized)),
            )
        except sqlite3.IntegrityError as exc:
            raise ValueError(f"{path}:{line_no}: duplicate declaration name/key {name!r}") from exc
        count += 1
    if count == 0:
        raise ValueError("refusing to build an empty ontology bundle")
    connection.commit()
    return count


def _insert_edges(connection: sqlite3.Connection, path: Path) -> int:
    count = 0
    for line_no, row in _read_jsonl(path):
        src, dst, kind = row.get("src"), row.get("dst"), row.get("kind")
        if (not isinstance(src, str) or not src or not isinstance(dst, str) or not dst
                or kind not in ("type", "value")):
            raise ValueError(f"{path}:{line_no}: invalid compiler dependency edge")
        key = row.get("_key", row.get("key", edge_key(src, kind, dst)))
        if key != edge_key(src, kind, dst):
            raise ValueError(f"{path}:{line_no}: edge key mismatch")
        normalized = {**row, "_key": key, "src": src, "dst": dst, "kind": kind}
        try:
            connection.execute(
                "INSERT INTO edges(key,src,dst,kind,payload) VALUES(?,?,?,?,?)",
                (key, src, dst, kind, _canonical_json(normalized)),
            )
        except sqlite3.IntegrityError as exc:
            raise ValueError(f"{path}:{line_no}: duplicate dependency edge {key!r}") from exc
        count += 1
    connection.commit()
    dangling = connection.execute(
        "SELECT e.src,e.dst FROM edges e "
        "LEFT JOIN declarations s ON s.name=e.src "
        "LEFT JOIN declarations d ON d.name=e.dst "
        "WHERE s.key IS NULL OR d.key IS NULL LIMIT 1"
    ).fetchone()
    if dangling:
        raise ValueError(f"dangling compiler dependency edge: {dangling[0]!r} -> {dangling[1]!r}")
    return count


def _digest_declarations(connection: sqlite3.Connection):
    cursor = connection.execute(
        "SELECT key,name,module,payload FROM declarations ORDER BY key COLLATE BINARY"
    )
    for key, name, module, payload in cursor:
        yield key, name, module, json.loads(payload)


def _digest_edges(connection: sqlite3.Connection):
    cursor = connection.execute(
        "SELECT e.key,s.key,d.key,e.kind,e.payload FROM edges e "
        "JOIN declarations s ON s.name=e.src JOIN declarations d ON d.name=e.dst "
        "ORDER BY e.key COLLATE BINARY"
    )
    yield from cursor


def _term_rows(connection: sqlite3.Connection):
    cursor = connection.execute(
        "SELECT key,name,module,doc,kind,rel_file,line FROM declarations ORDER BY key COLLATE BINARY"
    )
    for key, name, module, doc, kind, rel_file, line in cursor:
        description = doc + (f"\n\nSource: {rel_file}:{line}" if rel_file else "")
        yield {
            "imported_id": key,
            "name": name,
            "description": description,
            "source": "semantic",
            "synonyms": [kind] if kind else [],
        }


def _membership_rows(connection: sqlite3.Connection):
    cursor = connection.execute(
        "SELECT module,key FROM declarations ORDER BY key COLLATE BINARY"
    )
    for module, key in cursor:
        yield {"module": module, "term_imported_id": key}


def _relationship_rows(connection: sqlite3.Connection):
    cursor = connection.execute(
        "SELECT s.key,d.key,e.kind FROM edges e "
        "JOIN declarations s ON s.name=e.src JOIN declarations d ON d.name=e.dst "
        "ORDER BY e.key COLLATE BINARY"
    )
    for src, dst, kind in cursor:
        yield {"src_imported_id": src, "dst_imported_id": dst, "kind": kind}


def build_bundle(index_dir: Path, output_dir: Path, *, repo_root: Path) -> dict[str, Any]:
    """Validate a current declaration export and publish a new offline bundle."""
    index_dir = index_dir.resolve()
    meta_path, decls_path, edges_path = (
        index_dir / "meta.json", index_dir / "decls.jsonl", index_dir / "edges.jsonl"
    )
    for path in (meta_path, decls_path, edges_path):
        if not path.is_file():
            raise FileNotFoundError(f"required declaration-export file is missing: {path}")
    meta_bytes = meta_path.read_bytes()
    meta = json.loads(meta_bytes)
    if not isinstance(meta, dict) or meta.get("schemaVersion") != INDEX_SCHEMA_VERSION:
        raise ValueError(f"unsupported declaration export schema in {meta_path}")
    if not isinstance(meta.get("importRoot"), str) or not meta["importRoot"]:
        raise ValueError("declaration export has no importRoot")
    if not isinstance(meta.get("nsFilter"), str) or not meta["nsFilter"]:
        raise ValueError("declaration export has no namespace filter")
    hashes = meta.get("outputHashes")
    if meta.get("outputHashAlgorithm") != "sha256" or not isinstance(hashes, dict):
        raise ValueError("declaration export is not bound to SHA-256 output hashes")
    input_hashes = {"decls.jsonl": _sha256(decls_path), "edges.jsonl": _sha256(edges_path)}
    if any(hashes.get(name) != digest for name, digest in input_hashes.items()):
        raise ValueError("declaration export output hash mismatch")

    source_hash = compute_lean_source_hash(repo_root)
    olean_hash = compute_olean_content_hash(repo_root)
    if meta.get("sourceHash") != source_hash:
        raise ValueError("declaration export sourceHash is stale for this checkout")
    if meta.get("oleanHash") != olean_hash:
        raise ValueError("declaration export oleanHash is stale for this checkout")

    output_dir = output_dir.resolve()
    if output_dir.exists():
        raise FileExistsError(f"refusing to replace existing bundle: {output_dir}")
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix=f".{output_dir.name}.stage-", dir=output_dir.parent
    ) as stage_name:
        staging_root = Path(stage_name)
        stage = staging_root / "bundle"
        stage.mkdir()
        database = staging_root / "stage.sqlite3"
        with sqlite3.connect(database) as connection:
            connection.execute("PRAGMA journal_mode=OFF")
            connection.execute("PRAGMA synchronous=OFF")
            connection.execute("CREATE TABLE declarations("
                               "key TEXT PRIMARY KEY, name TEXT NOT NULL UNIQUE, module TEXT NOT NULL, "
                               "doc TEXT NOT NULL, kind TEXT NOT NULL, rel_file TEXT NOT NULL, "
                               "line INTEGER NOT NULL, payload TEXT NOT NULL)")
            connection.execute("CREATE TABLE edges("
                               "key TEXT PRIMARY KEY, src TEXT NOT NULL, dst TEXT NOT NULL, "
                               "kind TEXT NOT NULL, payload TEXT NOT NULL)")
            declaration_count = _insert_declarations(connection, decls_path)
            edge_count = _insert_edges(connection, edges_path)

            source = Source(DEFAULT_DEPLOYMENT_UUID, "infogeometry")
            export_receipt = {
                "schema": "info_geometry.decl_graph_generation.v1",
                "status": "complete",
                "_key": f"offline_{source_hash[:20]}",
                "importRoot": meta["importRoot"],
                "namespace": meta["nsFilter"],
                "buildFingerprint": olean_hash,
                "declarationCount": declaration_count,
                "validEdgeCount": edge_count,
            }
            digest = source_digest(
                source, export_receipt,
                _digest_declarations(connection), _digest_edges(connection),
            )
            term_hash = _write_jsonl(stage / "terms.jsonl", _term_rows(connection))
            membership_hash = _write_jsonl(
                stage / "module_memberships.jsonl", _membership_rows(connection)
            )
            relationship_hash = _write_jsonl(
                stage / "relationships.jsonl", _relationship_rows(connection)
            )
            module_count = connection.execute(
                "SELECT COUNT(DISTINCT module) FROM declarations"
            ).fetchone()[0]

        # Recheck all source/export sentinels after extraction to reject a mixed snapshot.
        if meta_path.read_bytes() != meta_bytes:
            raise ValueError("declaration export metadata changed while building bundle")
        if {"decls.jsonl": _sha256(decls_path), "edges.jsonl": _sha256(edges_path)} != input_hashes:
            raise ValueError("declaration export files changed while building bundle")
        if compute_lean_source_hash(repo_root) != source_hash:
            raise ValueError("Lean sources changed while building bundle")
        if compute_olean_content_hash(repo_root) != olean_hash:
            raise ValueError("Lean build artifacts changed while building bundle")

        receipt = {
            "schema": BUNDLE_SCHEMA,
            "status": "source_bound_offline_bundle",
            "source": {
                "deployment_uuid": str(source.deployment_uuid),
                "arango_database": source.arango_database,
                "sourceHash": source_hash,
                "oleanHash": olean_hash,
                "importRoot": meta["importRoot"],
                "namespace": meta["nsFilter"],
                "index_schema_version": meta["schemaVersion"],
                "index_meta_sha256": hashlib.sha256(meta_bytes).hexdigest(),
                "input_file_sha256": input_hashes,
            },
            "counts": {
                "terms": declaration_count,
                "module_memberships": declaration_count,
                "relationships": edge_count,
                "modules": module_count,
            },
            "source_digest": digest,
            "files": {
                "terms.jsonl": term_hash,
                "module_memberships.jsonl": membership_hash,
                "relationships.jsonl": relationship_hash,
            },
        }
        (stage / "bundle_receipt.json").write_text(
            json.dumps(receipt, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
            encoding="utf-8",
        )
        database.unlink()
        _publish_new_directory(stage, output_dir)
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--index-dir", type=Path, required=True,
                        help="source-bound export directory containing meta.json, decls.jsonl, edges.jsonl")
    parser.add_argument("--out-dir", type=Path, required=True,
                        help="new bundle directory; existing output is never overwritten")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    receipt = build_bundle(args.index_dir, args.out_dir, repo_root=root)
    print(json.dumps({"out_dir": str(args.out_dir), **receipt}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
