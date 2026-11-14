#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
_SRC = Path(__file__).resolve().parents[2] / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from tools.build_lock import BuildLock, acquire_build_lock
from tools.infra.artifacts import (
    normalize_repo_output,
    should_skip_decl_refresh,
    load_decl_index_meta,
    stamp_decl_index_meta,
    find_missing_decl_source_files,
)
from tools.infra.build import (
    build_indexer_command,
    compute_olean_content_hash,
    compute_lean_source_hash,
    run_locked_prebuild,
)
from tools.infra.timings import write_indexer_timing_sidecar
from tools.pathing import (
    default_decl_graph_file,
    default_decl_index_dir,
    default_decl_structure_file,
    repo_root,
)
from tools.infra.arango_env import (
    arango_endpoint,
    arango_username,
    arango_password,
    load_repo_arango_env,
)
from igf.graph.decl_schema import EDGE_KINDS, decl_key, edge_key
from tools.infra.decl_graph_generation import (
    validate_generation_counts,
    validate_generation_id,
    validate_generation_metadata,
)


def _normalize_generation_record(doc: object, decl_collection: str) -> tuple[str, dict]:
    """Validate one immutable-generation stream row and attach canonical identity."""
    if not isinstance(doc, dict):
        raise ValueError("stream record must be a JSON object")
    edge_fields = {"src", "dst", "_from", "_to"}
    if edge_fields.intersection(doc):
        if set(("src", "dst", "kind")) - doc.keys():
            raise ValueError("dependency edge requires src, dst, and kind")
        src, dst, kind = doc["src"], doc["dst"], doc["kind"]
        if (not isinstance(src, str) or not src or not isinstance(dst, str) or not dst
                or kind not in EDGE_KINDS):
            raise ValueError("dependency edge has an invalid endpoint or kind")
        expected_from = f"{decl_collection}/{decl_key(src)}"
        expected_to = f"{decl_collection}/{decl_key(dst)}"
        expected_key = edge_key(src, kind, dst)
        if (doc.get("_from", expected_from) != expected_from
                or doc.get("_to", expected_to) != expected_to
                or doc.get("_key", expected_key) != expected_key):
            raise ValueError("dependency edge identity is not canonical for this generation")
        normalized = dict(doc, _key=expected_key, _from=expected_from, _to=expected_to)
        return "edge", normalized

    name = doc.get("name")
    if not isinstance(name, str) or not name:
        raise ValueError("declaration requires a non-empty name")
    expected_key = decl_key(name)
    if any(doc[field] != expected_key for field in ("key", "_key") if field in doc):
        raise ValueError("declaration key is not canonical for its name")
    normalized = dict(doc, _key=expected_key)
    return "decl", normalized


def stream_to_arango(
    root: Path, import_root: str, namespace: str, database: str, run_mode: str,
    generation_id: str | None = None, build_fingerprint: str | None = None, *,
    expected_source_hash: str | None = None,
    expected_olean_hash: str | None = None,
) -> int:
    """Stream JSONL from dagIndexer directly to ArangoDB.

    Immutable generations fail closed: the stream must be valid, unique, complete,
    and tied to the expected source/olean snapshot before its receipt is published.
    """
    if generation_id is not None:
        try:
            validate_generation_id(generation_id)
            validate_generation_metadata(build_fingerprint, import_root, namespace)
        except ValueError as exc:
            print(f"[refresh-decl-graph] invalid generation preflight: {exc}", file=sys.stderr)
            return 1
    load_repo_arango_env(root)

    # Build the streaming command
    if run_mode == "exe":
        cmd = [
            "lake", "env",
            str(root / ".lake" / "build" / "bin" / "dagIndexer"),
            import_root, namespace, "--stream"
        ]
    else:
        cmd = ["lake", "env", "lean", "--run", "lean/DAG/Indexer.lean", import_root, namespace, "--stream"]

    print(f"[refresh-decl-graph] streaming: {' '.join(cmd)}", flush=True)

    # Do not contact ArangoDB if the selected exporter artifact is absent.
    if run_mode == "exe" and not (root / ".lake" / "build" / "bin" / "dagIndexer").is_file():
        print("[refresh-decl-graph] missing built dagIndexer executable", file=sys.stderr)
        return 1

    # Connect to ArangoDB
    try:
        from arango import ArangoClient
    except ImportError:
        print("Error: python-arango not installed. Install with: pip install python-arango", file=sys.stderr)
        return 1

    # Full `InfoGeometry.All` streams currently emit millions of dependency
    # edges.  Final endpoint validation is intentionally global and can exceed
    # the python-arango default 60-second HTTP timeout.
    client = ArangoClient(hosts=arango_endpoint(), request_timeout=3600)
    db = client.db(database, username=arango_username(), password=arango_password())

    # Legacy mode preserves its historical replace-in-place behavior. The
    # generation mode writes to fresh collections and never truncates prior data.
    suffix = f"_g_{generation_id}" if generation_id else ""
    decl_collection = "decls" + suffix
    edge_collection = "edges" + suffix
    collections = {decl_collection: False, edge_collection: True}
    for coll_name, is_edge in collections.items():
        if db.has_collection(coll_name):
            if generation_id:
                print(f"[refresh-decl-graph] immutable generation already exists: {coll_name}", file=sys.stderr)
                return 2
            db.collection(coll_name).truncate()
            print(f"[refresh-decl-graph] Truncated collection: {coll_name}")
        else:
            db.create_collection(coll_name, edge=is_edge)
            print(f"[refresh-decl-graph] Created collection: {coll_name}")

    # Stream JSONL to ArangoDB.  Generation-mode validation errors are recorded
    # while the pipe is drained, so the child cannot block on a full stdout pipe.
    proc = subprocess.Popen(cmd, cwd=root, stdout=subprocess.PIPE, stderr=None, text=True)

    decl_count = 0
    edge_count = 0
    batch_size = 5000
    decl_batch: list[dict] = []
    edge_batch: list[dict] = []
    stream_error: str | None = None

    def import_batch(collection_name: str, batch: list[dict]) -> None:
        result = db[collection_name].import_bulk(
            batch, overwrite=False, on_duplicate="replace"
        )
        if isinstance(result, dict) and int(result.get("errors", 0) or 0) > 0:
            raise RuntimeError(f"Arango import errors in {collection_name}: {result}")

    try:
        for line in proc.stdout:
            line = line.strip()
            if not line:
                continue
            try:
                doc = json.loads(line)
            except json.JSONDecodeError as exc:
                if generation_id is not None and stream_error is None:
                    stream_error = f"invalid JSONL record: {exc}"
                continue

            if generation_id is not None:
                try:
                    row_kind, doc = _normalize_generation_record(doc, decl_collection)
                except ValueError as exc:
                    if stream_error is None:
                        stream_error = str(exc)
                    continue
                batch = edge_batch if row_kind == "edge" else decl_batch
                batch.append(doc)
                if len(batch) >= batch_size:
                    collection = edge_collection if row_kind == "edge" else decl_collection
                    import_batch(collection, batch)
                    if row_kind == "edge":
                        edge_count += len(batch)
                        edge_batch = []
                    else:
                        decl_count += len(batch)
                        decl_batch = []
                continue

            # Legacy additive mode preserves its permissive input behavior.
            if (("_from" in doc and "_to" in doc)
                    or ("src" in doc and "dst" in doc)):
                if "src" in doc and "dst" in doc:
                    doc["kind"] = doc.get("kind", "type")
                    doc["_from"] = f"{decl_collection}/{decl_key(doc['src'])}"
                    doc["_to"] = f"{decl_collection}/{decl_key(doc['dst'])}"
                    doc.setdefault("_key", edge_key(doc["src"], doc["kind"], doc["dst"]))
                edge_batch.append(doc)
                if len(edge_batch) >= batch_size:
                    import_batch(edge_collection, edge_batch)
                    edge_count += len(edge_batch)
                    edge_batch = []
            else:
                if "name" in doc:
                    doc["_key"] = doc.get("key") or decl_key(doc["name"])
                decl_batch.append(doc)
                if len(decl_batch) >= batch_size:
                    import_batch(decl_collection, decl_batch)
                    decl_count += len(decl_batch)
                    decl_batch = []

        if stream_error is None:
            if decl_batch:
                import_batch(decl_collection, decl_batch)
                decl_count += len(decl_batch)
                decl_batch = []
            if edge_batch:
                import_batch(edge_collection, edge_batch)
                edge_count += len(edge_batch)
                edge_batch = []
    except UnicodeError:
        # Preserve decoding/stream errors for callers while still reaping the child.
        raise
    except Exception as exc:
        stream_error = str(exc)
        try:
            for _line in proc.stdout:
                pass
        except UnicodeError:
            raise
        except Exception:
            pass
    finally:
        if proc.stdout is not None:
            proc.stdout.close()
        proc.wait()

    if stream_error is not None:
        print(f"[refresh-decl-graph] Streaming import failed: {stream_error}", file=sys.stderr)
        return 1
    if proc.returncode != 0:
        print(f"[refresh-decl-graph] Indexer failed with exit code {proc.returncode}", file=sys.stderr)
        return proc.returncode
    if generation_id is not None:
        if decl_count == 0:
            print("[refresh-decl-graph] immutable generation has no declarations", file=sys.stderr)
            return 1
        if ((expected_source_hash is not None
             and compute_lean_source_hash(root) != expected_source_hash)
                or (expected_olean_hash is not None
                    and compute_olean_content_hash(root) != expected_olean_hash)):
            print("[refresh-decl-graph] source/olean snapshot changed during export", file=sys.stderr)
            return 1

    # Now every declaration is present, so endpoint validation cannot discard a
    # forward reference merely because its target appeared later in the stream.
    orphan_query = """
    FOR e IN @@edgeCollection
      LET from_doc = DOCUMENT(e._from)
      LET to_doc = DOCUMENT(e._to)
      FILTER from_doc == null OR to_doc == null
      COLLECT WITH COUNT INTO removed
      RETURN removed
    """
    orphan_binds = {"@edgeCollection": edge_collection}
    if generation_id is not None:
        orphan_query = orphan_query.replace(
            "      FILTER from_doc == null OR to_doc == null",
            "      FILTER from_doc == null OR to_doc == null "
            "OR !IS_SAME_COLLECTION(@declCollection, e._from) "
            "OR !IS_SAME_COLLECTION(@declCollection, e._to)",
        )
        orphan_binds["declCollection"] = decl_collection
    orphan_rows = list(db.aql.execute(orphan_query, bind_vars=orphan_binds))
    orphan_edges = orphan_rows[0] if orphan_rows else 0
    if generation_id is not None and orphan_edges:
        print(
            f"[refresh-decl-graph] immutable generation has {orphan_edges} dangling or foreign edges; "
            "not publishing it",
            file=sys.stderr,
        )
        return 1
    removed_edges = 0
    if not generation_id and orphan_edges:
        remove_orphans = orphan_query.replace(
            "      COLLECT WITH COUNT INTO removed\n      RETURN removed",
            "      REMOVE e IN @@edgeCollection\n      COLLECT WITH COUNT INTO removed\n      RETURN removed",
        )
        removed_rows = list(db.aql.execute(remove_orphans, bind_vars={"@edgeCollection": edge_collection}))
        removed_edges = removed_rows[0] if removed_rows else 0
    valid_edge_count = db.collection(edge_collection).count()

    if generation_id is not None:
        declaration_rows = db.collection(decl_collection).count()
        if declaration_rows != decl_count:
            print(
                f"[refresh-decl-graph] declaration count mismatch: emitted={decl_count}, "
                f"stored={declaration_rows}; not publishing it",
                file=sys.stderr,
            )
            return 1
        if valid_edge_count != edge_count:
            print(
                f"[refresh-decl-graph] edge count mismatch: emitted={edge_count}, "
                f"stored={valid_edge_count}; not publishing it",
                file=sys.stderr,
            )
            return 1
        try:
            validate_generation_counts(decl_count, edge_count, valid_edge_count, removed_edges)
        except ValueError as exc:
            print(f"[refresh-decl-graph] invalid immutable generation: {exc}", file=sys.stderr)
            return 1
        generations = "decl_graph_generations"
        if not db.has_collection(generations):
            db.create_collection(generations)
        db.collection(generations).insert({
            "_key": generation_id,
            "schema": "info_geometry.decl_graph_generation.v1",
            "status": "complete",
            "buildFingerprint": build_fingerprint,
            "importRoot": import_root,
            "namespace": namespace,
            "declCollection": decl_collection,
            "edgeCollection": edge_collection,
            "declarationCount": decl_count,
            "emittedEdgeCount": edge_count,
            "removedOrphanCount": removed_edges,
            "validEdgeCount": valid_edge_count,
        }, overwrite=False, sync=True)

    print(
        f"[refresh-decl-graph] Imported {decl_count} declarations and "
        f"{edge_count} emitted edges to {database}; removed {removed_edges} "
        f"orphaned edges, retained {valid_edge_count} valid edges"
    )
    return 0


DEFAULT_IMPORT_ROOT = "InfoGeometry.All"
DEFAULT_BUILD_TARGET = "InfoGeometry.All"
DEFAULT_NAMESPACE = "InfoGeometry"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Refresh the authoritative declaration-DAG artifacts into the public artifacts/dag lane "
            "using lean/DAG/Indexer.lean."
        )
    )
    parser.add_argument(
        "--import-root",
        default=DEFAULT_IMPORT_ROOT,
        help="Comma-separated Lean import roots to index. Defaults to InfoGeometry.All (not Mathlib).",
    )
    parser.add_argument(
        "--build-target",
        default=DEFAULT_BUILD_TARGET,
        help="Lake build target to prebuild under the lock before indexing. Defaults to the import root.",
    )
    parser.add_argument(
        "--namespace",
        default=DEFAULT_NAMESPACE,
        help="Comma-separated namespace prefixes to keep in the exported declaration graph.",
    )
    parser.add_argument(
        "--index-dir",
        default=str(default_decl_index_dir().relative_to(repo_root())),
        help="Output directory for decls.jsonl/edges.jsonl/morphisms.jsonl/types.jsonl.",
    )
    parser.add_argument(
        "--graph-out",
        default=str(default_decl_graph_file().relative_to(repo_root())),
        help="Output path for full_graph.json.",
    )
    parser.add_argument(
        "--structure-out",
        default=str(default_decl_structure_file().relative_to(repo_root())),
        help="Output path for the native structural-topology artifact.",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Skip the olean content-hash check and always re-run the indexer.",
    )
    parser.add_argument(
        "--skip-prebuild",
        action="store_true",
        help="Skip the locked prebuild step and run the indexer directly.",
    )
    parser.add_argument(
        "--allow-prebuild-failure",
        action="store_true",
        help=(
            "Allow indexing to continue when locked prebuild fails. "
            "Default behavior is fail-fast to prevent stale/partial DAG contamination."
        ),
    )
    parser.add_argument(
        "--run-mode",
        choices=["exe", "run"],
        default="exe",
        help=(
            "Indexer invocation mode: `exe` uses the compiled lake executable "
            "(default, incremental-friendly); `run` uses `lake env lean --run`."
        ),
    )
    parser.add_argument(
        "--stream",
        action="store_true",
        help="Use streaming mode: pipe JSONL directly to ArangoDB instead of writing files.",
    )
    parser.add_argument(
        "--arango-db",
        default="infogeometry",
        help="ArangoDB database name for streaming import.",
    )
    parser.add_argument("--generation-id", help="Write a fresh immutable generation; never truncate existing graph collections.")
    parser.add_argument("--build-fingerprint", help="Required environment fingerprint for --generation-id.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()
    owner = f"decl-graph-refresh:{os.getpid()}"
    with acquire_build_lock(None, owner, block=True) as build_lock:
        return _run_refresh(args, root, build_lock)


def _run_refresh(args: argparse.Namespace, root: Path, build_lock: BuildLock) -> int:
    # Streaming mode: pipe directly to ArangoDB
    if args.stream:
        if args.generation_id is not None:
            if not args.build_fingerprint:
                raise SystemExit("--build-fingerprint is required with --generation-id")
            try:
                validate_generation_id(args.generation_id)
                validate_generation_metadata(
                    args.build_fingerprint, args.import_root, args.namespace
                )
            except ValueError as exc:
                raise SystemExit(f"invalid immutable generation metadata: {exc}") from exc
        return stream_to_arango(
            root, args.import_root, args.namespace, args.arango_db, args.run_mode,
            args.generation_id, args.build_fingerprint,
        )

    # File-based mode (original behavior)
    index_dir = normalize_repo_output(root, args.index_dir)
    graph_out = normalize_repo_output(root, args.graph_out)
    structure_out = normalize_repo_output(root, args.structure_out)
    meta_path = index_dir / "meta.json"

    # Content-hash incremental skip: avoid full re-import when oleans haven't changed.
    if not args.force:
        current_hash = compute_olean_content_hash(root)
        current_source_hash = compute_lean_source_hash(root)
        if should_skip_decl_refresh(
            meta_path,
            current_hash=current_hash,
            current_source_hash=current_source_hash,
            import_root=args.import_root,
            namespace=args.namespace,
        ):
            stale_sources = find_missing_decl_source_files(index_dir, limit=5)
            if stale_sources:
                sample = ", ".join(stale_sources)
                print(
                    "[refresh-decl-graph] stale decl source references detected; forcing refresh "
                    f"instead of skip (sample: {sample})",
                    flush=True,
                )
            else:
                print("[refresh-decl-graph] oleans unchanged since last run, skipping (use --force to override)", flush=True)
                return 0
    else:
        current_hash = compute_olean_content_hash(root)
        current_source_hash = compute_lean_source_hash(root)

    index_dir.mkdir(parents=True, exist_ok=True)
    graph_out.parent.mkdir(parents=True, exist_ok=True)
    structure_out.parent.mkdir(parents=True, exist_ok=True)

    if not args.skip_prebuild:
        run_locked_prebuild(
            root,
            args.build_target,
            run_mode=args.run_mode,
            python_executable=sys.executable,
            allow_failure=args.allow_prebuild_failure,
            build_lock=build_lock,
        )

    # Bind the exporter run to one stable source/olean snapshot. The preflight
    # hashes above may precede the build target, so take this receipt after the
    # optional build and compare it again after declaration extraction.
    source_hash_before_indexer = compute_lean_source_hash(root)
    olean_hash_before_indexer = compute_olean_content_hash(root)

    cmd = build_indexer_command(
        root,
        args.import_root,
        args.namespace,
        index_dir,
        graph_out,
        structure_out,
        run_mode=args.run_mode,
    )
    print(f"[refresh-decl-graph] running: {' '.join(cmd)}", flush=True)
    subprocess.run(cmd, cwd=root, check=True)

    # Recompute after prebuild/indexer execution so the stamped hash reflects
    # the build products that actually produced the refreshed artifacts.
    current_hash = compute_olean_content_hash(root)
    current_source_hash = compute_lean_source_hash(root)
    if current_hash != olean_hash_before_indexer:
        raise SystemExit(
            "[refresh-decl-graph] olean inventory changed during declaration export; "
            "refusing to stamp a mixed-generation index"
        )
    if current_source_hash != source_hash_before_indexer:
        raise SystemExit(
            "[refresh-decl-graph] source inventory changed during declaration export; "
            "refusing to stamp a mixed-generation index"
        )

    # Backfill the ISO timestamp that the Lean indexer cannot produce.
    # Also store the olean content hash for incremental skip on next run.
    if stamp_decl_index_meta(
        meta_path,
        olean_hash=current_hash,
        source_hash=current_source_hash,
        output_paths={
            "decls.jsonl": index_dir / "decls.jsonl",
            "edges.jsonl": index_dir / "edges.jsonl",
            "morphisms.jsonl": index_dir / "morphisms.jsonl",
            "types.jsonl": index_dir / "types.jsonl",
            "full_graph.json": graph_out,
            "structural-topology.json": structure_out,
        },
    ) is not None:
        print(f"[refresh-decl-graph] stamped {meta_path}", flush=True)
    meta = load_decl_index_meta(meta_path)
    timing_sidecar = write_indexer_timing_sidecar(index_dir, meta)
    if timing_sidecar is not None:
        print(f"[refresh-decl-graph] wrote {timing_sidecar}", flush=True)

    print(f"[refresh-decl-graph] wrote {graph_out}", flush=True)
    print(f"[refresh-decl-graph] wrote {structure_out}", flush=True)
    print(f"[refresh-decl-graph] wrote {index_dir}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
