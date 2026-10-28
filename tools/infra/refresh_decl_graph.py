#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
_SRC = Path(__file__).resolve().parents[2] / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
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
    from igf.graph.decl_schema import decl_key, edge_key
else:
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
    from igf.graph.decl_schema import decl_key, edge_key


def stream_to_arango(
    root: Path, import_root: str, namespace: str, database: str, run_mode: str,
    generation_id: str | None = None, build_fingerprint: str | None = None,
) -> int:
    """Stream JSONL from dagIndexer directly to ArangoDB."""
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

    # Stream JSONL to ArangoDB
    proc = subprocess.Popen(cmd, cwd=root, stdout=subprocess.PIPE, stderr=None, text=True)

    decl_count = 0
    edge_count = 0
    batch_size = 5000
    decl_batch = []
    edge_batch = []
    def import_batch(collection_name: str, batch: list[dict]) -> None:
        """Append one stream batch to a collection truncated before this run."""
        result = db[collection_name].import_bulk(
            batch, overwrite=False, on_duplicate="replace"
        )
        if isinstance(result, dict) and int(result.get("errors", 0) or 0) > 0:
            raise RuntimeError(
                f"Arango import errors in {collection_name}: {result}"
            )

    try:
        for line in proc.stdout:
            line = line.strip()
            if not line:
                continue
            try:
                doc = json.loads(line)
            except json.JSONDecodeError:
                continue

            # Determine if it's a decl or edge by checking for src/dst fields (streaming format) or _from/_to (file format)
            if ("_from" in doc and "_to" in doc) or ("src" in doc and "dst" in doc):
                # Convert streaming format (src/dst/kind) to ArangoDB format (_from/_to)
                if "src" in doc and "dst" in doc:
                    # Shared schema keys (igf.graph.decl_schema == DAG.Schema in Lean);
                    # deterministic edge keys make re-imports idempotent.
                    doc["kind"] = doc.get("kind", "type")
                    doc["_from"] = f"{decl_collection}/{decl_key(doc['src'])}"
                    doc["_to"] = f"{decl_collection}/{decl_key(doc['dst'])}"
                    doc.setdefault("_key", edge_key(doc["src"], doc["kind"], doc["dst"]))
                edge_batch.append(doc)
                if len(edge_batch) >= batch_size:
                    # Endpoint declarations may occur later in the alphabetical
                    # declaration stream.  Preserve every emitted edge now and
                    # validate endpoints only after the declaration stream ends.
                    import_batch(edge_collection, edge_batch)
                    edge_count += len(edge_batch)
                    edge_batch = []
            else:
                # Ensure _key exists
                if "name" in doc:
                    # The Lean indexer now emits `key` (DAG.Schema.declKey); fall back
                    # to the identical Python formula for older producers.
                    doc["_key"] = doc.get("key") or decl_key(doc["name"])
                decl_batch.append(doc)
                if len(decl_batch) >= batch_size:
                    import_batch(decl_collection, decl_batch)
                    decl_count += len(decl_batch)
                    decl_batch = []

        # Flush remaining batches
        if decl_batch:
            import_batch(decl_collection, decl_batch)
            decl_count += len(decl_batch)
        if edge_batch:
            import_batch(edge_collection, edge_batch)
            edge_count += len(edge_batch)
            edge_batch = []

        proc.wait()
        if proc.returncode != 0:
            print(f"[refresh-decl-graph] Indexer failed with exit code {proc.returncode}", file=sys.stderr)
            return proc.returncode

    except Exception as e:
        print(f"[refresh-decl-graph] Streaming import failed: {e}", file=sys.stderr)
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
    orphan_rows = list(db.aql.execute(orphan_query, bind_vars={"@edgeCollection": edge_collection}))
    orphan_edges = orphan_rows[0] if orphan_rows else 0
    if generation_id and orphan_edges:
        print(
            f"[refresh-decl-graph] immutable generation has {orphan_edges} dangling edges; "
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

    if generation_id:
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

    # Streaming mode: pipe directly to ArangoDB
    if args.stream:
        if args.generation_id and not args.build_fingerprint:
            raise SystemExit("--build-fingerprint is required with --generation-id")
        if args.generation_id and (
            len(args.generation_id) > 32
            or not all(ch.isalnum() or ch in "_-" for ch in args.generation_id)
        ):
            raise SystemExit("--generation-id must be at most 32 letters, digits, '_' or '-'")
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
        )

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

    # Backfill the ISO timestamp that the Lean indexer cannot produce.
    # Also store the olean content hash for incremental skip on next run.
    if stamp_decl_index_meta(
        meta_path,
        olean_hash=current_hash,
        source_hash=current_source_hash,
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
