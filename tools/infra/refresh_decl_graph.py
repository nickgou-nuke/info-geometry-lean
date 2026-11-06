#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
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
from tools.infra.decl_graph_generation import (
    validate_generation_counts,
    validate_generation_metadata,
    validate_generation_id,
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


def validate_stream_record(doc: object, decl_collection: str) -> None:
    """Validate identity-bearing fields before normalization or database writes.

    Accept declaration records, src/dst edges, and legacy _from/_to edges.
    Extra compiler metadata is preserved; this is not full fingerprint-schema
    validation. Blank stream lines remain legal (the indexer emits a flush line).
    """
    if not isinstance(doc, dict):
        raise ValueError("stream record must be a JSON object")
    edge = any(field in doc for field in ("src", "dst", "_from", "_to"))
    def nonempty(field: str) -> str:
        value = doc.get(field)
        if not isinstance(value, str) or not value.strip():
            raise ValueError(f"stream record has invalid {field}")
        return value
    if edge:
        if "name" in doc:
            raise ValueError("ambiguous declaration/edge record")
        if nonempty("kind") not in ("type", "value"):
            raise ValueError("invalid dependency edge kind")
        named = "src" in doc or "dst" in doc
        addressed = "_from" in doc or "_to" in doc
        if named:
            src, dst = nonempty("src"), nonempty("dst")
            if "_key" in doc and doc["_key"] != edge_key(src, doc["kind"], dst):
                raise ValueError("edge key disagrees with dependency identity")
        if addressed:
            for field in ("_from", "_to"):
                value = nonempty(field)
                collection, separator, key = value.partition("/")
                if collection != decl_collection or not separator or not key or "/" in key:
                    raise ValueError("edge endpoint is outside selected declaration collection")
            if named and (doc["_from"] != f"{decl_collection}/{decl_key(src)}"
                          or doc["_to"] != f"{decl_collection}/{decl_key(dst)}"):
                raise ValueError("edge endpoint disagrees with named identity")
        if "_key" in doc:
            nonempty("_key")
    else:
        name = nonempty("name")
        for field in ("key", "_key"):
            if field in doc and doc[field] != decl_key(name):
                raise ValueError("declaration key disagrees with name")


def stream_to_arango(
    root: Path, import_root: str, namespace: str, database: str, run_mode: str,
    generation_id: str | None = None, build_fingerprint: str | None = None,
    expected_source_hash: str | None = None, expected_olean_hash: str | None = None,
) -> int:
    """Stream JSONL from dagIndexer directly to ArangoDB."""
    if generation_id is not None:
        try:
            validate_generation_id(generation_id)
            validate_generation_metadata(build_fingerprint, import_root, namespace)
        except ValueError as exc:
            print(f"[refresh-decl-graph] {exc}", file=sys.stderr)
            return 1
    load_repo_arango_env(root)

    # `HomotopyHypothesis` and this checkout both expose an `OAI` library.
    # Lake puts dependency paths before the root path, so an indexer process
    # using the default order can resolve the partial dependency OAI library
    # and fail to load root-owned OAI declarations. Put the already-built root
    # library first for the indexer process while preserving Lake's remaining
    # search path.
    path_result = subprocess.run(
        ["lake", "env", "printenv", "LEAN_PATH"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    root_lean_path = str(root / ".lake" / "build" / "lib" / "lean")
    lake_paths = [
        path for path in path_result.stdout.strip().split(os.pathsep)
        if path and path != root_lean_path
    ]
    lean_path = os.pathsep.join([root_lean_path, *lake_paths])

    # Build the streaming command
    if run_mode == "exe":
        base_cmd = [
            "lake", "env",
            str(root / ".lake" / "build" / "bin" / "dagIndexer"),
            import_root, namespace, "--stream"
        ]
    else:
        base_cmd = ["lake", "env", "lean", "--run", "lean/DAG/Indexer.lean", import_root, namespace, "--stream"]
    cmd = base_cmd[:2] + ["env", f"LEAN_PATH={lean_path}"] + base_cmd[2:]

    print(f"[refresh-decl-graph] streaming: {' '.join(cmd)}", flush=True)

    # Check the executable before creating or truncating any target collection.
    if run_mode == "exe" and not Path(base_cmd[2]).is_file():
        print(f"Error: DAG indexer executable not found: {base_cmd[2]}", file=sys.stderr)
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
            doc = json.loads(line)
            validate_stream_record(doc, decl_collection)
            if not isinstance(doc, dict):
                raise ValueError("indexer record must be a JSON object")

            # Determine if it's a decl or edge by checking for src/dst fields (streaming format) or _from/_to (file format)
            if ("_from" in doc and "_to" in doc) or ("src" in doc and "dst" in doc):
                if generation_id and not all(
                    isinstance(doc.get(field), str) and doc[field]
                    for field in ("src", "dst")
                ):
                    raise ValueError("immutable edges require nonempty src/dst declaration names")
                if generation_id and doc.get("kind") not in ("type", "value"):
                    raise ValueError("immutable dependency edge has an unknown kind")
                # Convert streaming format (src/dst/kind) to ArangoDB format (_from/_to)
                if "src" in doc and "dst" in doc:
                    # Shared schema keys (igf.graph.decl_schema == DAG.Schema in Lean);
                    # deterministic edge keys make re-imports idempotent.
                    doc["kind"] = doc.get("kind", "type")
                    doc["_from"] = f"{decl_collection}/{decl_key(doc['src'])}"
                    doc["_to"] = f"{decl_collection}/{decl_key(doc['dst'])}"
                    doc["_key"] = edge_key(doc["src"], doc["kind"], doc["dst"])
                edge_batch.append(doc)
                if len(edge_batch) >= batch_size:
                    # Endpoint declarations may occur later in the alphabetical
                    # declaration stream.  Preserve every emitted edge now and
                    # validate endpoints only after the declaration stream ends.
                    import_batch(edge_collection, edge_batch)
                    edge_count += len(edge_batch)
                    edge_batch = []
            else:
                if not isinstance(doc.get("name"), str) or not doc["name"]:
                    raise ValueError("indexer declaration requires a nonempty name")
                # Ensure _key exists
                if "name" in doc:
                    # The Lean indexer now emits `key` (DAG.Schema.declKey); fall back
                    # to the identical Python formula for older producers.
                    expected_key = decl_key(doc["name"])
                    if doc.get("key", expected_key) != expected_key:
                        raise ValueError("indexer declaration key disagrees with its name")
                    doc["_key"] = expected_key
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
    finally:
        # Preserve single-flight ownership on failure too. Drain rather than
        # kill the compiler/exporter, then reap it before releasing the lock.
        try:
            if proc.poll() is None:
                for _ in proc.stdout:
                    pass
        finally:
            try:
                proc.stdout.close()
            finally:
                proc.wait()

    stored_decl_count = db.collection(decl_collection).count()
    if generation_id and (decl_count == 0 or stored_decl_count != decl_count):
        print("[refresh-decl-graph] empty or inconsistent declaration stream; not publishing",
              file=sys.stderr)
        return 1

    # Now every declaration is present, so endpoint validation cannot discard a
    # forward reference merely because its target appeared later in the stream.
    orphan_query = """
    FOR e IN @@edgeCollection
      LET from_doc = DOCUMENT(e._from)
      LET to_doc = DOCUMENT(e._to)
      FILTER from_doc == null OR to_doc == null
        OR NOT IS_SAME_COLLECTION(@declCollection, e._from)
        OR NOT IS_SAME_COLLECTION(@declCollection, e._to)
      COLLECT WITH COUNT INTO removed
      RETURN removed
    """
    orphan_rows = list(db.aql.execute(orphan_query, bind_vars={"@edgeCollection": edge_collection, "declCollection": decl_collection}))
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
        removed_rows = list(db.aql.execute(remove_orphans, bind_vars={"@edgeCollection": edge_collection, "declCollection": decl_collection}))
        removed_edges = removed_rows[0] if removed_rows else 0
    valid_edge_count = db.collection(edge_collection).count()
    if generation_id and valid_edge_count != edge_count:
        print("[refresh-decl-graph] emitted/stored edge counts disagree; not publishing",
              file=sys.stderr)
        return 1

    if generation_id:
        try:
            validate_generation_counts(decl_count, edge_count, valid_edge_count, removed_edges)
        except ValueError as exc:
            print(f"[refresh-decl-graph] {exc}; generation is not published", file=sys.stderr)
            return 1
        # Do not publish a coherent-generation receipt if source or built
        # artifacts changed during the (potentially long) stream.
        if expected_source_hash is not None and compute_lean_source_hash(root) != expected_source_hash:
            print(
                "[refresh-decl-graph] source inventory changed during stream; "
                "generation is not published",
                file=sys.stderr,
            )
            return 1
        if expected_olean_hash is not None and compute_olean_content_hash(root) != expected_olean_hash:
            print(
                "[refresh-decl-graph] OLean inventory changed during stream; "
                "generation is not published",
                file=sys.stderr,
            )
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
        help=(
            "Pipe JSONL directly to ArangoDB. Defaults to an immutable, "
            "content-fingerprinted generation; use --replace-live only for explicit replacement."
        ),
    )
    parser.add_argument(
        "--arango-db",
        default="infogeometry",
        help="ArangoDB database name for streaming import.",
    )
    parser.add_argument(
        "--generation-id",
        help="Immutable generation ID; 'auto' (the streaming default) derives an ID and fingerprint under the build lock.",
    )
    parser.add_argument(
        "--build-fingerprint",
        help="Fingerprint for an explicit --generation-id; auto generations compute it internally.",
    )
    parser.add_argument(
        "--replace-live",
        action="store_true",
        help="Explicitly truncate and replace legacy decls/edges during --stream (destructive).",
    )
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
        if args.replace_live and (args.generation_id or args.build_fingerprint):
            raise SystemExit("--replace-live cannot be combined with immutable-generation options")
        if not args.replace_live and args.build_fingerprint and not args.generation_id:
            raise SystemExit("--build-fingerprint requires --generation-id")
        expected_source_hash = None
        expected_olean_hash = None
        generation_id = None if args.replace_live else (
            "auto" if args.generation_id is None else args.generation_id
        )
        build_fingerprint = args.build_fingerprint
        if generation_id == "auto":
            if build_fingerprint:
                raise SystemExit("--build-fingerprint is computed internally with --generation-id auto")
            expected_source_hash = compute_lean_source_hash(root)
            expected_olean_hash = compute_olean_content_hash(root)
            if not expected_source_hash or not expected_olean_hash:
                raise SystemExit(
                    "cannot create an immutable generation without complete source and OLean inventories"
                )
            manifest_path = root / "lake-manifest.json"
            identity = {
                "schema": "info_geometry.decl_graph_build.v1",
                "leanPathOrder": "repository-first-v1",
                "sourceHash": expected_source_hash,
                "oleanHash": expected_olean_hash,
                "toolchain": (root / "lean-toolchain").read_text().strip(),
                "manifestSha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
                "importRoot": args.import_root,
                "namespace": args.namespace,
            }
            build_fingerprint = hashlib.sha256(
                json.dumps(identity, sort_keys=True, separators=(",", ":")).encode("utf-8")
            ).hexdigest()
            generation_id = f"decl_{build_fingerprint[:24]}"
            print(
                f"[refresh-decl-graph] immutable generation: {generation_id} "
                f"(build fingerprint {build_fingerprint})",
                flush=True,
            )
        if generation_id and generation_id != "auto" and not build_fingerprint:
            raise SystemExit("--build-fingerprint is required with an explicit --generation-id")
        if generation_id is not None:
            try:
                validate_generation_id(generation_id)
            except ValueError as exc:
                raise SystemExit(f"--generation-id: {exc}") from exc
        return stream_to_arango(
            root, args.import_root, args.namespace, args.arango_db, args.run_mode,
            generation_id, build_fingerprint, expected_source_hash, expected_olean_hash,
        )

    if args.replace_live:
        raise SystemExit("--replace-live requires --stream")

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
