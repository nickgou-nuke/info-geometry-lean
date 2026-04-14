#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
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
        help="Lean import root to index. Use InfoGeometry.All for the public umbrella, or a stronger root when intentionally widening coverage.",
    )
    parser.add_argument(
        "--build-target",
        default=DEFAULT_BUILD_TARGET,
        help="Lake build target to prebuild under the lock before indexing. Defaults to the import root.",
    )
    parser.add_argument(
        "--namespace",
        default=DEFAULT_NAMESPACE,
        help="Namespace prefix to keep in the exported declaration graph.",
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
    return parser.parse_args()

def main() -> int:
    args = parse_args()
    root = repo_root()
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
