#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import (
        default_decl_graph_file,
        default_decl_index_dir,
        default_decl_meta_file,
        default_decl_structure_file,
        repo_root,
    )
else:
    from tools.pathing import (
        default_decl_graph_file,
        default_decl_index_dir,
        default_decl_meta_file,
        default_decl_structure_file,
        repo_root,
    )


DEFAULT_IMPORT_ROOT = "InfoGeometry.All"
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
        "--run-mode",
        choices=["exe", "run"],
        default="exe",
        help=(
            "Indexer invocation mode: `exe` uses the compiled lake executable "
            "(default, incremental-friendly); `run` uses `lake env lean --run`."
        ),
    )
    return parser.parse_args()


def normalize_output(root: Path, raw: str) -> Path:
    path = Path(raw)
    if path.is_absolute():
        return path
    return (root / path).resolve()


def _olean_content_hash(root: Path) -> str:
    """Compute a fast content hash over .olean files to detect environment changes."""
    import hashlib

    build_lib = root / ".lake" / "build" / "lib"
    if not build_lib.exists():
        build_lib = root / ".build" / "lib"
    if not build_lib.exists():
        return ""
    oleans = sorted(build_lib.rglob("*.olean"))
    h = hashlib.sha256()
    for p in oleans:
        h.update(p.name.encode())
        h.update(str(p.stat().st_mtime_ns).encode())
        h.update(str(p.stat().st_size).encode())
    return h.hexdigest()


# Expected indexer schema version.  Must match indexerSchemaVersion in
# lean/DAG/Indexer.lean.  If the Lean side bumps the version, artifacts
# produced by an older indexer are stale and must be regenerated.
EXPECTED_SCHEMA_VERSION = 3


def _should_skip(meta_path: Path, current_hash: str,
                 import_root: str, namespace: str) -> bool:
    """Return True if meta.json exists and its oleanHash, schemaVersion,
    importRoot, and nsFilter all match the current run parameters."""
    if not current_hash or not meta_path.exists():
        return False
    try:
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        if meta.get("oleanHash") != current_hash:
            return False
        if meta.get("importRoot") != import_root:
            return False
        if meta.get("nsFilter") != namespace:
            return False
        if meta.get("schemaVersion") != EXPECTED_SCHEMA_VERSION:
            return False
        return True
    except Exception:
        return False


def _run_locked_prebuild(root: Path, import_root: str) -> bool:
    cmd = [
        sys.executable,
        "tools/infra/run_locked_lake_build.py",
        "--wait-for-build-lock",
        "DAG.Indexer",
        import_root,
    ]
    print(f"[refresh-decl-graph] prebuilding with lock: {' '.join(cmd)}", flush=True)
    try:
        subprocess.run(cmd, cwd=root, check=True)
        return True
    except subprocess.CalledProcessError as exc:
        print(
            "[refresh-decl-graph] prebuild failed; continuing with direct indexer run "
            f"(exit={exc.returncode})",
            file=sys.stderr,
            flush=True,
        )
        return False


def main() -> int:
    args = parse_args()
    root = repo_root()
    index_dir = normalize_output(root, args.index_dir)
    graph_out = normalize_output(root, args.graph_out)
    structure_out = normalize_output(root, args.structure_out)
    meta_path = index_dir / "meta.json"

    # Content-hash incremental skip: avoid full re-import when oleans haven't changed.
    if not args.force:
        current_hash = _olean_content_hash(root)
        if _should_skip(meta_path, current_hash, args.import_root, args.namespace):
            print("[refresh-decl-graph] oleans unchanged since last run, skipping (use --force to override)", flush=True)
            return 0
    else:
        current_hash = _olean_content_hash(root)

    index_dir.mkdir(parents=True, exist_ok=True)
    graph_out.parent.mkdir(parents=True, exist_ok=True)
    structure_out.parent.mkdir(parents=True, exist_ok=True)

    if not args.skip_prebuild:
        _run_locked_prebuild(root, args.import_root)

    if args.run_mode == "exe":
        cmd = [
            "lake",
            "env",
            "dagIndexer",
            args.import_root,
            args.namespace,
            str(index_dir),
            str(graph_out),
            str(structure_out),
        ]
    else:
        cmd = [
            "lake",
            "env",
            "lean",
            "--run",
            "lean/DAG/Indexer.lean",
            args.import_root,
            args.namespace,
            str(index_dir),
            str(graph_out),
            str(structure_out),
        ]
    print(f"[refresh-decl-graph] running: {' '.join(cmd)}", flush=True)
    subprocess.run(cmd, cwd=root, check=True)

    # Backfill the ISO timestamp that the Lean indexer cannot produce.
    # Also store the olean content hash for incremental skip on next run.
    if meta_path.exists():
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        meta["timestamp"] = datetime.now(timezone.utc).isoformat()
        if current_hash:
            meta["oleanHash"] = current_hash
        meta_path.write_text(json.dumps(meta, indent=2) + "\n", encoding="utf-8")
        print(f"[refresh-decl-graph] stamped {meta_path}", flush=True)

    print(f"[refresh-decl-graph] wrote {graph_out}", flush=True)
    print(f"[refresh-decl-graph] wrote {structure_out}", flush=True)
    print(f"[refresh-decl-graph] wrote {index_dir}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
