#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import (
        default_decl_graph_file,
        default_decl_index_dir,
        repo_root,
    )
else:
    from tools.pathing import (
        default_decl_graph_file,
        default_decl_index_dir,
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
    return parser.parse_args()


def normalize_output(root: Path, raw: str) -> Path:
    path = Path(raw)
    if path.is_absolute():
        return path
    return (root / path).resolve()


def main() -> int:
    args = parse_args()
    root = repo_root()
    index_dir = normalize_output(root, args.index_dir)
    graph_out = normalize_output(root, args.graph_out)
    index_dir.mkdir(parents=True, exist_ok=True)
    graph_out.parent.mkdir(parents=True, exist_ok=True)

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
    ]
    print(f"[refresh-decl-graph] running: {' '.join(cmd)}", flush=True)
    subprocess.run(cmd, cwd=root, check=True)
    print(f"[refresh-decl-graph] wrote {graph_out}", flush=True)
    print(f"[refresh-decl-graph] wrote {index_dir}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
