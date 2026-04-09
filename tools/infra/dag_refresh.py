#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.dag_config import load_dag_toolchain_config, repo_display_path
    from tools.pathing import repo_root
else:
    from tools.infra.dag_config import load_dag_toolchain_config, repo_display_path
    from tools.pathing import repo_root


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Refresh the authoritative DAG artifacts using the checked-in DAG toolchain config."
    )
    parser.add_argument(
        "--config",
        help="Optional dag-toolchain.json override. Defaults to dag-toolchain.local.json when present, else dag-toolchain.json.",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Forward `--force` to refresh_decl_graph.py.",
    )
    parser.add_argument(
        "--skip-prebuild",
        action="store_true",
        help="Forward `--skip-prebuild` to refresh_decl_graph.py.",
    )
    parser.add_argument(
        "--run-mode",
        choices=["exe", "run"],
        help="Override the configured indexer run mode for this invocation.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print the resolved refresh command without executing it.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    config = load_dag_toolchain_config(args.config)
    root = repo_root()
    run_mode = args.run_mode or config.build.run_mode

    cmd = [
        sys.executable,
        "tools/infra/refresh_decl_graph.py",
        "--import-root",
        config.build.import_root,
        "--build-target",
        config.build.build_target,
        "--namespace",
        config.build.namespace_filter,
        "--index-dir",
        repo_display_path(config.authoritative_artifacts.index_dir, root),
        "--graph-out",
        repo_display_path(config.authoritative_artifacts.graph_out, root),
        "--structure-out",
        repo_display_path(config.authoritative_artifacts.structure_out, root),
        "--run-mode",
        run_mode,
    ]
    if args.force:
        cmd.append("--force")
    if args.skip_prebuild:
        cmd.append("--skip-prebuild")

    print(f"[dag-refresh] config: {repo_display_path(config.config_path, root)}", flush=True)
    print(f"[dag-refresh] running: {' '.join(cmd)}", flush=True)
    if args.dry_run:
        return 0
    return subprocess.run(cmd, cwd=root).returncode


if __name__ == "__main__":
    raise SystemExit(main())
