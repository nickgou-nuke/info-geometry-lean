#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.artifacts import load_decl_index_meta
    from tools.infra.dag_config import load_dag_toolchain_config, repo_display_path
    from tools.infra.timings import report_timing_json_path, write_report_timing_sidecar
    from tools.pathing import repo_root
else:
    from tools.infra.artifacts import load_decl_index_meta
    from tools.infra.dag_config import load_dag_toolchain_config, repo_display_path
    from tools.infra.timings import report_timing_json_path, write_report_timing_sidecar
    from tools.pathing import repo_root


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the managed derived DAG report sequence from dag-toolchain.json."
    )
    parser.add_argument(
        "--config",
        help="Optional dag-toolchain.json override. Defaults to dag-toolchain.local.json when present, else dag-toolchain.json.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print the resolved report commands without executing them.",
    )
    return parser.parse_args()


def resolve_step_command(step: tuple[str, ...]) -> list[str]:
    first = step[0]
    if first.endswith(".py"):
        return [sys.executable, *step]
    return list(step)


def build_report_env(root: Path) -> dict[str, str]:
    env = os.environ.copy()
    # Keep matplotlib caches inside the repo-controlled artifact lane so managed
    # report runs do not depend on a writable home-directory config path.
    mpl_dir = root / ".artifacts" / "matplotlib"
    mpl_dir.mkdir(parents=True, exist_ok=True)
    env["MPLCONFIGDIR"] = str(mpl_dir)
    return env


def main() -> int:
    args = parse_args()
    config = load_dag_toolchain_config(args.config)
    root = repo_root()
    env = build_report_env(root)
    meta_path = config.authoritative_artifacts.index_dir / "meta.json"
    meta = load_decl_index_meta(meta_path) or {}
    timing_path = report_timing_json_path(root)
    steps: list[dict[str, object]] = []
    run_start = time.perf_counter()
    status = "ok"

    print(f"[dag-reports] config: {repo_display_path(config.config_path, root)}", flush=True)
    print(f"[dag-reports] MPLCONFIGDIR: {repo_display_path(Path(env['MPLCONFIGDIR']), root)}", flush=True)
    for i, step in enumerate(config.derived_reports.report_sequence, start=1):
        cmd = resolve_step_command(step)
        print(f"[dag-reports] step {i}: {' '.join(cmd)}", flush=True)
        if args.dry_run:
            continue
        step_start = time.perf_counter()
        completed = subprocess.run(cmd, cwd=root, check=False, env=env)
        elapsed_ms = int((time.perf_counter() - step_start) * 1000)
        steps.append(
            {
                "index": i,
                "label": step[0],
                "command": cmd,
                "elapsed_ms": elapsed_ms,
                "exit_code": completed.returncode,
            }
        )
        if completed.returncode != 0:
            status = "failed"
            write_report_timing_sidecar(
                timing_path,
                config_path=config.config_path,
                meta=meta,
                steps=steps,
                total_ms=int((time.perf_counter() - run_start) * 1000),
                status=status,
            )
            raise SystemExit(completed.returncode)
    if not args.dry_run:
        write_report_timing_sidecar(
            timing_path,
            config_path=config.config_path,
            meta=meta,
            steps=steps,
            total_ms=int((time.perf_counter() - run_start) * 1000),
            status=status,
        )
        print(f"[dag-reports] wrote {repo_display_path(timing_path, root)}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
