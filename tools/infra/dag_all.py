#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
else:
    from tools.pathing import repo_root


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the managed DAG operator lane: status, refresh, reports, doctor."
    )
    parser.add_argument(
        "--config",
        help="Optional dag-toolchain.json override passed through to each managed step.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print the resolved commands without executing them.",
    )
    return parser.parse_args()


def step_command(script: str, *, config: str | None) -> list[str]:
    cmd = [sys.executable, script]
    if config:
        cmd.extend(["--config", config])
    return cmd


def main() -> int:
    args = parse_args()
    root = repo_root()
    steps = [
        ("dagStatus", step_command("tools/infra/dag_status.py", config=args.config)),
        ("dagRefresh", step_command("tools/infra/dag_refresh.py", config=args.config)),
        ("dagReports", step_command("tools/infra/dag_reports.py", config=args.config)),
        ("dagDoctor", step_command("tools/infra/dag_doctor.py", config=args.config)),
    ]

    print("[dag-all] managed DAG lane", flush=True)
    for i, (label, cmd) in enumerate(steps, start=1):
        print(f"[dag-all] step {i}/{len(steps)} {label}: {' '.join(cmd)}", flush=True)
        if args.dry_run:
            continue
        completed = subprocess.run(cmd, cwd=root, check=False)
        if completed.returncode != 0:
            print(f"[dag-all] failed at {label}", flush=True)
            return completed.returncode

    if args.dry_run:
        print("[dag-all] dry-run only; no commands executed", flush=True)
    else:
        print("[dag-all] completed successfully", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
