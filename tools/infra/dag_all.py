#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
    from tools.infra.build import log_spectral_stage
else:
    from tools.pathing import repo_root
    from tools.infra.build import log_spectral_stage


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

    log_spectral_stage("PREP", "dag-all", "managed DAG lane")
    step_stage = {
        "dagStatus": "PREP",
        "dagRefresh": "DECOMP",
        "dagReports": "ASSIGN",
        "dagDoctor": "PAULI",
    }
    for i, (label, cmd) in enumerate(steps, start=1):
        stage = step_stage.get(label, "ASSIGN")
        log_spectral_stage(stage, f"dag-all:{label}", f"step {i}/{len(steps)} {' '.join(cmd)}")
        if args.dry_run:
            continue
        completed = subprocess.run(cmd, cwd=root, check=False)
        if completed.returncode != 0:
            log_spectral_stage(
                "CONGEST",
                f"dag-all:{label}",
                f"failed with exit code {completed.returncode}",
            )
            return completed.returncode

    if args.dry_run:
        log_spectral_stage("ATLAS", "dag-all", "dry-run only; no commands executed")
    else:
        log_spectral_stage("CRYSTAL", "dag-all", "managed DAG lane completed successfully")
        log_spectral_stage("ATLAS", "dag-all", "status/refresh/reports/doctor registry up to date")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
