#!/usr/bin/env python3
"""Batch runner for Socratic alchemy loops over multiple seed prompt files."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--prompt-file", action="append", default=[])
    p.add_argument("--prompt-glob", default="")
    p.add_argument("--reason", default="batch Socratic alchemy")
    p.add_argument("--run-prefix", default="batch-seed")
    p.add_argument("--concept-rounds", type=int, default=2)
    p.add_argument("--repair-rounds", type=int, default=1)
    p.add_argument("--lean-import", action="append", default=["Mathlib"])
    p.add_argument("--stop-on-failure", action="store_true")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[2]
    prompts: list[Path] = []
    for raw in args.prompt_file:
        p = Path(raw)
        if not p.is_absolute():
            p = (repo_root / p).resolve()
        prompts.append(p)
    if args.prompt_glob:
        prompts.extend(sorted((repo_root).glob(args.prompt_glob)))
    prompts = [p for p in prompts if p.exists()]
    if not prompts:
        raise SystemExit("no prompt files found")

    rc = 0
    for idx, prompt in enumerate(prompts, start=1):
        run_name = f"{args.run_prefix}-{idx:02d}-{prompt.stem}"
        cmd = [
            "python3",
            "tools/infra/run_socratic_alchemy_loop.py",
            "--prompt-file",
            str(prompt),
            "--run-name",
            run_name,
            "--reason",
            args.reason,
            "--concept-rounds",
            str(args.concept_rounds),
            "--repair-rounds",
            str(args.repair_rounds),
        ]
        for item in args.lean_import:
            cmd.extend(["--lean-import", item])
        proc = subprocess.run(cmd, cwd=repo_root, text=True, capture_output=True, check=False)
        sys.stdout.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        if proc.returncode != 0:
            rc = proc.returncode
            if args.stop_on_failure:
                return rc
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
