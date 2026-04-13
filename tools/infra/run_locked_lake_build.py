#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.build import run_locked_lake_build
else:
    from tools.infra.build import run_locked_lake_build


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run `lake build` under the shared build lock used by the managed DAG/tooling lane."
    )
    parser.add_argument(
        "--wait-for-build-lock",
        action="store_true",
        help="Block until the shared build lock is available instead of failing immediately.",
    )
    parser.add_argument(
        "--wfail",
        action="store_true",
        help="Pass `--wfail` to `lake build` so warnings are treated as errors.",
    )
    parser.add_argument(
        "targets",
        nargs="*",
        help="Optional lake build targets. If omitted, this runs the default `lake build` target set.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    return run_locked_lake_build(
        args.targets, wait_for_lock=args.wait_for_build_lock, wfail=args.wfail
    )


if __name__ == "__main__":
    raise SystemExit(main())
