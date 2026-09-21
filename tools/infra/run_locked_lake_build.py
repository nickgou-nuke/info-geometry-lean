#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Sequence

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.build import run_locked_lake_build
else:
    from tools.infra.build import run_locked_lake_build


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    """Parse wrapper options separately from arguments intended for Lake.

    Lake options must follow `--` (for example, `... -- -R`). This prevents
    argparse from consuming Lake flags and makes the executed argv auditable.
    """
    raw = list(sys.argv[1:] if argv is None else argv)
    if "--" in raw:
        separator = raw.index("--")
        wrapper_argv, lake_argv = raw[:separator], raw[separator + 1:]
    else:
        wrapper_argv, lake_argv = raw, []

    parser = argparse.ArgumentParser(
        description=(
            "Run `lake build` under the repository-wide build lock. "
            "Pass Lake options after `--`; positional arguments are build targets."
        )
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
    parser.add_argument("targets", nargs="*", help="Lake build targets.")
    args = parser.parse_args(wrapper_argv)
    args.lake_args = lake_argv
    return args


def main() -> int:
    args = parse_args()
    return run_locked_lake_build(
        [*args.targets, *args.lake_args],
        wait_for_lock=args.wait_for_build_lock,
        wfail=args.wfail,
    )


if __name__ == "__main__":
    raise SystemExit(main())
