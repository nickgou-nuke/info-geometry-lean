#!/usr/bin/env python3
"""Run an isolated GRH-package command under InfoGeometry's shared build lock."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[1]
sys.path.insert(0, str(ROOT))
from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        parser.error("supply the command after --")
    for path in (ROOT / ".git", PACKAGE / ".lake", PACKAGE / ".lake/packages"):
        if path.is_symlink() or (path.name == ".git" and path.is_file()):
            parser.error(f"linked worktrees and symlinked build roots are unsupported: {path}")
    with BuildLock(DEFAULT_BUILD_LOCK_PATH, "grh-compatibility", block=True) as lock:
        print("Running in", PACKAGE, ":", command, flush=True)
        result = subprocess.run(
            command,
            cwd=PACKAGE,
            env=os.environ.copy(),
            pass_fds=(lock.fileno(),),
            check=False,
        )
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
