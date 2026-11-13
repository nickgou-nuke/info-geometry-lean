#!/usr/bin/env python3
"""Run the focused real matrix split package under the repository's shared build lock."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[1]
sys.path.insert(0, str(ROOT))

from tools.build_lock import acquire_build_lock  # noqa: E402
from tools.infra.build import (  # noqa: E402
    _interrupt_child_and_wait,
    _validate_lake_workspace_integrity,
)


def main() -> int:
    for directory in (ROOT, PROJECT):
        error = _validate_lake_workspace_integrity(directory)
        if error:
            print(error, file=sys.stderr)
            return 2
    command = ["lake", "-d", str(PROJECT), *(sys.argv[1:] or ["build"])]
    print("[real-matrix-split] waiting for the shared build lock", flush=True)
    lock = acquire_build_lock(None, f"real-matrix-split:{os.getpid()}", block=True)
    process = None
    try:
        print("[real-matrix-split] " + " ".join(command), flush=True)
        process = subprocess.Popen(command, cwd=ROOT, start_new_session=(os.name == "posix"))
        try:
            return process.wait()
        except KeyboardInterrupt:
            _interrupt_child_and_wait(process)
            return 130
    finally:
        if process is not None and process.poll() is None:
            _interrupt_child_and_wait(process)
        lock.release()


if __name__ == "__main__":
    raise SystemExit(main())
