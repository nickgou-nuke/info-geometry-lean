#!/usr/bin/env python3
"""Run one Lean elaboration under the repository build lock.

File-level elaboration is a compilation operation and must not race a Lake
build.  This helper keeps audit scripts on the same serialized lane as the
incremental owner builds.
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.build_lock import BuildLockBusyError, acquire_build_lock
from tools.pathing import repo_root


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run lake env lean under the shared build lock.")
    parser.add_argument("--wait-for-build-lock", action="store_true")
    parser.add_argument("--no-wait-for-build-lock", dest="wait", action="store_false")
    parser.set_defaults(wait=True)
    parser.add_argument("file", help="Lean source file to elaborate")
    parser.add_argument("lean_args", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)

    root = repo_root()
    source = Path(args.file)
    if source.is_absolute():
        try:
            source = source.resolve().relative_to(root.resolve())
        except ValueError:
            print("[locked-lean] file must be inside the repository", file=sys.stderr)
            return 2
    if source.suffix != ".lean" or not (root / source).is_file():
        print(f"[locked-lean] Lean file not found: {source}", file=sys.stderr)
        return 2

    owner = f"locked-lean:{os.getpid()}:{source}"
    try:
        lock = acquire_build_lock(None, owner, block=args.wait)
    except BuildLockBusyError as exc:
        print(f"[locked-lean] build lock is held at {exc.lock_path}", file=sys.stderr)
        return 2
    except OSError as exc:
        print(f"[locked-lean] could not acquire build lock: {exc}", file=sys.stderr)
        return 126

    try:
        command = ["lake", "env", "lean", str(source), *args.lean_args]
        print(f"[locked-lean] executing: {' '.join(command)}", flush=True)
        return subprocess.run(command, cwd=root, check=False).returncode
    finally:
        lock.release()


if __name__ == "__main__":
    raise SystemExit(main())
