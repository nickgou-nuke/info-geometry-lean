#!/usr/bin/env python3
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.build_lock import BuildLockBusyError, acquire_build_lock
else:
    from tools.build_lock import BuildLockBusyError, acquire_build_lock


def main() -> int:
    args = sys.argv[1:]
    wait = False
    if args and args[0] == "--wait-for-build-lock":
        wait = True
        args = args[1:]

    owner = f"locked-lake-build:{os.getpid()}:{' '.join(args) if args else '<default>'}"
    try:
        lock = acquire_build_lock(None, owner, block=wait)
    except BuildLockBusyError as exc:
        meta = exc.metadata or {}
        owner_msg = meta.get("owner", "unknown")
        pid_msg = meta.get("pid", "unknown")
        print(
            f"[locked-lake-build] another build already holds {exc.lock_path} "
            f"(owner={owner_msg}, pid={pid_msg}); refusing to start a concurrent build",
            file=sys.stderr,
            flush=True,
        )
        return 2

    cmd = ["lake", "build", *args]
    print(f"[locked-lake-build] acquired {lock.lock_path}", flush=True)
    print(f"[locked-lake-build] running: {' '.join(cmd)}", flush=True)
    try:
        proc = subprocess.run(cmd)
        return proc.returncode
    finally:
        lock.release()
        print(f"[locked-lake-build] released {lock.lock_path}", flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
