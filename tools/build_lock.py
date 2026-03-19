#!/usr/bin/env python3
from __future__ import annotations

import fcntl
import json
import os
import time
from pathlib import Path


DEFAULT_BUILD_LOCK_PATH = Path("/tmp/info-geometry-build.lock")


class BuildLock:
    def __init__(self, lock_path: Path, owner: str) -> None:
        self.lock_path = lock_path
        self.owner = owner
        self._handle: object | None = None

    def acquire(self) -> "BuildLock":
        self.lock_path.parent.mkdir(parents=True, exist_ok=True)
        handle = self.lock_path.open("a+", encoding="utf-8")
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        handle.seek(0)
        handle.truncate(0)
        handle.write(
            json.dumps(
                {
                    "owner": self.owner,
                    "pid": os.getpid(),
                    "acquiredAt": time.time(),
                },
                ensure_ascii=False,
            )
            + "\n"
        )
        handle.flush()
        self._handle = handle
        return self

    def release(self) -> None:
        if self._handle is None:
            return
        handle = self._handle
        self._handle = None
        try:
            handle.seek(0)
            handle.truncate(0)
            handle.flush()
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        finally:
            handle.close()

    def __enter__(self) -> "BuildLock":
        return self.acquire()

    def __exit__(self, exc_type, exc, tb) -> None:
        self.release()


def acquire_build_lock(lock_path: Path | None, owner: str) -> BuildLock:
    return BuildLock(lock_path or DEFAULT_BUILD_LOCK_PATH, owner).acquire()
