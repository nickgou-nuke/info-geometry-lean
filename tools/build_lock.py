#!/usr/bin/env python3
from __future__ import annotations

import fcntl
import json
import os
import sys
import time
from pathlib import Path
from typing import Any


DEFAULT_BUILD_LOCK_PATH = Path("/tmp/info-geometry-build.lock")


class BuildLockBusyError(RuntimeError):
    def __init__(self, lock_path: Path, metadata: dict[str, Any] | None = None) -> None:
        self.lock_path = lock_path
        self.metadata = metadata or {}
        owner = self.metadata.get("owner")
        pid = self.metadata.get("pid")
        details = []
        if owner:
            details.append(f"owner={owner}")
        if pid:
            details.append(f"pid={pid}")
        suffix = f" ({', '.join(details)})" if details else ""
        super().__init__(f"build lock busy: {lock_path}{suffix}")


def read_lock_metadata(lock_path: Path) -> dict[str, Any] | None:
    try:
        raw = lock_path.read_text(encoding="utf-8").strip()
    except FileNotFoundError:
        return None
    except OSError:
        return None
    if not raw:
        return None
    try:
        data = json.loads(raw)
    except json.JSONDecodeError:
        return {"raw": raw}
    return data if isinstance(data, dict) else {"raw": data}


class BuildLock:
    def __init__(self, lock_path: Path, owner: str, *, block: bool = True) -> None:
        self.lock_path = lock_path
        self.owner = owner
        self.block = block
        self._handle: Any = None
        self._ref_count: int = 0

    def acquire(self) -> "BuildLock":
        if self._handle is not None:
            self._ref_count += 1
            return self
        self.lock_path.parent.mkdir(parents=True, exist_ok=True)
        handle = self.lock_path.open("a+", encoding="utf-8")
        flags = fcntl.LOCK_EX
        if not self.block:
            flags |= fcntl.LOCK_NB
        try:
            fcntl.flock(handle.fileno(), flags)
        except BlockingIOError as exc:
            meta = read_lock_metadata(self.lock_path) or {}
            handle.close()
            raise BuildLockBusyError(self.lock_path, meta) from exc
        except BaseException:
            handle.close()
            raise

        try:
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
        except BaseException:
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
            finally:
                handle.close()
            raise
        self._handle = handle
        self._ref_count = 1
        return self

    def release(self) -> None:
        if self._handle is None:
            return
        if self._ref_count > 1:
            self._ref_count -= 1
            return
        self._ref_count = 0
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

    def __exit__(self, exc_type: Any, exc: Any, tb: Any) -> None:
        self.release()


def acquire_build_lock(lock_path: Path | None, owner: str, *, block: bool = True) -> BuildLock:
    return BuildLock(lock_path or DEFAULT_BUILD_LOCK_PATH, owner, block=block).acquire()
