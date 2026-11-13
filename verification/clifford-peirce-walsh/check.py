#!/usr/bin/env python3
"""Check the exact repository sources with pinned dependencies and the shared lock.

This focused project does not certify the root project's optional dependencies
or its unrelated default targets. Pass Lake arguments, for example:
    python3 verification/clifford-peirce-walsh/check.py build MODULE
    python3 verification/clifford-peirce-walsh/check.py env lean ABSOLUTE_FILE
"""

from __future__ import annotations

import os
import json
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


def validate_pins() -> None:
    if (PROJECT / "lean-toolchain").read_bytes() != (ROOT / "lean-toolchain").read_bytes():
        raise RuntimeError("selected and root toolchains differ")
    root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    expected = {p["name"]: p["rev"] for p in root_manifest["packages"] if p["type"] == "git"}
    selected = json.loads((PROJECT / "lake-manifest.json").read_text())
    for package in selected["packages"]:
        name = package["name"]
        if package["type"] == "git" and package["rev"] != expected[name]:
            raise RuntimeError(f"selected dependency pin differs for {name}")
        directory = ROOT / ".lake" / "packages" / name
        actual = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True
        ).strip()
        if actual != expected[name]:
            raise RuntimeError(f"dependency checkout revision differs for {name}")
        dirty = subprocess.check_output(
            ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"],
            text=True,
        )
        if dirty:
            raise RuntimeError(f"tracked dependency source is modified: {name}")


def main() -> int:
    for directory in (ROOT, PROJECT):
        error = _validate_lake_workspace_integrity(directory)
        if error:
            print(error, file=sys.stderr)
            return 2
    args = sys.argv[1:] or ["build", "InfoGeometry.Canonical.CliffordPeirceWalshAudit"]
    command = ["lake", "-d", str(PROJECT), *args]
    lock = acquire_build_lock(None, f"clifford-peirce-walsh:{os.getpid()}", block=True)
    process = None
    try:
        validate_pins()
        print("[clifford-peirce-walsh] " + " ".join(command), flush=True)
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
