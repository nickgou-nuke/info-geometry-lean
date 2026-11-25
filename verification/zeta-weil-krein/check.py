#!/usr/bin/env python3
"""Run the focused zeta/Weil--Krein package under the repository build lock."""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tomllib

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[1]
sys.path.insert(0, str(ROOT))

from tools.build_lock import acquire_build_lock  # noqa: E402
from tools.infra.build import (  # noqa: E402
    _interrupt_child_and_wait,
    _validate_lake_workspace_integrity,
)


def check_pins() -> None:
    if (ROOT / "lean-toolchain").read_bytes() != (PROJECT / "lean-toolchain").read_bytes():
        raise SystemExit("Focused and root toolchains differ")
    root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    focused_manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
    config = tomllib.loads((PROJECT / "lakefile.toml").read_text())
    if focused_manifest["name"] != config["name"]:
        raise SystemExit("Focused manifest and package names differ")
    root_pins = {
        p["name"]: (p["url"], p["rev"], p.get("subDir"))
        for p in root_manifest["packages"] if p["type"] == "git"
    }
    packages = focused_manifest["packages"]
    names = [p["name"] for p in packages]
    expected = {"mathlib", "plausible", "LeanSearchClient", "importGraph",
                "proofwidgets", "aesop", "Qq", "batteries", "Cli"}
    if len(names) != len(set(names)) or set(names) != expected:
        raise SystemExit("Unexpected focused dependency inventory")
    for package in packages:
        if package["type"] != "git":
            raise SystemExit("Focused dependencies must use pinned Git revisions")
        pin = (package["url"], package["rev"], package.get("subDir"))
        if root_pins.get(package["name"]) != pin:
            raise SystemExit(f"Focused dependency pin differs: {package['name']}")
    requirements = config.get("require", [])
    if len(requirements) != 1 or requirements[0]["name"] != "mathlib":
        raise SystemExit("Focused package must require exactly Mathlib")
    requirement = requirements[0]
    if (requirement.get("git"), requirement.get("rev"), requirement.get("subDir")) != root_pins["mathlib"]:
        raise SystemExit("Focused Mathlib requirement differs from the root pin")


def main() -> int:
    check_pins()
    for directory in (ROOT, PROJECT):
        error = _validate_lake_workspace_integrity(directory)
        if error:
            print(error, file=sys.stderr)
            return 2
    command = ["lake", "-d", str(PROJECT), *(sys.argv[1:] or ["build"])]
    print("[zeta-weil-krein] waiting for the shared build lock", flush=True)
    lock = acquire_build_lock(None, f"zeta-weil-krein:{os.getpid()}", block=True)
    process = None
    try:
        print("[zeta-weil-krein] " + " ".join(command), flush=True)
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
