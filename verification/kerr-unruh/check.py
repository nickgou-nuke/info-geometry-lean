#!/usr/bin/env python3
"""Run the focused single-mode Fermi/Kerr package under the repository's shared build lock."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[1]
STRICT_SOURCES = (
    "lean/InfoGeometry/Clifford/FermiDiracAnalytic.lean",
    "lean/InfoGeometry/Lie/LorentzCartanKernel.lean",
    "lean/InfoGeometry/Canonical/KerrUnruhFermionicHorizonBridge.lean",
    "lean/InfoGeometry/Canonical/KerrUnruhFermionicHorizonAudit.lean",
)
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
    prefix = ["lake", "-d", str(PROJECT)]
    strict_commands = [
        prefix + ["env", "lean", "-DwarningAsError=true", source]
        for source in STRICT_SOURCES
    ]
    if sys.argv[1:] == ["--validate"]:
        # The library config makes the build itself strict for every owner.
        # Re-elaborate the audit to capture fresh axiom output after that build.
        commands = [prefix + ["build"], strict_commands[-1]]
    elif sys.argv[1:] == ["--strict-sources"]:
        commands = strict_commands
    else:
        commands = [prefix + (sys.argv[1:] or ["build"])]
    print("[kerr-unruh] waiting for the shared build lock", flush=True)
    lock = acquire_build_lock(None, f"kerr-unruh:{os.getpid()}", block=True)
    process = None
    try:
        for command in commands:
            print("[kerr-unruh] " + " ".join(command), flush=True)
            process = subprocess.Popen(command, cwd=ROOT, start_new_session=(os.name == "posix"))
            try:
                result = process.wait()
            except KeyboardInterrupt:
                _interrupt_child_and_wait(process)
                return 130
            if result:
                return result
        return 0
    finally:
        if process is not None and process.poll() is None:
            _interrupt_child_and_wait(process)
        lock.release()


if __name__ == "__main__":
    raise SystemExit(main())
