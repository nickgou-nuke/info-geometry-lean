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
from tools.infra.build import _validate_lake_workspace_integrity
from tools.pathing import repo_root


def build_lean_command(
    lake: str, source: Path, lean_args: list[str], *, run_script: bool = False
) -> list[str]:
    """Build the exact serialized Lake/Lean command, including script mode."""
    command = [lake, "env", "lean"]
    if run_script:
        command.append("--run")
    return [*command, str(source), *lean_args]


def execute_locked_lean(
    source: str | Path,
    lean_args: list[str] | None = None,
    *,
    lake: str = "lake",
    root: Path | None = None,
    wait: bool = True,
    run_script: bool = False,
    **run_kwargs,
) -> subprocess.CompletedProcess:
    """Run Lean under the shared build lock; timeout kills the direct Lake child."""
    root = (root or repo_root()).resolve()
    integrity_error = _validate_lake_workspace_integrity(root)
    if integrity_error is not None:
        raise RuntimeError(integrity_error)
    source_path = Path(source)
    if source_path.is_absolute():
        try:
            source_path = source_path.resolve().relative_to(root)
        except ValueError as exc:
            raise ValueError("Lean file must be inside the repository") from exc
    if source_path.suffix != ".lean" or not (root / source_path).is_file():
        raise ValueError(f"Lean file not found: {source_path}")

    owner = f"locked-lean:{os.getpid()}:{source_path}"
    lock = acquire_build_lock(None, owner, block=wait)
    try:
        command = build_lean_command(lake, source_path, lean_args or [], run_script=run_script)
        return subprocess.run(command, cwd=root, check=False, **run_kwargs)
    finally:
        lock.release()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run lake env lean under the shared build lock.")
    parser.add_argument("--wait-for-build-lock", action="store_true")
    parser.add_argument("--no-wait-for-build-lock", dest="wait", action="store_false")
    parser.set_defaults(wait=True)
    parser.add_argument("--run", action="store_true", help="Execute the source file as a Lean script.")
    parser.add_argument("--lake", default="lake", help="Lake executable path.")
    parser.add_argument("file", help="Lean source file to elaborate")
    parser.add_argument("lean_args", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)

    try:
        source = Path(args.file)
        if source.is_absolute():
            source = source.resolve().relative_to(repo_root().resolve())
        command = build_lean_command(args.lake, source, args.lean_args, run_script=args.run)
        print(f"[locked-lean] executing: {' '.join(command)}", flush=True)
        return execute_locked_lean(
            source, args.lean_args, lake=args.lake, wait=args.wait, run_script=args.run
        ).returncode
    except BuildLockBusyError as exc:
        print(f"[locked-lean] build lock is held at {exc.lock_path}", file=sys.stderr)
        return 2
    except OSError as exc:
        print(f"[locked-lean] could not acquire build lock: {exc}", file=sys.stderr)
        return 126
    except (RuntimeError, ValueError) as exc:
        print(f"[locked-lean] {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
