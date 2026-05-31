#!/usr/bin/env python3
"""Require audited paths to be committed, clean, and optionally pushed."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


def git(args: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], text=True, capture_output=True, check=check)


def tracked_or_untracked_status(paths: list[str]) -> list[str]:
    out = git(["status", "--porcelain=v1", "--untracked-files=all", "--", *paths]).stdout
    return [line for line in out.splitlines() if line.strip()]


def lean_status_lines(lines: list[str]) -> list[str]:
    selected: list[str] = []
    for line in lines:
        path = line[3:] if len(line) > 3 else ""
        if path.endswith(".lean") or "/lean/" in path or path.startswith("lean/"):
            selected.append(line)
    return selected


def upstream_ref() -> str | None:
    proc = git(["rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{u}"], check=False)
    if proc.returncode != 0:
        return None
    return proc.stdout.strip()


def unpushed_count(upstream: str) -> int:
    out = git(["rev-list", "--left-right", "--count", f"{upstream}...HEAD"]).stdout.split()
    if len(out) != 2:
        return 0
    return int(out[1])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="*", default=["lean"])
    ap.add_argument("--require-pushed", action="store_true")
    ap.add_argument("--all-files", action="store_true", help="check every dirty path, not only Lean paths")
    args = ap.parse_args()

    lines = tracked_or_untracked_status(args.paths)
    dirty = lines if args.all_files else lean_status_lines(lines)
    failures: list[str] = []

    if dirty:
        failures.append("uncommitted audited files:")
        failures.extend(f"  {line}" for line in dirty)

    if args.require_pushed:
        upstream = upstream_ref()
        if upstream is None:
            failures.append("no upstream branch configured for pushed-baseline verification")
        else:
            ahead = unpushed_count(upstream)
            if ahead:
                failures.append(f"HEAD has {ahead} unpushed commit(s) relative to {upstream}")

    if failures:
        print("committed_baseline_gate: FAIL")
        for failure in failures:
            print(f"  - {failure}" if not failure.startswith("  ") else failure)
        return 1

    checked = ", ".join(args.paths) if args.paths else "lean"
    push_state = "pushed" if args.require_pushed else "push-not-required"
    print(f"committed_baseline_gate: ok ({checked}; {push_state})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
