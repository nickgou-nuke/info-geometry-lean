#!/usr/bin/env python3
"""Audit duplicate Lake mathlib checkouts without changing them.

Lake checkouts may contain compiled oleans, untracked cache data, or local
work.  Moving or deleting one and replacing it with a symlink can therefore
break an otherwise valid project.  This command is deliberately read-only;
share a checkout through an explicit Lake path dependency instead.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


@dataclass(frozen=True)
class MathlibCheckout:
    path: Path
    rev: str
    size_bytes: int
    dirty: bool
    is_symlink: bool


def run(cmd: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, check=True, text=True, capture_output=True)


def git_output(path: Path, args: list[str]) -> str:
    return run(["git", "-C", str(path), *args]).stdout.strip()


def dir_size(path: Path) -> int:
    total = 0
    for root, dirs, files in os.walk(path):
        dirs[:] = [d for d in dirs if d not in {".git"}]
        for file_name in files:
            file_path = Path(root) / file_name
            try:
                total += file_path.stat().st_size
            except OSError:
                pass
    return total


def discover_mathlibs(roots: list[Path]) -> list[Path]:
    found: list[Path] = []
    for root in roots:
        if not root.exists():
            continue
        for path in root.rglob(".lake/packages/mathlib"):
            if path.is_dir() or path.is_symlink():
                found.append(path)
    return sorted(set(found))


def checkout_info(path: Path) -> MathlibCheckout | None:
    try:
        rev = git_output(path, ["rev-parse", "HEAD"])
    except subprocess.CalledProcessError:
        return None
    try:
        dirty = bool(git_output(path, ["status", "--porcelain", "--untracked-files=no"]))
    except subprocess.CalledProcessError:
        dirty = True
    try:
        size = dir_size(path)
    except OSError:
        size = 0
    return MathlibCheckout(path=path, rev=rev, size_bytes=size, dirty=dirty, is_symlink=path.is_symlink())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "roots",
        nargs="*",
        type=Path,
        default=[Path("/home/goutev/repos")],
        help="roots to scan for .lake/packages/mathlib",
    )
    args = parser.parse_args()

    checkouts = [info for path in discover_mathlibs(args.roots) if (info := checkout_info(path)) is not None]
    by_rev: dict[str, list[MathlibCheckout]] = {}
    for checkout in checkouts:
        by_rev.setdefault(checkout.rev, []).append(checkout)

    print("mode=read-only-audit")
    print("policy=preserve-checkouts-and-build-artifacts; create-no-symlinks")
    print(f"timestamp={datetime.now(timezone.utc).isoformat()}")

    for rev, group in sorted(by_rev.items()):
        print()
        print(f"rev={rev} count={len(group)}")
        for checkout in sorted(group, key=lambda c: str(c.path)):
            size_gib = checkout.size_bytes / (1024**3)
            markers = []
            if checkout.dirty:
                markers.append("dirty")
            if checkout.is_symlink:
                markers.append("symlink")
            suffix = f" ({', '.join(markers)})" if markers else ""
            print(f"  {size_gib:7.2f} GiB  {checkout.path}{suffix}")
        if len(group) <= 1:
            continue
        print("  action  none (use an explicit Lake path dependency if sharing is intended)")

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"Error: {exc}", file=sys.stderr)
        raise SystemExit(1)
