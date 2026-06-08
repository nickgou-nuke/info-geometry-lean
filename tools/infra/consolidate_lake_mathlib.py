#!/usr/bin/env python3
"""Consolidate duplicate Lake mathlib package checkouts.

Lake packages are tied to exact git revisions and Lean toolchains.  This tool
therefore deduplicates by mathlib commit, not by package name alone.
"""

from __future__ import annotations

import argparse
import os
import shutil
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


def relink(source: Path, target: Path, *, dry_run: bool, force: bool) -> None:
    if source.resolve() == target.resolve():
        print(f"keep    {source} -> shared target")
        return
    if source.is_symlink():
        print(f"link    {source} -> {target}")
        if not dry_run:
            source.unlink()
            source.symlink_to(target, target_is_directory=True)
        return
    if not force:
        info = checkout_info(source)
        if info and info.dirty:
            raise RuntimeError(f"refusing dirty mathlib checkout without --force: {source}")
    print(f"delete  {source}")
    print(f"link    {source} -> {target}")
    if not dry_run:
        shutil.rmtree(source)
        source.symlink_to(target, target_is_directory=True)


def ensure_shared_target(
    checkouts: list[MathlibCheckout],
    shared_root: Path,
    *,
    dry_run: bool,
    force: bool,
) -> tuple[Path, Path | None]:
    rev = checkouts[0].rev
    target = shared_root / rev
    if target.exists():
        target_info = checkout_info(target)
        if target_info is None or target_info.rev != rev:
            raise RuntimeError(f"shared target exists but is not mathlib rev {rev}: {target}")
        print(f"target  {target} already exists")
        return target, None

    canonical = max((c for c in checkouts if not c.is_symlink), key=lambda c: c.size_bytes, default=None)
    if canonical is None:
        raise RuntimeError(f"no physical checkout available for rev {rev}")
    if canonical.dirty and not force:
        raise RuntimeError(f"refusing dirty canonical checkout without --force: {canonical.path}")

    print(f"move    {canonical.path} -> {target}")
    print(f"link    {canonical.path} -> {target}")
    if not dry_run:
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(canonical.path), str(target))
        canonical.path.symlink_to(target, target_is_directory=True)
    return target, canonical.path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "roots",
        nargs="*",
        type=Path,
        default=[Path("/home/goutev/repos")],
        help="roots to scan for .lake/packages/mathlib",
    )
    parser.add_argument(
        "--shared-root",
        type=Path,
        default=Path.home() / ".cache" / "lake-shared" / "mathlib",
        help="central storage root, keyed by mathlib git commit",
    )
    parser.add_argument("--apply", action="store_true", help="perform changes; default is dry-run")
    parser.add_argument("--force", action="store_true", help="allow tracked local modifications in mathlib")
    args = parser.parse_args()

    checkouts = [info for path in discover_mathlibs(args.roots) if (info := checkout_info(path)) is not None]
    by_rev: dict[str, list[MathlibCheckout]] = {}
    for checkout in checkouts:
        by_rev.setdefault(checkout.rev, []).append(checkout)

    dry_run = not args.apply
    mode = "apply" if args.apply else "dry-run"
    print(f"mode={mode}")
    print(f"shared_root={args.shared_root}")
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
        if len(group) <= 1 and not args.apply:
            continue
        target, moved_canonical = ensure_shared_target(group, args.shared_root, dry_run=dry_run, force=args.force)
        for checkout in group:
            if moved_canonical is not None and checkout.path == moved_canonical:
                continue
            relink(checkout.path, target, dry_run=dry_run, force=args.force)

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"Error: {exc}", file=sys.stderr)
        raise SystemExit(1)
