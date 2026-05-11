#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path
from typing import Iterable

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.build import run_locked_lake_build
    from tools.pathing import repo_root
else:
    from tools.infra.build import run_locked_lake_build
    from tools.pathing import repo_root


def run_git(args: list[str], cwd: Path) -> list[str]:
    proc = subprocess.run(
        ["git", *args],
        cwd=cwd,
        check=True,
        capture_output=True,
        text=True,
    )
    return [line.strip() for line in proc.stdout.splitlines() if line.strip()]


def _base_ref_commit(root: Path, base_ref: str) -> str:
    try:
        merged = run_git(["merge-base", base_ref, "HEAD"], cwd=root)
    except subprocess.CalledProcessError:
        return "HEAD"
    return merged[0] if merged else base_ref


def changed_paths(
    root: Path,
    *,
    include_untracked: bool,
    base_ref: str | None = None,
) -> set[Path]:
    # Collect working-tree + staged tracked changes against the selected baseline.
    base = "HEAD"
    if base_ref:
        base = _base_ref_commit(root, base_ref)

    try:
        raw = run_git(["diff", "--name-only", base], cwd=root)
    except subprocess.CalledProcessError:
        if base_ref is None:
            raise
        raw = run_git(["diff", "--name-only", "HEAD"], cwd=root)
    out = {(root / rel).resolve() for rel in raw}
    # staged-only changes are not included by plain working-tree diff.
    try:
        out.update((root / rel).resolve() for rel in run_git(["diff", "--cached", "--name-only", base], cwd=root))
    except subprocess.CalledProcessError:
        pass

    if include_untracked:
        extra = run_git(["ls-files", "--others", "--exclude-standard"], cwd=root)
        out |= {(root / rel).resolve() for rel in extra}
    return out


def path_to_module(root: Path, path: Path) -> str | None:
    try:
        rel = path.resolve().relative_to(root.resolve())
    except ValueError:
        return None
    parts = rel.parts
    if len(parts) < 2:
        return None
    if parts[0] == "lean" and rel.suffix == ".lean":
        stem_parts = list(parts[1:])
    elif parts[0] == "InfoGeometry" and rel.suffix == ".lean":
        stem_parts = list(parts)
    else:
        return None
    stem_parts[-1] = Path(stem_parts[-1]).stem
    return ".".join(stem_parts)


def collect_modules(
    root: Path,
    *,
    include_untracked: bool,
    allow_umbrella: bool,
    prefix: str | None,
    base_ref: str | None,
) -> list[str]:
    modules: set[str] = set()
    for path in changed_paths(root, include_untracked=include_untracked, base_ref=base_ref):
        if not path.exists():
            continue
        mod = path_to_module(root, path)
        if mod is None:
            continue
        if (not allow_umbrella) and mod.endswith(".All"):
            continue
        if prefix and not mod.startswith(prefix):
            continue
        modules.add(mod)
    return sorted(modules)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Incremental Lean build helper: detect changed Lean files from git and "
            "build only their owner modules under the shared lock."
        )
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print selected modules and exit without building.",
    )
    parser.add_argument(
        "--prefix",
        default="InfoGeometry.",
        help="Optional module-prefix filter (default: InfoGeometry.). Use empty string to disable.",
    )
    parser.add_argument(
        "--include-untracked",
        action="store_true",
        default=True,
        help="Include untracked Lean files (default: true).",
    )
    parser.add_argument(
        "--no-include-untracked",
        dest="include_untracked",
        action="store_false",
        help="Ignore untracked Lean files.",
    )
    parser.add_argument(
        "--base-ref",
        default=None,
        help=(
            "Optional git ref to compare against when collecting changed Lean files. "
            "When set, uses merge-base(base_ref, HEAD) when available."
        ),
    )
    parser.add_argument(
        "--allow-umbrella",
        action="store_true",
        help="Allow umbrella modules such as `*.All` (disabled by default).",
    )
    parser.add_argument(
        "--wait-for-build-lock",
        action="store_true",
        default=True,
        help="Block until shared build lock is available (default: true).",
    )
    parser.add_argument(
        "--no-wait-for-build-lock",
        dest="wait_for_build_lock",
        action="store_false",
        help="Fail fast if the build lock is held.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()
    prefix = args.prefix if args.prefix else None
    modules = collect_modules(
        root,
        include_untracked=args.include_untracked,
        allow_umbrella=args.allow_umbrella,
        prefix=prefix,
        base_ref=args.base_ref,
    )
    if not modules:
        print("[build-changed-lean] no changed Lean owner modules detected", flush=True)
        return 0

    print(f"[build-changed-lean] modules ({len(modules)}):", flush=True)
    for mod in modules:
        print(f"  - {mod}", flush=True)

    if args.dry_run:
        print("[build-changed-lean] dry-run only; no build executed", flush=True)
        return 0

    return run_locked_lake_build(modules, wait_for_lock=args.wait_for_build_lock)


if __name__ == "__main__":
    raise SystemExit(main())
