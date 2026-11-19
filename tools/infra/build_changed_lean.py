#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import re
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
    staged_only: bool = False,
) -> set[Path]:
    # Collect working-tree + staged tracked changes against the selected baseline,
    # or only staged changes when staged_only=True.
    base = "HEAD"
    if base_ref:
        base = _base_ref_commit(root, base_ref)

    out: set[Path] = set()
    if staged_only:
        try:
            out.update((root / rel).resolve() for rel in run_git(["diff", "--cached", "--name-only", base], cwd=root))
        except subprocess.CalledProcessError:
            out.update((root / rel).resolve() for rel in run_git(["diff", "--cached", "--name-only", "HEAD"], cwd=root))
        return out

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


def path_to_module(
    root: Path, path: Path, *, source_root: str = "lean"
) -> str | None:
    try:
        rel = path.resolve().relative_to(root.resolve())
    except ValueError:
        return None
    parts = rel.parts
    if len(parts) < 2:
        return None
    if parts[0] == source_root and rel.suffix == ".lean":
        stem_parts = list(parts[1:])
    elif source_root == "lean" and parts[0] == "InfoGeometry" and rel.suffix == ".lean":
        stem_parts = list(parts)
    else:
        return None
    stem_parts[-1] = Path(stem_parts[-1]).stem
    return ".".join(stem_parts)


_IMPORT_LINE_RE = re.compile(r"^(?:public\s+|meta\s+|private\s+)?import\s+\S+")


def _strip_lean_comments(text: str) -> str:
    """Strip nested Lean block comments and line comments outside strings."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line = False
    in_string = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            i += 1
            continue
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
            i += 1
            continue
        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
            continue
        if ch == "-" and nxt == "-":
            in_line = True
            i += 2
            continue
        if ch == '"':
            in_string = True
        out.append(ch)
        i += 1
    return "".join(out)


def is_import_only_umbrella(path: Path) -> bool:
    """Return True when a Lean file contains at least one import and nothing else."""
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return False
    stripped = _strip_lean_comments(text)
    non_empty = [ln.strip() for ln in stripped.splitlines() if ln.strip()]
    return bool(non_empty) and all(_IMPORT_LINE_RE.match(ln) for ln in non_empty)


def collect_modules(
    root: Path,
    *,
    include_untracked: bool,
    allow_umbrella: bool,
    prefix: str | None,
    base_ref: str | None = None,
    source_root: str = "lean",
    scope_paths: Iterable[Path] | None = None,
    staged_only: bool = False,
) -> list[str]:
    resolved_scopes = [
        (root / sp).resolve() if not sp.is_absolute() else sp.resolve()
        for sp in (scope_paths or ())
    ]
    modules: set[str] = set()
    for path in changed_paths(
        root,
        include_untracked=include_untracked,
        base_ref=base_ref,
        staged_only=staged_only,
    ):
        if resolved_scopes and not any(path == sp or sp in path.parents for sp in resolved_scopes):
            continue
        if not path.exists():
            continue
        mod = path_to_module(root, path, source_root=source_root)
        if mod is None:
            continue
        # Aggregate imports intentionally traverse the full lane. Keep them out
        # of the default changed-owner path; they remain available through an
        # explicit target/build after owner repairs are complete.
        if (not allow_umbrella) and (
            mod.rsplit(".", 1)[-1] in {"All", "AllExhaustive"}
            or is_import_only_umbrella(path)
        ):
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
        "paths",
        nargs="*",
        default=[],
        help="Optional file or directory paths to scope changed-module selection.",
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
        "--source-root",
        choices=("auto", "lean", "src", "both"),
        default="auto",
        help=(
            "Source tree(s) whose changed module identities should be selected. "
            "`auto` (default) builds `lean` unless explicit scope paths under `src/` are passed."
        ),
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
    parser.add_argument(
        "--wfail",
        action="store_true",
        help="Pass --wfail to Lake for the selected changed-owner modules.",
    )
    parser.add_argument(
        "--staged-only",
        action="store_true",
        help="Collect only git-staged changed Lean files (ignores unstaged/untracked noise).",
    )
    parser.add_argument(
        "--all-changed",
        action="store_true",
        help="Allow unscoped changed-module builds even when many dirty files exist in a shared worktree.",
    )
    parser.add_argument(
        "--max-unscoped-modules",
        type=int,
        default=int(os.environ.get("INFOGEOMETRY_MAX_UNSCOPED_CHANGED", "25")),
        help="Abort unscoped builds when more than this many changed modules are found unless --all-changed is set (default: 25, 0 disables).",
    )
    return parser.parse_args()


def _selected_lanes(root: Path, source_root: str, scope_paths: Iterable[Path] | None) -> tuple[str, ...]:
    if source_root == "both":
        return ("lean", "src")
    if source_root in ("lean", "src"):
        return (source_root,)
    has_src_scope = False
    has_non_src_scope = False
    resolved_root = root.resolve()
    for raw_path in scope_paths or ():
        resolved = (resolved_root / raw_path).resolve() if not raw_path.is_absolute() else raw_path.resolve()
        try:
            rel = resolved.relative_to(resolved_root)
        except ValueError:
            continue
        if rel.parts and rel.parts[0] == "src":
            has_src_scope = True
        else:
            has_non_src_scope = True
    if has_src_scope and has_non_src_scope:
        return ("lean", "src")
    if has_src_scope:
        return ("src",)
    return ("lean",)


def main() -> int:
    args = parse_args()
    root = repo_root()
    prefix = args.prefix if args.prefix else None
    scope_paths = [Path(p) for p in args.paths] if args.paths else None
    lanes = _selected_lanes(root, args.source_root, scope_paths)
    modules_by_lane = {
        lane: collect_modules(
            root,
            include_untracked=args.include_untracked,
            allow_umbrella=args.allow_umbrella,
            prefix=prefix,
            base_ref=args.base_ref,
            source_root=lane,
            scope_paths=scope_paths,
            staged_only=args.staged_only,
        )
        for lane in lanes
    }
    if not any(modules_by_lane.values()):
        print("[build-changed-lean] no changed Lean owner modules detected", flush=True)
        return 0

    for lane, modules in modules_by_lane.items():
        print(f"[build-changed-lean] {lane} modules ({len(modules)}):", flush=True)
        for mod in modules:
            print(f"  - {mod}", flush=True)

    if args.dry_run:
        print("[build-changed-lean] dry-run only; no build executed", flush=True)
        return 0

    total_modules = sum(len(mods) for mods in modules_by_lane.values())
    if (
        not args.paths
        and not args.all_changed
        and args.max_unscoped_modules > 0
        and total_modules > args.max_unscoped_modules
    ):
        print(
            f"[build-changed-lean] refusing unscoped build of {total_modules} changed modules "
            f"(limit={args.max_unscoped_modules}) in a shared dirty worktree; "
            "pass explicit target paths/modules, use `--staged-only` if scoped, or pass `--all-changed`.",
            file=sys.stderr,
            flush=True,
        )
        return 2

    for lane, modules in modules_by_lane.items():
        if not modules:
            continue
        status = run_locked_lake_build(
            modules,
            wait_for_lock=args.wait_for_build_lock,
            wfail=args.wfail,
            lakefile="lakefile.src.lean" if lane == "src" else None,
        )
        if status != 0:
            return status
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
