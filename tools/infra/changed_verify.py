#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.build import run_locked_lake_build
    from tools.infra.build_changed_lean import changed_paths, collect_modules
    from tools.pathing import repo_root
else:
    from tools.infra.build import run_locked_lake_build
    from tools.infra.build_changed_lean import changed_paths, collect_modules
    from tools.pathing import repo_root


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Verify changed Lean work with one compressed lane: narrow file gates, "
            "incremental owner-module builds, and an optional umbrella build."
        )
    )
    parser.add_argument("--dry-run", action="store_true", help="Print the resolved commands without executing them.")
    parser.add_argument(
        "--prefix",
        default="InfoGeometry.",
        help="Optional module-prefix filter for the owner build (default: InfoGeometry.). Use empty string to disable.",
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
        "--allow-umbrella",
        action="store_true",
        help="Allow changed owner modules ending in `.All` during the incremental owner build.",
    )
    parser.add_argument(
        "--wait-for-build-lock",
        action="store_true",
        default=True,
        help="Block until the shared build lock is available for owner or umbrella builds (default: true).",
    )
    parser.add_argument(
        "--no-wait-for-build-lock",
        dest="wait_for_build_lock",
        action="store_false",
        help="Fail fast if the build lock is currently held.",
    )
    parser.add_argument(
        "--skip-file-gates",
        action="store_true",
        help="Skip `lake env lean <file>` gates and run only the owner and optional umbrella builds.",
    )
    parser.add_argument(
        "--skip-owner-build",
        action="store_true",
        help="Skip the incremental owner-module build and run only file gates plus any optional umbrella build.",
    )
    parser.add_argument(
        "--umbrella",
        choices=["none", "canonical", "all", "audit"],
        default="none",
        help="Optional umbrella target to run after the changed owner build.",
    )
    parser.add_argument(
        "--strict-check",
        action="store_true",
        help="Run `scripts/quality/strict-check.sh` after the Lean build lane.",
    )
    return parser.parse_args()


def changed_lean_files(root: Path, *, include_untracked: bool) -> list[Path]:
    out: list[Path] = []
    for path in sorted(changed_paths(root, include_untracked=include_untracked)):
        if path.suffix != ".lean":
            continue
        if not path.exists():
            continue
        try:
            rel = path.resolve().relative_to(root.resolve())
        except ValueError:
            continue
        if rel.parts and rel.parts[0] == "lean":
            out.append(path.resolve())
    return out


def run_file_gate(root: Path, path: Path) -> int:
    rel = path.resolve().relative_to(root.resolve())
    completed = subprocess.run(["lake", "env", "lean", str(rel)], cwd=root, check=False)
    return completed.returncode


def umbrella_target(name: str) -> str | None:
    mapping = {
        "canonical": "InfoGeometry.Canonical.All",
        "all": "InfoGeometry.All",
        "audit": "InfoGeometry.Audit",
    }
    return mapping.get(name)


def main() -> int:
    args = parse_args()
    root = repo_root()
    prefix = args.prefix if args.prefix else None
    files = changed_lean_files(root, include_untracked=args.include_untracked)
    modules = collect_modules(
        root,
        include_untracked=args.include_untracked,
        allow_umbrella=args.allow_umbrella,
        prefix=prefix,
    )
    umbrella = umbrella_target(args.umbrella)

    print("[changed-verify] compressed Lean verification lane", flush=True)
    print(f"[changed-verify] changed Lean files: {len(files)}", flush=True)
    for path in files:
        print(f"  - {path.relative_to(root)}", flush=True)
    print(f"[changed-verify] owner modules: {len(modules)}", flush=True)
    for mod in modules:
        print(f"  - {mod}", flush=True)
    if umbrella:
        print(f"[changed-verify] umbrella target: {umbrella}", flush=True)
    if args.strict_check:
        print("[changed-verify] strict check enabled", flush=True)

    if args.dry_run:
        if not args.skip_file_gates:
            for path in files:
                rel = path.relative_to(root)
                print(f"[changed-verify] would run: lake env lean {rel}", flush=True)
        if not args.skip_owner_build and modules:
            print("[changed-verify] would run locked owner build", flush=True)
        if umbrella:
            print(f"[changed-verify] would run locked umbrella build: {umbrella}", flush=True)
        if args.strict_check:
            print("[changed-verify] would run: bash scripts/quality/strict-check.sh", flush=True)
        print("[changed-verify] dry-run only; no commands executed", flush=True)
        return 0

    if not args.skip_file_gates:
        for path in files:
            rel = path.relative_to(root)
            print(f"[changed-verify] file gate: lake env lean {rel}", flush=True)
            code = run_file_gate(root, path)
            if code != 0:
                return code

    if not args.skip_owner_build and modules:
        code = run_locked_lake_build(modules, wait_for_lock=args.wait_for_build_lock)
        if code != 0:
            return code

    if umbrella:
        code = run_locked_lake_build([umbrella], wait_for_lock=args.wait_for_build_lock)
        if code != 0:
            return code

    if args.strict_check:
        completed = subprocess.run(["bash", "scripts/quality/strict-check.sh"], cwd=root, check=False)
        if completed.returncode != 0:
            return completed.returncode

    print("[changed-verify] completed successfully", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
