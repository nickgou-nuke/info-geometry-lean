#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Sequence

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.build import run_locked_lake_build
else:
    from tools.infra.build import run_locked_lake_build


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    """Parse wrapper options separately from arguments intended for Lake.

    Lake options must follow `--` (for example, `... -- -R`). This prevents
    argparse from consuming Lake flags and makes the executed argv auditable.
    """
    raw = list(sys.argv[1:] if argv is None else argv)
    if "--" in raw:
        separator = raw.index("--")
        wrapper_argv, lake_argv = raw[:separator], raw[separator + 1:]
    else:
        wrapper_argv, lake_argv = raw, []

    parser = argparse.ArgumentParser(
        description=(
            "Run `lake build` under the repository-wide build lock. "
            "Pass Lake options after `--`; positional arguments are build targets."
        )
    )
    parser.add_argument(
        "--wait-for-build-lock",
        action="store_true",
        help="Block until the shared build lock is available instead of failing immediately.",
    )
    parser.add_argument(
        "--wfail",
        action="store_true",
        help="Pass `--wfail` to `lake build` so warnings are treated as errors.",
    )
    parser.add_argument(
        "--all-default-targets",
        action="store_true",
        help=(
            "Run both the canonical lean/ and isolated src/ Lake workspaces with no target, "
            "compiling every @[default_target] in each."
        ),
    )
    parser.add_argument(
        "--source-lane",
        action="store_true",
        help="Build explicit targets from src/ using lakefile.src.lean and isolated outputs.",
    )
    parser.add_argument(
        "--changed",
        action="store_true",
        help=(
            "Build only changed Lean owner modules via build_changed_lean.py. "
            "This is the safe default for development scripts."
        ),
    )
    parser.add_argument(
        "--staged",
        action="store_true",
        help=(
            "Build only git-staged changed Lean owner modules via build_changed_lean.py --staged-only."
        ),
    )
    parser.add_argument(
        "--all-changed",
        action="store_true",
        help="Allow building all changed modules even in a large multi-agent dirty worktree.",
    )
    parser.add_argument(
        "targets", nargs="*",
        help=(
            "Lake build targets (or .lean file paths under lean/, tests/, proofs/, src/). "
            "With no target, changed Lean owner modules are built incrementally; use "
            "--all-default-targets for an explicit Lake default-target build."
        ),
    )
    args = parser.parse_args(wrapper_argv)
    args.lake_args = lake_argv
    return args


def normalize_lake_target(raw: str, *, source_lane: bool = False) -> str:
    """Convert a repo-relative `.lean` path under lean/, tests/, proofs/, or src/ to a Lake module name."""
    norm = raw.replace("\\", "/")
    while norm.startswith("./"):
        norm = norm[2:]
    if not norm.endswith(".lean"):
        return raw
    if source_lane:
        if norm.startswith("src/"):
            return norm[len("src/") : -len(".lean")].replace("/", ".")
        return raw
    if norm == "lean/InfoGeometry.lean":
        return "InfoGeometry"
    if norm == "lean/GrandUnifiedNoncommutativeOperatorSynthesis.lean":
        return "GrandUnifiedNoncommutativeOperatorSynthesis"
    if norm.startswith("lean/"):
        return norm[len("lean/") : -len(".lean")].replace("/", ".")
    if norm.startswith("tests/"):
        return norm[len("tests/") : -len(".lean")].replace("/", ".")
    if norm.startswith("proofs/"):
        return "proofs." + norm[len("proofs/") : -len(".lean")].replace("/", ".")
    return raw


def main() -> int:
    args = parse_args()
    if args.all_default_targets and (args.targets or args.changed or args.staged or args.source_lane or args.all_changed):
        print(
            "--all-default-targets cannot be combined with targets, --changed, --staged, --source-lane, or --all-changed",
            file=sys.stderr,
        )
        return 2
    if args.all_changed and args.targets:
        print("--all-changed cannot be combined with positional targets", file=sys.stderr)
        return 2
    if (args.changed or args.staged) and args.targets:
        root = Path(__file__).resolve().parents[2]
        invalid = [
            t for t in args.targets
            if not ("/" in t or "\\" in t or t.endswith(".lean") or (root / t).exists())
        ]
        if invalid:
            print(
                "--changed/--staged only accept file or directory paths, not module names: "
                + ", ".join(invalid),
                file=sys.stderr,
            )
            return 2
    targets = [] if args.all_default_targets else [
        normalize_lake_target(t, source_lane=args.source_lane) for t in args.targets
    ]
    # No-target invocations are development builds: resolve changed owners
    # instead of silently expanding to the repository umbrella target.
    if args.source_lane and not args.targets:
        print("--source-lane requires one or more explicit module targets", file=sys.stderr)
        return 2
    if args.staged or args.changed or args.all_changed or (not args.targets and not args.all_default_targets):
        import subprocess
        changed = Path(__file__).with_name("build_changed_lean.py")
        cmd = [sys.executable, str(changed)]
        if args.staged:
            cmd.append("--staged-only")
        if args.all_changed:
            cmd.append("--all-changed")
        if args.wait_for_build_lock:
            cmd.append("--wait-for-build-lock")
        if args.lake_args:
            print("--changed/--staged does not accept positional Lake options; use wrapper flags", file=sys.stderr)
            return 2
        if args.wfail:
            cmd.append("--wfail")
        if args.targets:
            cmd.extend(args.targets)
        return subprocess.run(cmd, cwd=Path(__file__).resolve().parents[2]).returncode
    return run_locked_lake_build(
        [*targets, *args.lake_args],
        wait_for_lock=args.wait_for_build_lock,
        wfail=args.wfail,
        include_src_default=args.all_default_targets,
        lakefile="lakefile.src.lean" if args.source_lane else None,
    )


if __name__ == "__main__":
    raise SystemExit(main())
