#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import repo_root
else:
    from tools.pathing import repo_root


DEFAULT_FRONTIER_JSON = "reports/dag/skynet-v2-frontier-reverse.json"
DEFAULT_RUNS_DIR = "reports/optimization-runs"
DEFAULT_WORKTREE_ROOT = "/tmp/info-geometry-autoopt"
DEFAULT_BRANCH_PREFIX = "auto-opt/dry-cycle-"
DEFAULT_MODULE = "InfoGeometry.Unstable.AutoOptCycle"
DEFAULT_REL_FILE = "lean/InfoGeometry/Unstable/AutoOptCycle.lean"


@dataclass
class CommandResult:
    argv: list[str]
    returncode: int
    stdout_path: str
    stderr_path: str


def now_utc_compact() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def run_capture(cmd: list[str], cwd: Path, stdout_path: Path, stderr_path: Path) -> CommandResult:
    stdout_path.parent.mkdir(parents=True, exist_ok=True)
    stderr_path.parent.mkdir(parents=True, exist_ok=True)
    with stdout_path.open("w", encoding="utf-8") as stdout_handle, stderr_path.open(
        "w", encoding="utf-8"
    ) as stderr_handle:
        proc = subprocess.run(cmd, cwd=cwd, stdout=stdout_handle, stderr=stderr_handle, text=True)
    return CommandResult(
        argv=cmd,
        returncode=proc.returncode,
        stdout_path=str(stdout_path),
        stderr_path=str(stderr_path),
    )


def run_text(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, check=True, capture_output=True, text=True)


def ensure_clean_tracked_tree(root: Path) -> None:
    proc = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=no"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    if proc.stdout.strip():
        raise SystemExit(
            "refusing to start optimization cycle with tracked local modifications.\n"
            "commit or stash them first."
        )


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Run one safe dry optimization cycle in an isolated git worktree. "
            "This runner does not call an LLM; it only materializes a quarantine file, "
            "runs a targeted build, and records a manifest."
        )
    )
    ap.add_argument(
        "--frontier-json",
        default=DEFAULT_FRONTIER_JSON,
        help="Trusted frontier JSON to consume.",
    )
    ap.add_argument(
        "--frontier-index",
        type=int,
        default=0,
        help="Index of the primary frontier item to target.",
    )
    ap.add_argument(
        "--top-k",
        type=int,
        default=5,
        help="Number of frontier items to embed into the quarantine context.",
    )
    ap.add_argument(
        "--runs-dir",
        default=DEFAULT_RUNS_DIR,
        help="Directory under the repo where run manifests/logs are written.",
    )
    ap.add_argument(
        "--worktree-root",
        default=DEFAULT_WORKTREE_ROOT,
        help="Root directory under which isolated worktrees are created.",
    )
    ap.add_argument(
        "--branch-prefix",
        default=DEFAULT_BRANCH_PREFIX,
        help="Prefix for generated dry-cycle branch names.",
    )
    ap.add_argument(
        "--module",
        default=DEFAULT_MODULE,
        help="Lean module name to build inside the isolated worktree.",
    )
    ap.add_argument(
        "--relative-file",
        default=DEFAULT_REL_FILE,
        help="Path of the quarantine file inside the worktree.",
    )
    ap.add_argument(
        "--cleanup-worktree",
        action="store_true",
        help="Remove the worktree after the targeted build completes.",
    )
    ap.add_argument(
        "--allow-dirty-tracked",
        action="store_true",
        help="Development override: allow the cycle to run even with tracked local modifications.",
    )
    return ap.parse_args()


def selected_frontier_rows(frontier_obj: dict[str, Any], frontier_index: int, top_k: int) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    frontier = frontier_obj.get("frontier", [])
    if not frontier:
        raise SystemExit("frontier JSON contains no frontier entries")
    if frontier_index < 0 or frontier_index >= len(frontier):
        raise SystemExit(f"--frontier-index {frontier_index} out of range for frontier of size {len(frontier)}")
    return frontier[frontier_index], frontier[:top_k]


def quoted_strings(xs: list[str]) -> str:
    if not xs:
        return "[]"
    inner = ", ".join(json.dumps(x) for x in xs)
    return f"[{inner}]"


def render_quarantine_file(run_id: str, frontier_path: Path, frontier_obj: dict[str, Any], chosen: dict[str, Any], top_rows: list[dict[str, Any]]) -> str:
    seed_names = [str(x) for x in frontier_obj.get("seedNames", [])]
    chosen_names = [str(x) for x in chosen.get("primaryProduces", [])]
    top_names: list[str] = []
    for row in top_rows:
        produces = [str(x) for x in row.get("primaryProduces", [])]
        top_names.extend(produces[:1] if produces else [str(row.get("stableId", ""))])
    return f"""import InfoGeometry.All
import InfoGeometry.KK.KasparovCycle

/-!
# InfoGeometry.Unstable.AutoOptCycle

Auto-generated dry optimization cycle context.

This file is intentionally report-only. It materializes the current frontier
selection in a compilable quarantine module without attempting theorem
generation.

Run id: `{run_id}`
Frontier source: `{frontier_path}`
-/

namespace InfoGeometry.Unstable.AutoOptCycle

def runId : String := {json.dumps(run_id)}

def frontierSource : String := {json.dumps(str(frontier_path))}

def walkMode : String := {json.dumps(str(frontier_obj.get("walk", "unknown")))}

def seedDeclarations : List String := {quoted_strings(seed_names)}

def selectedDeclarations : List String := {quoted_strings(chosen_names)}

def selectedStableId : String := {json.dumps(str(chosen.get("stableId", "")))}

def selectedSourceFile : String := {json.dumps(str(chosen.get("sourceFile", "")))}

def frontierContext : List String := {quoted_strings(top_names)}

end InfoGeometry.Unstable.AutoOptCycle
"""


def write_manifest(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_summary(path: Path, payload: dict[str, Any]) -> None:
    chosen = payload["chosenFrontier"]
    lines = [
        "# Optimization Cycle",
        "",
        f"- run id: `{payload['runId']}`",
        f"- git head: `{payload['gitHead']}`",
        f"- branch: `{payload['branchName']}`",
        f"- worktree: `{payload['worktreePath']}`",
        f"- frontier source: `{payload['frontierJson']}`",
        f"- walk: `{payload['walk']}`",
        f"- selected stable id: `{chosen.get('stableId', '')}`",
        f"- selected source file: `{chosen.get('sourceFile', '')}`",
        "",
        "## Selected declarations",
    ]
    for name in chosen.get("primaryProduces", []):
        lines.append(f"- `{name}`")
    lines += [
        "",
        "## Top frontier context",
    ]
    for name in payload["frontierContext"]:
        lines.append(f"- `{name}`")
    lines += [
        "",
        "## Targeted build",
        f"- module: `{payload['module']}`",
        f"- quarantine file: `{payload['relativeFile']}`",
        f"- return code: `{payload['targetedBuild']['returncode']}`",
        f"- stdout: `{payload['targetedBuild']['stdout_path']}`",
        f"- stderr: `{payload['targetedBuild']['stderr_path']}`",
        "",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    root = repo_root()
    if not args.allow_dirty_tracked:
        ensure_clean_tracked_tree(root)

    frontier_path = (root / args.frontier_json).resolve()
    if not frontier_path.exists():
        raise SystemExit(f"missing frontier JSON: {frontier_path}")
    frontier_obj = load_json(frontier_path)
    chosen, top_rows = selected_frontier_rows(frontier_obj, args.frontier_index, args.top_k)

    run_id = now_utc_compact()
    git_head = run_text(["git", "rev-parse", "HEAD"], cwd=root).stdout.strip()
    branch_name = f"{args.branch_prefix}{run_id}"
    worktree_path = Path(args.worktree_root).resolve() / run_id
    run_dir = (root / args.runs_dir / run_id).resolve()
    run_dir.mkdir(parents=True, exist_ok=True)

    write_manifest(
        run_dir / "preflight.json",
        {
            "runId": run_id,
            "gitHead": git_head,
            "branchName": branch_name,
            "worktreePath": str(worktree_path),
            "frontierJson": str(frontier_path),
            "walk": frontier_obj.get("walk"),
            "seedNames": frontier_obj.get("seedNames", []),
            "seedBlocks": frontier_obj.get("seedBlocks", []),
            "chosenFrontier": chosen,
        },
    )

    worktree_cmd = run_capture(
        ["git", "worktree", "add", "-b", branch_name, str(worktree_path), "HEAD"],
        cwd=root,
        stdout_path=run_dir / "git-worktree-add.stdout.log",
        stderr_path=run_dir / "git-worktree-add.stderr.log",
    )
    if worktree_cmd.returncode != 0:
        write_manifest(
            run_dir / "manifest.json",
            {
                "status": "worktree_failed",
                "runId": run_id,
                "gitHead": git_head,
                "branchName": branch_name,
                "worktreePath": str(worktree_path),
                "frontierJson": str(frontier_path),
                "worktreeCommand": asdict(worktree_cmd),
            },
        )
        return worktree_cmd.returncode

    relative_file = Path(args.relative_file)
    quarantine_path = worktree_path / relative_file
    quarantine_path.parent.mkdir(parents=True, exist_ok=True)
    file_text = render_quarantine_file(run_id, frontier_path, frontier_obj, chosen, top_rows)
    quarantine_path.write_text(file_text, encoding="utf-8")

    top_names: list[str] = []
    for row in top_rows:
        produces = [str(x) for x in row.get("primaryProduces", [])]
        top_names.extend(produces[:1] if produces else [str(row.get("stableId", ""))])

    targeted_cmd = run_capture(
        ["lake", "build", args.module],
        cwd=worktree_path,
        stdout_path=run_dir / "targeted-build.stdout.log",
        stderr_path=run_dir / "targeted-build.stderr.log",
    )

    manifest = {
        "status": "ok" if targeted_cmd.returncode == 0 else "targeted_build_failed",
        "runId": run_id,
        "gitHead": git_head,
        "branchName": branch_name,
        "worktreePath": str(worktree_path),
        "frontierJson": str(frontier_path),
        "walk": frontier_obj.get("walk"),
        "seedNames": frontier_obj.get("seedNames", []),
        "seedBlocks": frontier_obj.get("seedBlocks", []),
        "chosenFrontier": chosen,
        "frontierContext": top_names,
        "module": args.module,
        "relativeFile": str(relative_file),
        "quarantineFile": str(quarantine_path),
        "worktreeCommand": asdict(worktree_cmd),
        "targetedBuild": asdict(targeted_cmd),
        "cleanupWorktree": bool(args.cleanup_worktree),
        "environment": {
            "cwd": str(root),
            "python": sys.executable,
        },
    }
    write_manifest(run_dir / "manifest.json", manifest)
    write_summary(run_dir / "summary.md", manifest)

    if args.cleanup_worktree:
        cleanup_cmd = run_capture(
            ["git", "worktree", "remove", "--force", str(worktree_path)],
            cwd=root,
            stdout_path=run_dir / "git-worktree-remove.stdout.log",
            stderr_path=run_dir / "git-worktree-remove.stderr.log",
        )
        manifest["cleanupCommand"] = asdict(cleanup_cmd)
        write_manifest(run_dir / "manifest.json", manifest)

    print(f"[run-optimization-cycle] run dir: {run_dir}")
    print(f"[run-optimization-cycle] worktree: {worktree_path}")
    print(f"[run-optimization-cycle] status: {manifest['status']}")
    return 0 if targeted_cmd.returncode == 0 else targeted_cmd.returncode


if __name__ == "__main__":
    raise SystemExit(main())
