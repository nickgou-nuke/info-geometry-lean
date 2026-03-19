#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from build_lock import acquire_build_lock
    from pathing import repo_root
else:
    from tools.build_lock import acquire_build_lock
    from tools.pathing import repo_root


DEFAULT_FRONTIER_JSON = "reports/dag/skynet-v2-frontier-reverse.json"
DEFAULT_RUNS_DIR = "reports/optimization-runs"
DEFAULT_WORKTREE_ROOT = "/tmp/info-geometry-autoopt"
DEFAULT_BRANCH_PREFIX = "auto-opt/dry-cycle-"
DEFAULT_LAB_NAME = "current"
DEFAULT_MODULE = "InfoGeometry.Unstable.AutoOptCycle"
DEFAULT_REL_FILE = "lean/InfoGeometry/Unstable/AutoOptCycle.lean"
DEFAULT_CANDIDATE_PACKET = "skills/info-geometry-repo/references/bridge-candidates.md"


@dataclass
class CommandResult:
    argv: list[str]
    returncode: int
    stdout_path: str
    stderr_path: str


@dataclass
class CandidateSketch:
    ordinal: int
    name: str
    signature_sketch: str
    why: str
    proof_ingredients: list[str]
    risk: str


@dataclass
class HydrationResult:
    copied_packages: bool
    copied_build: bool
    package_copy: CommandResult | None
    build_copy: CommandResult | None


def acquire_worktree_lock(worktree_path: Path, run_id: str) -> Path:
    worktree_path.mkdir(parents=True, exist_ok=True)
    lock_path = worktree_path / ".autoopt.lock"
    try:
        fd = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        raise SystemExit(f"worktree already locked by another optimization cycle: {lock_path}")
    with os.fdopen(fd, "w", encoding="utf-8") as handle:
        handle.write(run_id + "\n")
    return lock_path


def release_worktree_lock(lock_path: Path | None) -> None:
    if lock_path is None:
        return
    try:
        lock_path.unlink()
    except FileNotFoundError:
        pass


def hydrate_worktree_from_local_lake(root: Path, worktree_path: Path, run_dir: Path) -> HydrationResult:
    src_lake = root / ".lake"
    dst_lake = worktree_path / ".lake"
    dst_lake.mkdir(parents=True, exist_ok=True)

    package_copy: CommandResult | None = None
    build_copy: CommandResult | None = None

    src_packages = src_lake / "packages"
    dst_packages = dst_lake / "packages"
    copied_packages = False
    if src_packages.exists():
        dst_packages.mkdir(parents=True, exist_ok=True)
        package_copy = run_capture(
            ["cp", "-a", "-n", f"{src_packages}/.", str(dst_packages)],
            cwd=root,
            stdout_path=run_dir / "hydrate-packages.stdout.log",
            stderr_path=run_dir / "hydrate-packages.stderr.log",
        )
        copied_packages = package_copy.returncode == 0

    src_build = src_lake / "build"
    dst_build = dst_lake / "build"
    copied_build = False
    if src_build.exists():
        dst_build.mkdir(parents=True, exist_ok=True)
        build_copy = run_capture(
            ["cp", "-a", "-n", f"{src_build}/.", str(dst_build)],
            cwd=root,
            stdout_path=run_dir / "hydrate-build.stdout.log",
            stderr_path=run_dir / "hydrate-build.stderr.log",
        )
        copied_build = build_copy.returncode == 0

    return HydrationResult(
        copied_packages=copied_packages,
        copied_build=copied_build,
        package_copy=package_copy,
        build_copy=build_copy,
    )


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


def branch_exists(root: Path, branch_name: str) -> bool:
    proc = subprocess.run(
        ["git", "show-ref", "--verify", "--quiet", f"refs/heads/{branch_name}"],
        cwd=root,
        capture_output=True,
        text=True,
    )
    return proc.returncode == 0


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
        "--lab-name",
        default=DEFAULT_LAB_NAME,
        help="Persistent lab directory name under --worktree-root when not using --fresh-worktree.",
    )
    ap.add_argument(
        "--reuse-worktree",
        default=None,
        help="Reuse an existing isolated worktree instead of creating a fresh one.",
    )
    ap.add_argument(
        "--fresh-worktree",
        action="store_true",
        help="Create a new sterile worktree for this run instead of using the persistent lab.",
    )
    ap.add_argument(
        "--branch-prefix",
        default=DEFAULT_BRANCH_PREFIX,
        help="Prefix for generated fresh-worktree branch names.",
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
        "--candidate-packet",
        default=DEFAULT_CANDIDATE_PACKET,
        help="Tracked candidate packet markdown to consume.",
    )
    ap.add_argument(
        "--candidate-index",
        type=int,
        default=0,
        help="Index of the bridge candidate to materialize into the quarantine module.",
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


def _capture_section(section: str, label: str, next_label: str | None = None) -> str:
    pattern = rf"`{re.escape(label)}`\s*(.*)"
    if next_label is None:
        pattern = rf"`{re.escape(label)}`\s*(.*)\Z"
    else:
        pattern = rf"`{re.escape(label)}`\s*(.*?)\s*`{re.escape(next_label)}`"
    match = re.search(pattern, section, flags=re.S)
    if not match:
        raise SystemExit(f"candidate packet parse error: missing section `{label}`")
    return match.group(1).strip()


def parse_bridge_candidates(packet_path: Path) -> list[CandidateSketch]:
    text = packet_path.read_text(encoding="utf-8")
    matches = list(re.finditer(r"^## Candidate (\d+)\s*$", text, flags=re.M))
    if not matches:
        raise SystemExit(f"candidate packet contains no `## Candidate N` sections: {packet_path}")
    candidates: list[CandidateSketch] = []
    for i, match in enumerate(matches):
        start = match.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        section = text[start:end]
        ordinal = int(match.group(1))
        name_match = re.search(r"`name`\s*`([^`]+)`", section, flags=re.S)
        sketch_match = re.search(r"`Lean-style signature sketch`\s*```lean\n(.*?)```", section, flags=re.S)
        if not name_match or not sketch_match:
            raise SystemExit(f"candidate packet parse error in Candidate {ordinal}: missing name or sketch")
        why = _capture_section(
            section,
            "why this closes a real frontier edge",
            "likely proof ingredients already present in repo",
        )
        ingredients_block = _capture_section(
            section,
            "likely proof ingredients already present in repo",
            "risk level",
        )
        risk_match = re.search(r"`risk level`\s*`([^`]+)`", section, flags=re.S)
        if not risk_match:
            raise SystemExit(f"candidate packet parse error in Candidate {ordinal}: missing risk")
        proof_ingredients = [
            line.removeprefix("- ").strip()
            for line in ingredients_block.splitlines()
            if line.strip().startswith("- ")
        ]
        candidates.append(
            CandidateSketch(
                ordinal=ordinal,
                name=name_match.group(1).strip(),
                signature_sketch=sketch_match.group(1).strip(),
                why=why,
                proof_ingredients=proof_ingredients,
                risk=risk_match.group(1).strip(),
            )
        )
    return candidates


def select_candidate(candidates: list[CandidateSketch], candidate_index: int) -> CandidateSketch:
    if candidate_index < 0 or candidate_index >= len(candidates):
        raise SystemExit(
            f"--candidate-index {candidate_index} out of range for candidate packet of size {len(candidates)}"
        )
    return candidates[candidate_index]


def quoted_strings(xs: list[str]) -> str:
    if not xs:
        return "[]"
    inner = ", ".join(json.dumps(x) for x in xs)
    return f"[{inner}]"


def quoted_multiline(s: str) -> str:
    return json.dumps(s)


def persistent_branch_name(lab_name: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9._-]+", "-", lab_name).strip("-")
    safe = safe or DEFAULT_LAB_NAME
    return f"auto-opt/lab-{safe}"


def render_quarantine_file(
    run_id: str,
    frontier_path: Path,
    frontier_obj: dict[str, Any],
    chosen: dict[str, Any],
    top_rows: list[dict[str, Any]],
    candidate_packet_path: Path,
    candidate: CandidateSketch,
) -> str:
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

def candidatePacket : String := {json.dumps(str(candidate_packet_path))}

def candidateOrdinal : Nat := {candidate.ordinal}

def candidateName : String := {json.dumps(candidate.name)}

def candidateRisk : String := {json.dumps(candidate.risk)}

def candidateProofIngredients : List String := {quoted_strings(candidate.proof_ingredients)}

def candidateWhy : String := {quoted_multiline(candidate.why)}

/-
Report-only bridge candidate chosen for this isolated optimization cycle.
This remains a commented sketch until a later generation/refactor phase.
-/
/-
{candidate.signature_sketch}
-/

end InfoGeometry.Unstable.AutoOptCycle
"""


def write_manifest(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_summary(path: Path, payload: dict[str, Any]) -> None:
    chosen = payload["chosenFrontier"]
    candidate = payload["selectedCandidate"]
    lines = [
        "# Optimization Cycle",
        "",
        f"- run id: `{payload['runId']}`",
        f"- git head: `{payload['gitHead']}`",
        f"- branch: `{payload['branchName']}`",
        f"- worktree: `{payload['worktreePath']}`",
        f"- worktree mode: `{payload['worktreeMode']}`",
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
        "## Selected candidate",
        f"- ordinal: `{candidate.get('ordinal', '')}`",
        f"- name: `{candidate.get('name', '')}`",
        f"- risk: `{candidate.get('risk', '')}`",
        f"- packet: `{payload['candidatePacket']}`",
        "",
        "### Proof ingredients",
    ]
    for ingredient in candidate.get("proof_ingredients", []):
        lines.append(f"- `{ingredient}`")
    lines += [
        "",
        "## Top frontier context",
    ]
    for name in payload["frontierContext"]:
        lines.append(f"- `{name}`")
    hydration = payload.get("hydration", {})
    lines += [
        "",
        "## Hydration",
        f"- copied packages: `{hydration.get('copiedPackages', False)}`",
        f"- copied build cache: `{hydration.get('copiedBuild', False)}`",
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
    if args.reuse_worktree and args.fresh_worktree:
        raise SystemExit("cannot use --reuse-worktree together with --fresh-worktree")

    frontier_path = (root / args.frontier_json).resolve()
    if not frontier_path.exists():
        raise SystemExit(f"missing frontier JSON: {frontier_path}")
    frontier_obj = load_json(frontier_path)
    chosen, top_rows = selected_frontier_rows(frontier_obj, args.frontier_index, args.top_k)
    candidate_packet_path = (root / args.candidate_packet).resolve()
    if not candidate_packet_path.exists():
        raise SystemExit(f"missing candidate packet markdown: {candidate_packet_path}")
    candidates = parse_bridge_candidates(candidate_packet_path)
    candidate = select_candidate(candidates, args.candidate_index)

    run_id = now_utc_compact()
    git_head = run_text(["git", "rev-parse", "HEAD"], cwd=root).stdout.strip()
    explicit_reuse = Path(args.reuse_worktree).resolve() if args.reuse_worktree else None
    persistent_path = Path(args.worktree_root).resolve() / args.lab_name
    if explicit_reuse is not None:
        if not explicit_reuse.exists():
            raise SystemExit(f"missing reuse worktree path: {explicit_reuse}")
        worktree_path = explicit_reuse
        branch_name = run_text(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=worktree_path).stdout.strip()
        created_worktree = False
        worktree_mode = "reused-explicit"
        reuse_worktree = explicit_reuse
    elif args.fresh_worktree:
        branch_name = f"{args.branch_prefix}{run_id}"
        worktree_path = Path(args.worktree_root).resolve() / run_id
        created_worktree = True
        worktree_mode = "created-fresh"
        reuse_worktree = None
    elif persistent_path.exists():
        worktree_path = persistent_path
        branch_name = run_text(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=worktree_path).stdout.strip()
        created_worktree = False
        worktree_mode = "reused-default"
        reuse_worktree = persistent_path
    else:
        branch_name = persistent_branch_name(args.lab_name)
        worktree_path = persistent_path
        created_worktree = True
        worktree_mode = "created-persistent"
        reuse_worktree = persistent_path
    run_dir = (root / args.runs_dir / run_id).resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    lock_path: Path | None = None
    build_lock = None

    write_manifest(
        run_dir / "preflight.json",
        {
            "runId": run_id,
            "gitHead": git_head,
            "branchName": branch_name,
            "worktreePath": str(worktree_path),
            "worktreeMode": worktree_mode,
            "reuseWorktree": str(reuse_worktree) if reuse_worktree else None,
            "freshWorktree": bool(args.fresh_worktree),
            "frontierJson": str(frontier_path),
            "walk": frontier_obj.get("walk"),
            "seedNames": frontier_obj.get("seedNames", []),
            "seedBlocks": frontier_obj.get("seedBlocks", []),
            "chosenFrontier": chosen,
            "candidatePacket": str(candidate_packet_path),
            "selectedCandidate": asdict(candidate),
        },
    )

    worktree_cmd: CommandResult | None = None
    if created_worktree:
        if worktree_path.exists():
            raise SystemExit(f"refusing to create worktree at existing path: {worktree_path}")
        if branch_exists(root, branch_name):
            add_cmd = ["git", "worktree", "add", str(worktree_path), branch_name]
        else:
            add_cmd = ["git", "worktree", "add", "-b", branch_name, str(worktree_path), "HEAD"]
        worktree_cmd = run_capture(
            add_cmd,
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
                    "worktreeMode": worktree_mode,
                    "reuseWorktree": str(reuse_worktree) if reuse_worktree else None,
                    "freshWorktree": bool(args.fresh_worktree),
                    "frontierJson": str(frontier_path),
                    "worktreeCommand": asdict(worktree_cmd),
                },
            )
            return worktree_cmd.returncode

    try:
        lock_path = acquire_worktree_lock(worktree_path, run_id)
        build_lock = acquire_build_lock(None, f"run-optimization-cycle:{run_id}")
        relative_file = Path(args.relative_file)
        quarantine_path = worktree_path / relative_file
        quarantine_path.parent.mkdir(parents=True, exist_ok=True)
        file_text = render_quarantine_file(
            run_id,
            frontier_path,
            frontier_obj,
            chosen,
            top_rows,
            candidate_packet_path,
            candidate,
        )
        quarantine_path.write_text(file_text, encoding="utf-8")

        hydration = hydrate_worktree_from_local_lake(root, worktree_path, run_dir)

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
            "worktreeMode": worktree_mode,
            "reuseWorktree": str(reuse_worktree) if reuse_worktree else None,
            "freshWorktree": bool(args.fresh_worktree),
            "frontierJson": str(frontier_path),
            "walk": frontier_obj.get("walk"),
            "seedNames": frontier_obj.get("seedNames", []),
            "seedBlocks": frontier_obj.get("seedBlocks", []),
            "chosenFrontier": chosen,
            "candidatePacket": str(candidate_packet_path),
            "selectedCandidate": asdict(candidate),
            "frontierContext": top_names,
            "module": args.module,
            "relativeFile": str(relative_file),
            "quarantineFile": str(quarantine_path),
            "worktreeLock": str(lock_path),
            "buildLock": str(build_lock.lock_path),
            "worktreeCommand": asdict(worktree_cmd) if worktree_cmd is not None else None,
            "hydration": {
                "copiedPackages": hydration.copied_packages,
                "copiedBuild": hydration.copied_build,
                "packageCopy": asdict(hydration.package_copy) if hydration.package_copy else None,
                "buildCopy": asdict(hydration.build_copy) if hydration.build_copy else None,
            },
            "targetedBuild": asdict(targeted_cmd),
            "cleanupWorktree": bool(args.cleanup_worktree),
            "environment": {
                "cwd": str(root),
                "python": sys.executable,
            },
        }
        write_manifest(run_dir / "manifest.json", manifest)
        write_summary(run_dir / "summary.md", manifest)

        if args.cleanup_worktree and targeted_cmd.returncode == 0:
            release_worktree_lock(lock_path)
            lock_path = None
            cleanup_cmd = run_capture(
                ["git", "worktree", "remove", "--force", str(worktree_path)],
                cwd=root,
                stdout_path=run_dir / "git-worktree-remove.stdout.log",
                stderr_path=run_dir / "git-worktree-remove.stderr.log",
            )
            manifest["cleanupCommand"] = asdict(cleanup_cmd)
            write_manifest(run_dir / "manifest.json", manifest)
        elif args.cleanup_worktree and targeted_cmd.returncode != 0:
            manifest["cleanupSkipped"] = "targeted_build_failed"
            write_manifest(run_dir / "manifest.json", manifest)
    finally:
        if build_lock is not None:
            build_lock.release()
        release_worktree_lock(lock_path)

    print(f"[run-optimization-cycle] run dir: {run_dir}")
    print(f"[run-optimization-cycle] worktree: {worktree_path}")
    print(f"[run-optimization-cycle] status: {manifest['status']}")
    return 0 if targeted_cmd.returncode == 0 else targeted_cmd.returncode


if __name__ == "__main__":
    raise SystemExit(main())
