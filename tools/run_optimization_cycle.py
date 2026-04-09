#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from tools.build_lock import acquire_build_lock
    from tools.pathing import repo_root
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
DEFAULT_FAILURE_CORRECTION_RETRIES = 1


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
    review_verdict: str | None = None
    review_reason: str | None = None
    quarantine_recommendation: str | None = None
    materialization_sketch: str | None = None


@dataclass
class HydrationResult:
    copied_packages: bool
    copied_build: bool
    package_copy: CommandResult | None
    build_copy: CommandResult | None


@dataclass
class ProofAttemptRecord:
    attempt: int
    context_path: str
    command_template: str
    command: list[str] | None
    proof_command: CommandResult | None
    proof_report: dict[str, Any] | None
    materialization_status: str | None
    failure_correction_command: list[str] | None
    failure_correction: CommandResult | None
    targeted_build: CommandResult


def acquire_worktree_lock(worktree_path: Path, run_id: str, recover_stale_lock: bool = False) -> Path:
    worktree_path.mkdir(parents=True, exist_ok=True)
    lock_path = worktree_path / ".autoopt.lock"
    try:
        fd = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        stale_removed = False
        try:
            raw_lines = lock_path.read_text(encoding="utf-8").splitlines()
        except OSError:
            raw_lines = []
        owner_run_id = raw_lines[0].strip() if raw_lines else "unknown"
        owner_pid: int | None = None
        if len(raw_lines) >= 2:
            try:
                owner_pid = int(raw_lines[1].strip())
            except ValueError:
                owner_pid = None
        # Locking remains strict by default. Stale-lock recovery is an explicit
        # operator override to avoid accidentally allowing concurrent runs.
        if recover_stale_lock:
            if owner_pid is not None:
                alive = True
                try:
                    os.kill(owner_pid, 0)
                except ProcessLookupError:
                    alive = False
                except PermissionError:
                    alive = True
                if not alive:
                    lock_path.unlink(missing_ok=True)
                    stale_removed = True
            else:
                # Legacy lockfiles may only contain run id. Under explicit
                # operator override we allow recovering these stale locks.
                lock_path.unlink(missing_ok=True)
                stale_removed = True

        if stale_removed:
            fd = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        else:
            owner_suffix = f" (owner run: {owner_run_id})"
            if owner_pid is not None:
                owner_suffix += f" (pid: {owner_pid})"
            raise SystemExit(
                "worktree already locked by another optimization cycle: "
                f"{lock_path}{owner_suffix}"
            )
    with os.fdopen(fd, "w", encoding="utf-8") as handle:
        handle.write(run_id + "\n")
        handle.write(str(os.getpid()) + "\n")
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


def load_text(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8")


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
        "--proof-attempt-command",
        default=None,
        help=(
            "Optional external command template to run inside quarantine before each targeted build. "
            "Supported placeholders: {context_json}, {worktree}, {module}, {relative_file}, "
            "{quarantine_file}, {attempt}, {run_dir}."
        ),
    )
    ap.add_argument(
        "--proof-attempt-retries",
        type=int,
        default=0,
        help="How many extra proof/build retries to allow after the initial attempt.",
    )
    ap.add_argument(
        "--failure-correction-command",
        default=None,
        help=(
            "Optional external command template to run after a failed targeted build, "
            "before automatic resubmission. Supported placeholders: {context_json}, "
            "{worktree}, {module}, {relative_file}, {quarantine_file}, {attempt}, "
            "{run_dir}, {build_stdout}, {build_stderr}."
        ),
    )
    ap.add_argument(
        "--failure-correction-retries",
        type=int,
        default=DEFAULT_FAILURE_CORRECTION_RETRIES,
        help="How many correction+resubmission retries to allow after the initial failed build.",
    )
    ap.add_argument(
        "--allow-dirty-tracked",
        action="store_true",
        help="Development override: allow the cycle to run even with tracked local modifications.",
    )
    ap.add_argument(
        "--recover-stale-worktree-lock",
        action="store_true",
        help=(
            "Operator override: if the worktree lock owner PID is provably dead, "
            "clear that stale lock and continue. By default, lock blocking is strict."
        ),
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


def _capture_inline_value_optional(section: str, labels: list[str]) -> str | None:
    for label in labels:
        match = re.search(rf"`{re.escape(label)}`\s*`([^`]+)`", section, flags=re.S)
        if match:
            return match.group(1).strip()
    return None


def _capture_code_block_optional(section: str, labels: list[str]) -> str | None:
    for label in labels:
        match = re.search(rf"`{re.escape(label)}`\s*```lean\n(.*?)```", section, flags=re.S)
        if match:
            return match.group(1).strip()
    return None


def _capture_section_optional(section: str, labels: list[str], next_labels: list[str]) -> str | None:
    starts: list[tuple[int, int]] = []
    for label in labels:
        match = re.search(rf"`{re.escape(label)}`", section, flags=re.S)
        if match:
            starts.append((match.start(), match.end()))
    if not starts:
        return None
    _, start_end = min(starts, key=lambda item: item[0])
    end_positions: list[int] = []
    for label in next_labels:
        match = re.search(rf"`{re.escape(label)}`", section[start_end:], flags=re.S)
        if match:
            end_positions.append(start_end + match.start())
    end = min(end_positions) if end_positions else len(section)
    return section[start_end:end].strip()


def _normalize_sketch_block(sketch: str | None) -> str | None:
    if sketch is None:
        return None
    text = sketch.strip()
    fenced = re.fullmatch(r"```(?:lean)?\n(.*?)```", text, flags=re.S)
    if fenced:
        return fenced.group(1).strip()
    return text


def parse_bridge_candidates(packet_path: Path) -> list[CandidateSketch]:
    text = packet_path.read_text(encoding="utf-8")
    matches = list(re.finditer(r"^## Candidate (\d+)\s*$", text, flags=re.M))
    if not matches:
        return []
    candidates: list[CandidateSketch] = []
    for i, match in enumerate(matches):
        start = match.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        section = text[start:end]
        ordinal = int(match.group(1))
        name = _capture_inline_value_optional(section, ["name"])
        signature_sketch = _capture_code_block_optional(
            section,
            ["Lean-style signature sketch", "minimal Lean-style signature sketch"],
        )
        materialization_sketch = _capture_code_block_optional(
            section,
            [
                "Lean-ready materialization sketch",
                "quarantine-ready materialization sketch",
                "concrete Lean materialization sketch",
                "minimal theorem header to materialize",
            ],
        )
        if materialization_sketch is None:
            materialization_sketch = _capture_section_optional(
                section,
                ["minimal theorem header to materialize"],
                [
                    "allowed helper lemmas",
                    "blocked moves",
                    "risk level",
                    "thinness risk",
                    "review verdict",
                    "verdict",
                    "review reason",
                    "reason",
                    "quarantine recommendation",
                ],
            )
        signature_sketch = _normalize_sketch_block(signature_sketch)
        materialization_sketch = _normalize_sketch_block(materialization_sketch)
        if signature_sketch is None:
            signature_sketch = materialization_sketch
        if not name or not signature_sketch:
            raise SystemExit(f"candidate packet parse error in Candidate {ordinal}: missing name or sketch")
        why = _capture_section_optional(
            section,
            ["why this closes a real frontier edge", "which graph gap it closes"],
            [
                "likely proof ingredients already present in repo",
                "proof ingredients already present in repo",
                "risk level",
                "thinness risk",
                "review verdict",
                "verdict",
                "review reason",
                "reason",
                "quarantine recommendation",
                "Lean-ready materialization sketch",
                "quarantine-ready materialization sketch",
                "concrete Lean materialization sketch",
            ],
        ) or ""
        ingredients_block = _capture_section_optional(
            section,
            ["likely proof ingredients already present in repo", "proof ingredients already present in repo"],
            [
                "risk level",
                "thinness risk",
                "review verdict",
                "verdict",
                "review reason",
                "reason",
                "quarantine recommendation",
                "Lean-ready materialization sketch",
                "quarantine-ready materialization sketch",
                "concrete Lean materialization sketch",
            ],
        ) or ""
        risk = _capture_inline_value_optional(section, ["risk level", "thinness risk"]) or "unknown"
        review_verdict = _capture_inline_value_optional(section, ["review verdict", "review_verdict", "verdict"])
        review_reason = _capture_section_optional(
            section,
            ["review reason", "review_reason", "reason"],
            [
                "Lean-style signature sketch",
                "minimal Lean-style signature sketch",
                "likely proof ingredients already present in repo",
                "proof ingredients already present in repo",
                "risk level",
                "thinness risk",
                "quarantine recommendation",
                "quarantine_recommendation",
                "Lean-ready materialization sketch",
                "quarantine-ready materialization sketch",
                "concrete Lean materialization sketch",
            ],
        )
        quarantine_recommendation = _capture_inline_value_optional(
            section,
            ["quarantine recommendation", "quarantine_recommendation"],
        )
        proof_ingredients = [
            line.removeprefix("- ").strip()
            for line in ingredients_block.splitlines()
            if line.strip().startswith("- ")
        ]
        candidates.append(
            CandidateSketch(
                ordinal=ordinal,
                name=name,
                signature_sketch=signature_sketch,
                why=why,
                proof_ingredients=proof_ingredients,
                risk=risk,
                review_verdict=review_verdict,
                review_reason=review_reason,
                quarantine_recommendation=quarantine_recommendation,
                materialization_sketch=materialization_sketch,
            )
        )
    return candidates


def placeholder_candidate_for_frontier(chosen: dict[str, Any], packet_path: Path) -> CandidateSketch:
    produces = [str(x) for x in chosen.get("primaryProduces", [])]
    stable_id = str(chosen.get("stableId", "")).strip()
    source_file = str(chosen.get("sourceFile", "")).strip()
    name = produces[0] if produces else (stable_id or "unnamed_frontier_target")
    why_bits = [
        "No reviewed candidate sketch is currently present in the checked-in candidate packet.",
        f"Packet: {packet_path}",
    ]
    if source_file:
        why_bits.append(f"Frontier source file: {source_file}")
    return CandidateSketch(
        ordinal=0,
        name=name,
        signature_sketch="-- placeholder only: no reviewed candidate sketch available",
        why=" ".join(why_bits),
        proof_ingredients=[],
        risk="unreviewed",
        review_verdict="missing-packet-candidates",
        review_reason="candidate packet is present but contains no concrete `## Candidate N` sections",
        quarantine_recommendation="no",
        materialization_sketch=None,
    )


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
    materialization_block = ""
    if candidate.materialization_sketch and candidate.materialization_sketch != candidate.signature_sketch:
        materialization_block = f"""
/-
Reviewed concrete materialization sketch.
The external proof driver may materialize this theorem only if the reviewed
packet explicitly recommends quarantine execution.
-/
/-
{candidate.materialization_sketch}
-/
"""
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

def candidateReviewVerdict : String := {json.dumps(candidate.review_verdict or "")}

def candidateQuarantineRecommendation : String := {json.dumps(candidate.quarantine_recommendation or "")}

def candidateProofIngredients : List String := {quoted_strings(candidate.proof_ingredients)}

def candidateWhy : String := {quoted_multiline(candidate.why)}

/-
Report-only bridge candidate chosen for this isolated optimization cycle.
This remains a commented sketch until a later generation/refactor phase.
-/
/-
{candidate.signature_sketch}
-/
{materialization_block}

end InfoGeometry.Unstable.AutoOptCycle
"""


def write_manifest(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def append_trace(run_dir: Path, event: str, **fields: Any) -> None:
    trace_path = run_dir / "trace.ndjson"
    payload: dict[str, Any] = {"ts": utc_now_iso(), "event": event}
    payload.update(fields)
    with trace_path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, sort_keys=True) + "\n")


def write_runtime_state(run_dir: Path, phase: str, **fields: Any) -> None:
    state_path = run_dir / "runtime_state.json"
    payload: dict[str, Any] = {"ts": utc_now_iso(), "phase": phase}
    payload.update(fields)
    state_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


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
    ]
    review_verdict = candidate.get("review_verdict")
    quarantine_recommendation = candidate.get("quarantine_recommendation")
    materialization_sketch = candidate.get("materialization_sketch")
    if review_verdict:
        lines.append(f"- review verdict: `{review_verdict}`")
    if quarantine_recommendation:
        lines.append(f"- quarantine recommendation: `{quarantine_recommendation}`")
    lines += [
        f"- reviewed materialization sketch: `{'yes' if materialization_sketch else 'no'}`",
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
        f"- run status: `{payload.get('status', 'unknown')}`",
        f"- build status: `{payload.get('buildStatus', payload.get('status', 'unknown'))}`",
        f"- materialization status: `{payload.get('materializationStatus', 'unknown')}`",
        f"- module: `{payload['module']}`",
        f"- quarantine file: `{payload['relativeFile']}`",
        f"- return code: `{payload['targetedBuild']['returncode']}`",
        f"- stdout: `{payload['targetedBuild']['stdout_path']}`",
        f"- stderr: `{payload['targetedBuild']['stderr_path']}`",
        "",
    ]
    proof_attempts = payload.get("proofAttempts", [])
    if proof_attempts:
        lines += ["## Proof Attempts"]
        for attempt in proof_attempts:
            lines.append(
                f"- attempt `{attempt.get('attempt')}` build return code: "
                f"`{attempt.get('targeted_build', {}).get('returncode')}`"
            )
            materialization_status = attempt.get("materialization_status")
            if materialization_status is not None:
                lines.append(f"  materialization status: `{materialization_status}`")
            proof_command = attempt.get("proof_command")
            if proof_command is not None:
                lines.append(f"  proof command return code: `{proof_command.get('returncode')}`")
            proof_report = attempt.get("proof_report")
            if proof_report is not None:
                lines.append(f"  proof report: `{proof_report.get('path', '')}`")
                verdict = proof_report.get("verdict")
                if verdict:
                    lines.append(f"  proof report verdict: `{verdict}`")
            correction = attempt.get("failure_correction")
            if correction is not None:
                lines.append(
                    f"  failure correction return code: `{correction.get('returncode')}`"
                )
        lines.append("")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def _extract_report_value(report_text: str, label: str) -> str | None:
    match = re.search(rf"^- {re.escape(label)}: `([^`]+)`", report_text, flags=re.M)
    if not match:
        return None
    return match.group(1).strip()


def parse_proof_report(report_path: Path) -> dict[str, Any] | None:
    if not report_path.exists():
        return None
    report_text = report_path.read_text(encoding="utf-8")
    materialized_raw = _extract_report_value(report_text, "materialized")
    materialized: bool | None = None
    if materialized_raw is not None:
        materialized = materialized_raw.lower() == "true"
    return {
        "path": str(report_path),
        "verdict": _extract_report_value(report_text, "verdict"),
        "materialized": materialized,
        "sketch_source": _extract_report_value(report_text, "sketch source"),
    }


def normalize_materialization_status(verdict: str | None) -> str | None:
    if not verdict:
        return None
    normalized = verdict.strip().lower().replace("-", "_")
    if normalized == "defer":
        return "deferred"
    return normalized


def aggregate_materialization_status(
    proof_attempts: list[ProofAttemptRecord],
    proof_requested: bool,
) -> tuple[str, str | None]:
    statuses = [attempt.materialization_status for attempt in proof_attempts if attempt.materialization_status]
    final_status = statuses[-1] if statuses else None
    if not proof_requested:
        return "not_requested", final_status
    if "materialized" in statuses:
        return "materialized", final_status
    if "already_present" in statuses:
        return "already_present", final_status
    if "deferred" in statuses:
        return "deferred", final_status
    return "unknown", final_status


def classify_cycle_status(build_status: str, materialization_status: str) -> str:
    if build_status != "ok":
        return build_status
    if materialization_status == "not_requested":
        return "ok_no_proof_attempt"
    if materialization_status == "materialized":
        return "ok_materialized"
    if materialization_status == "already_present":
        return "ok_already_present"
    if materialization_status == "deferred":
        return "ok_deferred"
    return "ok_unknown_materialization"


def proof_attempt_command(
    template: str,
    context_path: Path,
    worktree_path: Path,
    args: argparse.Namespace,
    attempt: int,
    quarantine_path: Path,
    run_dir: Path,
) -> list[str]:
    formatted = template.format(
        context_json=str(context_path),
        worktree=str(worktree_path),
        module=args.module,
        relative_file=str(args.relative_file),
        quarantine_file=str(quarantine_path),
        attempt=attempt,
        run_dir=str(run_dir),
    )
    return shlex.split(formatted)


def failure_correction_command(
    template: str,
    context_path: Path,
    worktree_path: Path,
    args: argparse.Namespace,
    attempt: int,
    quarantine_path: Path,
    run_dir: Path,
    build_stdout: Path,
    build_stderr: Path,
) -> list[str]:
    formatted = template.format(
        context_json=str(context_path),
        worktree=str(worktree_path),
        module=args.module,
        relative_file=str(args.relative_file),
        quarantine_file=str(quarantine_path),
        attempt=attempt,
        run_dir=str(run_dir),
        build_stdout=str(build_stdout),
        build_stderr=str(build_stderr),
    )
    return shlex.split(formatted)


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
    if candidates:
        candidate = select_candidate(candidates, args.candidate_index)
    else:
        candidate = placeholder_candidate_for_frontier(chosen, candidate_packet_path)

    if args.failure_correction_command is None:
        args.failure_correction_command = (
            f"{shlex.quote(sys.executable)} "
            f"{shlex.quote(str((root / 'tools' / 'failure_correction_driver.py').resolve()))} "
            "--context {context_json} "
            "--build-stdout {build_stdout} "
            "--build-stderr {build_stderr} "
            "--quarantine-file {quarantine_file}"
        )

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
    append_trace(run_dir, "run_started", run_id=run_id)
    write_runtime_state(run_dir, "starting", run_id=run_id)
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
            "proofAttemptCommandTemplate": args.proof_attempt_command,
            "proofAttemptRetries": max(args.proof_attempt_retries, 0),
            "failureCorrectionCommandTemplate": args.failure_correction_command,
            "failureCorrectionRetries": max(args.failure_correction_retries, 0),
        },
    )

    worktree_cmd: CommandResult | None = None
    if created_worktree:
        write_runtime_state(run_dir, "worktree_setup", created_worktree=True, worktree=str(worktree_path))
        append_trace(run_dir, "worktree_setup_started", worktree=str(worktree_path), branch=branch_name)
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
            worktree_error = load_text(Path(worktree_cmd.stderr_path)).strip()
            append_trace(run_dir, "worktree_setup_failed", returncode=worktree_cmd.returncode)
            write_runtime_state(run_dir, "failed", reason="worktree_failed", returncode=worktree_cmd.returncode)
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
                    "worktreeError": worktree_error,
                },
            )
            if worktree_error:
                print(
                    "[run-optimization-cycle] worktree setup failed:\n"
                    f"{worktree_error}",
                    file=sys.stderr,
                )
            return worktree_cmd.returncode

    try:
        write_runtime_state(run_dir, "acquiring_locks", worktree=str(worktree_path))
        lock_path = acquire_worktree_lock(
            worktree_path,
            run_id,
            recover_stale_lock=bool(args.recover_stale_worktree_lock),
        )
        append_trace(run_dir, "worktree_lock_acquired", lock_path=str(lock_path))
        build_lock = acquire_build_lock(None, f"run-optimization-cycle:{run_id}")
        append_trace(run_dir, "build_lock_acquired", lock_path=str(build_lock.lock_path))
        relative_file = Path(args.relative_file)
        quarantine_path = worktree_path / relative_file
        write_runtime_state(run_dir, "render_quarantine", relative_file=str(relative_file))
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
        append_trace(run_dir, "quarantine_written", quarantine_file=str(quarantine_path))

        write_runtime_state(run_dir, "hydrating_worktree")
        hydration = hydrate_worktree_from_local_lake(root, worktree_path, run_dir)
        append_trace(
            run_dir,
            "hydration_completed",
            copied_packages=hydration.copied_packages,
            copied_build=hydration.copied_build,
        )

        top_names: list[str] = []
        for row in top_rows:
            produces = [str(x) for x in row.get("primaryProduces", [])]
            top_names.extend(produces[:1] if produces else [str(row.get("stableId", ""))])

        proof_attempts: list[ProofAttemptRecord] = []
        proof_retries = max(args.proof_attempt_retries, 0) if args.proof_attempt_command else 0
        correction_retries = max(args.failure_correction_retries, 0) if args.failure_correction_command else 0
        total_attempts = 1 + max(proof_retries, correction_retries)
        targeted_cmd: CommandResult | None = None
        for attempt in range(1, total_attempts + 1):
            write_runtime_state(run_dir, "attempt_start", attempt=attempt, total_attempts=total_attempts)
            append_trace(run_dir, "attempt_started", attempt=attempt, total_attempts=total_attempts)
            context_path = run_dir / f"proof-attempt-{attempt}.context.json"
            proof_command_result: CommandResult | None = None
            proof_command_argv: list[str] | None = None
            proof_report: dict[str, Any] | None = None
            materialization_status: str | None = None
            correction_command_result: CommandResult | None = None
            correction_command_argv: list[str] | None = None
            context_payload = {
                "runId": run_id,
                "attempt": attempt,
                "frontierJson": str(frontier_path),
                "chosenFrontier": chosen,
                "selectedCandidate": asdict(candidate),
                "module": args.module,
                "relativeFile": str(relative_file),
                "quarantineFile": str(quarantine_path),
                "worktreePath": str(worktree_path),
                "runDir": str(run_dir),
                "previousBuild": asdict(targeted_cmd) if targeted_cmd is not None else None,
                "failureCorrectionCommandTemplate": args.failure_correction_command,
            }
            write_manifest(context_path, context_payload)
            append_trace(run_dir, "attempt_context_written", attempt=attempt, context_path=str(context_path))

            if args.proof_attempt_command:
                write_runtime_state(run_dir, "proof_attempt_running", attempt=attempt)
                proof_command_argv = proof_attempt_command(
                    args.proof_attempt_command,
                    context_path,
                    worktree_path,
                    args,
                    attempt,
                    quarantine_path,
                    run_dir,
                )
                proof_command_result = run_capture(
                    proof_command_argv,
                    cwd=worktree_path,
                    stdout_path=run_dir / f"proof-attempt-{attempt}.stdout.log",
                    stderr_path=run_dir / f"proof-attempt-{attempt}.stderr.log",
                )
                proof_report = parse_proof_report(context_path.with_suffix(".report.md"))
                materialization_status = normalize_materialization_status(
                    proof_report.get("verdict") if proof_report else None
                )
                append_trace(
                    run_dir,
                    "proof_attempt_completed",
                    attempt=attempt,
                    returncode=proof_command_result.returncode,
                    materialization_status=materialization_status,
                )

            build_stdout = run_dir / "targeted-build.stdout.log"
            build_stderr = run_dir / "targeted-build.stderr.log"
            if total_attempts > 1:
                build_stdout = run_dir / f"targeted-build-{attempt}.stdout.log"
                build_stderr = run_dir / f"targeted-build-{attempt}.stderr.log"
            write_runtime_state(run_dir, "targeted_build_running", attempt=attempt, module=args.module)
            append_trace(run_dir, "targeted_build_started", attempt=attempt, module=args.module)
            targeted_cmd = run_capture(
                ["lake", "build", args.module],
                cwd=worktree_path,
                stdout_path=build_stdout,
                stderr_path=build_stderr,
            )
            append_trace(
                run_dir,
                "targeted_build_completed",
                attempt=attempt,
                module=args.module,
                returncode=targeted_cmd.returncode,
                stdout_path=str(build_stdout),
                stderr_path=str(build_stderr),
            )

            if targeted_cmd.returncode != 0 and args.failure_correction_command and attempt < total_attempts:
                write_runtime_state(run_dir, "failure_correction_running", attempt=attempt, module=args.module)
                correction_command_argv = failure_correction_command(
                    args.failure_correction_command,
                    context_path,
                    worktree_path,
                    args,
                    attempt,
                    quarantine_path,
                    run_dir,
                    build_stdout,
                    build_stderr,
                )
                append_trace(
                    run_dir,
                    "failure_correction_started",
                    attempt=attempt,
                    module=args.module,
                    build_stdout=str(build_stdout),
                    build_stderr=str(build_stderr),
                )
                correction_command_result = run_capture(
                    correction_command_argv,
                    cwd=worktree_path,
                    stdout_path=run_dir / f"failure-correction-{attempt}.stdout.log",
                    stderr_path=run_dir / f"failure-correction-{attempt}.stderr.log",
                )
                append_trace(
                    run_dir,
                    "failure_correction_completed",
                    attempt=attempt,
                    returncode=correction_command_result.returncode,
                )

            proof_attempts.append(
                ProofAttemptRecord(
                    attempt=attempt,
                    context_path=str(context_path),
                    command_template=args.proof_attempt_command or "",
                    command=proof_command_argv,
                    proof_command=proof_command_result,
                    proof_report=proof_report,
                    materialization_status=materialization_status,
                    failure_correction_command=correction_command_argv,
                    failure_correction=correction_command_result,
                    targeted_build=targeted_cmd,
                )
            )
            if targeted_cmd.returncode == 0:
                break

        if targeted_cmd is None:
            raise SystemExit("internal error: targeted build did not execute")

        build_status = "ok" if targeted_cmd.returncode == 0 else "targeted_build_failed"
        materialization_status, final_materialization_status = aggregate_materialization_status(
            proof_attempts,
            bool(args.proof_attempt_command),
        )
        cycle_status = classify_cycle_status(build_status, materialization_status)
        manifest = {
            "status": cycle_status,
            "buildStatus": build_status,
            "materializationStatus": materialization_status,
            "finalAttemptMaterializationStatus": final_materialization_status,
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
            "proofAttemptCommandTemplate": args.proof_attempt_command,
            "proofAttemptRetries": max(args.proof_attempt_retries, 0),
            "failureCorrectionCommandTemplate": args.failure_correction_command,
            "failureCorrectionRetries": max(args.failure_correction_retries, 0),
            "proofAttempts": [
                {
                    "attempt": attempt.attempt,
                    "context_path": attempt.context_path,
                    "command_template": attempt.command_template,
                    "command": attempt.command,
                    "proof_command": asdict(attempt.proof_command) if attempt.proof_command else None,
                    "proof_report": attempt.proof_report,
                    "materialization_status": attempt.materialization_status,
                    "failure_correction_command": attempt.failure_correction_command,
                    "failure_correction": (
                        asdict(attempt.failure_correction) if attempt.failure_correction else None
                    ),
                    "targeted_build": asdict(attempt.targeted_build),
                }
                for attempt in proof_attempts
            ],
            "targetedBuild": asdict(targeted_cmd),
            "cleanupWorktree": bool(args.cleanup_worktree),
            "environment": {
                "cwd": str(root),
                "python": sys.executable,
            },
        }
        write_manifest(run_dir / "manifest.json", manifest)
        write_summary(run_dir / "summary.md", manifest)
        write_runtime_state(
            run_dir,
            "completed",
            status=manifest["status"],
            build_status=build_status,
            materialization_status=materialization_status,
        )
        append_trace(
            run_dir,
            "run_completed",
            status=manifest["status"],
            build_status=build_status,
            materialization_status=materialization_status,
        )

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
            append_trace(run_dir, "build_lock_released")
        release_worktree_lock(lock_path)
        if lock_path is not None:
            append_trace(run_dir, "worktree_lock_released", lock_path=str(lock_path))

    print(f"[run-optimization-cycle] run dir: {run_dir}")
    print(f"[run-optimization-cycle] worktree: {worktree_path}")
    print(f"[run-optimization-cycle] status: {manifest['status']}")
    print(f"[run-optimization-cycle] materialization status: {manifest['materializationStatus']}")
    return 0 if targeted_cmd.returncode == 0 else targeted_cmd.returncode


if __name__ == "__main__":
    raise SystemExit(main())
