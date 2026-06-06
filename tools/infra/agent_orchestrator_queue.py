#!/usr/bin/env python3
"""Concrete Researcher/SymPy/Lean queue runner for Archon and shell workflows.

This is the deterministic companion to agent-orchestrator.ts. It uses the same
task_queue.json contract and the same persistent side-by-side task files:

  proofs/<task-id>.lean
  proofs/<task-id>.sp

Execution order:
  1. Researcher and Algebraist run concurrently.
  2. Formalist runs Lean after grounding.
  3. Critic runs the vacuity linter.
  4. Archivist writes artifacts/agent_orchestrator/*.json.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path.cwd()
QUEUE_PATH = ROOT / "task_queue.json"
PROOF_DIR = ROOT / "proofs"
ARTIFACT_DIR = ROOT / "artifacts" / "agent_orchestrator"


def safe_id(value: str) -> str:
    return re.sub(r"[^a-zA-Z0-9_.-]", "_", value)


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_queue() -> dict[str, Any]:
    if not QUEUE_PATH.exists():
        return {
            "orchestrator": "deepseek/deepseek-v4-flash",
            "queue": [],
            "agents": {},
        }
    return json.loads(QUEUE_PATH.read_text())


def save_queue(queue: dict[str, Any]) -> None:
    QUEUE_PATH.write_text(json.dumps(queue, indent=2, ensure_ascii=False))


def task_lean_path(task: dict[str, Any]) -> Path:
    if task.get("lean_path"):
        return (ROOT / task["lean_path"]).resolve()
    return PROOF_DIR / f"{safe_id(task['id'])}.lean"


def task_sympy_path(task: dict[str, Any]) -> Path:
    if task.get("sympy_path"):
        return (ROOT / task["sympy_path"]).resolve()
    side_by_side = PROOF_DIR / f"{safe_id(task['id'])}.sp"
    if side_by_side.exists():
        return side_by_side
    return ROOT / "witnesses" / f"{safe_id(task['id'])}_sympy.py"


def stage_skip(stage: str, reason: str) -> dict[str, Any]:
    return {
        "stage": stage,
        "ok": True,
        "skipped": True,
        "elapsed_ms": 0,
        "stdout": reason,
    }


def run_command(
    stage: str,
    cmd: list[str],
    *,
    timeout: int,
    cwd: Path | None = None,
    path_for_report: Path | None = None,
    allow_exit_one: bool = False,
) -> dict[str, Any]:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            cmd,
            cwd=str(cwd or ROOT),
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        ok = completed.returncode == 0 or (allow_exit_one and completed.returncode == 1)
        return {
            "stage": stage,
            "ok": ok,
            "path": rel(path_for_report) if path_for_report else None,
            "command": cmd,
            "elapsed_ms": int((time.monotonic() - started) * 1000),
            "stdout": completed.stdout,
            "stderr": completed.stderr,
            "error": None if ok else f"exit code {completed.returncode}",
        }
    except Exception as exc:
        return {
            "stage": stage,
            "ok": False,
            "path": rel(path_for_report) if path_for_report else None,
            "command": cmd,
            "elapsed_ms": int((time.monotonic() - started) * 1000),
            "error": str(exc),
        }


def find_python_with_sympy() -> str | None:
    candidates = [
        ROOT / ".venv" / "bin" / "python3",
        ROOT / ".venv" / "bin" / "python",
        shutil.which("python3"),
        shutil.which("python"),
    ]
    for candidate in candidates:
        if candidate is None:
            continue
        candidate_s = str(candidate)
        if os.path.sep in candidate_s and not Path(candidate_s).exists():
            continue
        result = subprocess.run(
            [candidate_s, "-c", "import sympy"],
            text=True,
            capture_output=True,
            timeout=5,
            check=False,
        )
        if result.returncode == 0:
            return candidate_s
    return None


def run_researcher(task: dict[str, Any]) -> dict[str, Any]:
    roots = [p for p in ["lean", "docs", "tools"] if (ROOT / p).exists()]
    rg = shutil.which("rg")
    if not roots:
        return stage_skip("researcher", "No local search roots found.")
    if not rg:
        return stage_skip("researcher", "rg not available.")
    return run_command(
        "researcher",
        [
            rg,
            "-n",
            "--fixed-strings",
            "--ignore-case",
            "--max-count",
            "12",
            task["title"],
            *roots,
        ],
        timeout=15,
        allow_exit_one=True,
    )


def run_algebraist(task: dict[str, Any]) -> dict[str, Any]:
    sympy_path = task_sympy_path(task)
    if not sympy_path.exists():
        if task.get("sympy_witness"):
            return {
                "stage": "algebraist",
                "ok": False,
                "path": rel(sympy_path),
                "elapsed_ms": 0,
                "error": f"SymPy witness missing: {rel(sympy_path)}",
            }
        return stage_skip("algebraist", "No SymPy witness requested.")

    python = find_python_with_sympy()
    if not python:
        return {
            "stage": "algebraist",
            "ok": False,
            "path": rel(sympy_path),
            "elapsed_ms": 0,
            "error": "No Python executable with SymPy is available.",
        }
    return run_command(
        "algebraist",
        [python, str(sympy_path)],
        timeout=30,
        path_for_report=sympy_path,
    )


def run_formalist(task: dict[str, Any]) -> dict[str, Any]:
    lean_path = task_lean_path(task)
    if not lean_path.exists():
        if task.get("lean_proof"):
            return {
                "stage": "formalist",
                "ok": False,
                "path": rel(lean_path),
                "elapsed_ms": 0,
                "error": f"Lean proof missing: {rel(lean_path)}",
            }
        return stage_skip("formalist", "No Lean proof requested.")

    return run_command(
        "formalist",
        ["lake", "env", "lean", str(lean_path)],
        timeout=120,
        path_for_report=lean_path,
    )


def run_critic(task: dict[str, Any]) -> dict[str, Any]:
    lean_path = task_lean_path(task)
    if not lean_path.exists():
        return stage_skip("critic", "No Lean file to lint.")

    linter = ROOT / "tools" / "scripts" / "vacuity-linter.py"
    if not linter.exists():
        linter = ROOT / "scripts" / "vacuity-linter.py"
    if not linter.exists():
        return stage_skip("critic", "No vacuity linter found.")

    return run_command(
        "critic",
        ["python3", str(linter), "--json", str(lean_path)],
        timeout=30,
        path_for_report=lean_path,
    )


def write_report(report: dict[str, Any]) -> Path:
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    report_path = ARTIFACT_DIR / f"{stamp}_{safe_id(report['task_id'])}.json"
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False))
    return report_path


def summarize(report: dict[str, Any], report_path: Path) -> str:
    lines = [
        f"[QUEUE]: {report['status']} {report['task_id']} - {report['title']}",
        f"Report: {rel(report_path)}",
        "",
        "Executed workers:",
    ]
    for stage in report["stages"]:
        mark = "OK" if stage.get("ok") and not stage.get("skipped") else "SKIP" if stage.get("ok") else "FAIL"
        path_text = f" ({stage['path']})" if stage.get("path") else ""
        lines.append(f"  {mark} {stage['stage']}{path_text} in {stage.get('elapsed_ms', 0)}ms")
        detail = (stage.get("error") or stage.get("stderr") or stage.get("stdout") or "").strip()
        if detail:
            clipped = detail[:900] + ("\n...[truncated]" if len(detail) > 900 else "")
            lines.append("    " + clipped.replace("\n", "\n    "))
    return "\n".join(lines)


def add_task(args: argparse.Namespace) -> int:
    queue = load_queue()
    if any(t["id"] == args.theorem_id for t in queue["queue"]):
        print(f"[ERROR]: Theorem {args.theorem_id} already exists in queue.", file=sys.stderr)
        return 2

    PROOF_DIR.mkdir(parents=True, exist_ok=True)
    task_id = safe_id(args.theorem_id)
    lean_path = PROOF_DIR / f"{task_id}.lean"
    sympy_path = PROOF_DIR / f"{task_id}.sp"

    if args.lean_code:
        lean_path.write_text(args.lean_code)
    if args.lean_file:
        lean_path.write_text(Path(args.lean_file).read_text())
    if args.sympy_code:
        sympy_path.write_text(args.sympy_code)
    if args.sympy_file:
        sympy_path.write_text(Path(args.sympy_file).read_text())

    task = {
        "id": args.theorem_id,
        "title": args.title,
        "status": "pending",
        "sympy_witness": bool(args.sympy_code or args.sympy_file),
        "lean_proof": bool(args.lean_code or args.lean_file),
        "external_ref": None,
    }
    if task["sympy_witness"]:
        task["sympy_path"] = rel(sympy_path)
    if task["lean_proof"]:
        task["lean_path"] = rel(lean_path)

    queue["queue"].append(task)
    save_queue(queue)
    print(json.dumps(task, indent=2, ensure_ascii=False))
    return 0


def status() -> int:
    queue = load_queue()
    counts: dict[str, int] = {}
    for task in queue["queue"]:
        counts[task["status"]] = counts.get(task["status"], 0) + 1
    print(json.dumps({"total": len(queue["queue"]), "counts": counts}, indent=2))
    return 0


def run_next() -> int:
    queue = load_queue()
    task = next((t for t in queue["queue"] if t["status"] == "pending"), None)
    if task is None:
        print("[QUEUE]: No pending theorems.")
        return 0

    task["status"] = "running"
    save_queue(queue)

    started = now_iso()
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
        futures = [executor.submit(run_researcher, task), executor.submit(run_algebraist, task)]
        grounding = [future.result() for future in concurrent.futures.as_completed(futures)]

    formalist = run_formalist(task)
    critic = run_critic(task)
    stages = grounding + [formalist, critic]
    ok = all(stage.get("ok") for stage in stages)
    task["status"] = "done" if ok else "failed"

    report = {
        "task_id": task["id"],
        "title": task["title"],
        "status": task["status"],
        "started_at": started,
        "finished_at": now_iso(),
        "stages": stages,
    }
    report_path = write_report(report)
    archivist = {
        "stage": "archivist",
        "ok": True,
        "path": rel(report_path),
        "elapsed_ms": 0,
        "stdout": f"Wrote {rel(report_path)}",
    }
    report["stages"].append(archivist)
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False))
    task["last_report"] = rel(report_path)
    save_queue(queue)

    print(summarize(report, report_path))
    return 0 if ok else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    add = sub.add_parser("add")
    add.add_argument("--theorem-id", required=True)
    add.add_argument("--title", required=True)
    add.add_argument("--sympy-code")
    add.add_argument("--sympy-file")
    add.add_argument("--lean-code")
    add.add_argument("--lean-file")

    sub.add_parser("status")
    sub.add_parser("run-next")

    args = parser.parse_args()
    if args.command == "add":
        return add_task(args)
    if args.command == "status":
        return status()
    if args.command == "run-next":
        return run_next()
    parser.error("unknown command")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
