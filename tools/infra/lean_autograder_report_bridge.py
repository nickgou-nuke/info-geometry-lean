#!/usr/bin/env python3
"""Normalize lean4-autograder-style result reports into Hive telemetry.

The Robert Y. Lewis Lean 4 autograder checks named proof/definition problems
and emits grading-style outcomes.  This bridge treats those results as scoring
telemetry for target/submission tasks, not as proof authority and not as a
replacement for build/SafeVerify/LeanParanoia gates.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.lean_autograder_report.v1"
SUMMARY_SCHEMA = "info_geometry.lean_autograder_report.summary.v1"


def stable_hash(payload: Any) -> str:
    text = json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    return hashlib.sha1(text.encode("utf-8")).hexdigest()


def iter_json_docs(path: Path) -> Iterable[tuple[Any, Path]]:
    if path.is_dir():
        for child in sorted(path.rglob("*.json")):
            yield from iter_json_docs(child)
        return
    if not path.exists() or path.suffix.lower() != ".json":
        return
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return
    if isinstance(payload, list):
        for row in payload:
            yield row, path
    else:
        yield payload, path


def _first(row: dict[str, Any], keys: tuple[str, ...], default: Any = None) -> Any:
    for key in keys:
        if key in row and row[key] is not None:
            return row[key]
    return default


def coerce_problem_rows(payload: Any) -> list[dict[str, Any]]:
    if isinstance(payload, list):
        return [row for row in payload if isinstance(row, dict)]
    if not isinstance(payload, dict):
        return []
    for key in ("problems", "results", "tests", "scores", "outcomes"):
        rows = payload.get(key)
        if isinstance(rows, list):
            return [row for row in rows if isinstance(row, dict)]
    if any(key in payload for key in ("name", "problem", "points", "earned", "passed", "status")):
        return [payload]
    return []


def normalize_problem(row: dict[str, Any], *, source_path: Path, index: int) -> dict[str, Any]:
    name = str(_first(row, ("name", "problem", "problemName", "decl", "declaration"), f"problem_{index}"))
    kind = str(_first(row, ("kind", "problemKind", "type"), "unknown"))
    max_points = float(_first(row, ("points", "maxPoints", "max_score", "scorePossible"), 0) or 0)
    earned = float(_first(row, ("earned", "score", "pointsEarned", "points_earned"), 0) or 0)
    status_raw = _first(row, ("status", "result", "passed"), None)
    if isinstance(status_raw, bool):
        passed = status_raw
        status = "passed" if passed else "failed"
    else:
        status = str(status_raw or "").lower()
        passed = status in {"pass", "passed", "success", "ok", "true"}
    return {
        "id": stable_hash(["autograder_problem", str(source_path), index, name, kind, earned, max_points, status]),
        "name": name,
        "kind": kind,
        "passed": passed,
        "status": status,
        "earned": earned,
        "points": max_points,
        "message": str(_first(row, ("message", "error", "feedback", "reason"), "")),
        "raw": row,
    }


def normalize_autograder_payload(payload: Any, source_path: Path) -> dict[str, Any]:
    problems = [
        normalize_problem(row, source_path=source_path, index=idx)
        for idx, row in enumerate(coerce_problem_rows(payload))
    ]
    total_points = sum(float(row["points"]) for row in problems)
    earned_points = sum(float(row["earned"]) for row in problems)
    row = {
        "schema": SCHEMA,
        "id": "",
        "source": "lean4_autograder",
        "source_path": str(source_path),
        "passed": bool(problems) and all(bool(row["passed"]) for row in problems),
        "problem_count": len(problems),
        "passed_count": sum(1 for row in problems if row["passed"]),
        "failed_count": sum(1 for row in problems if not row["passed"]),
        "earned_points": earned_points,
        "total_points": total_points,
        "problems": problems,
        "raw": payload,
        "authority": {
            "autograder_is_scoring_signal": True,
            "not_a_lean_proof_authority": True,
            "lean_remains_proof_authority": True,
            "promotion_requires_hive_gates": True,
        },
    }
    row["id"] = stable_hash(
        {
            "source_path": str(source_path),
            "problem_count": row["problem_count"],
            "passed_count": row["passed_count"],
            "earned_points": earned_points,
            "total_points": total_points,
        }
    )
    return row


def write_outputs(rows: list[dict[str, Any]], output_dir: Path, *, input_ref: str | None = None, command: list[str] | None = None) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    out = output_dir / "lean_autograder_report.jsonl"
    with out.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
    summary = {
        "schema": SUMMARY_SCHEMA,
        "input": input_ref,
        "output": str(out),
        "command": command or [],
        "records": len(rows),
        "problem_count": sum(int(row["problem_count"]) for row in rows),
        "passed_count": sum(int(row["passed_count"]) for row in rows),
        "failed_count": sum(int(row["failed_count"]) for row in rows),
        "earned_points": sum(float(row["earned_points"]) for row in rows),
        "total_points": sum(float(row["total_points"]) for row in rows),
    }
    (output_dir / "lean_autograder_report_summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return summary


def normalize_existing_reports(input_path: Path, output_dir: Path) -> dict[str, Any]:
    rows = [
        normalize_autograder_payload(payload, source_path)
        for payload, source_path in iter_json_docs(input_path)
    ]
    return write_outputs(rows, output_dir, input_ref=str(input_path))


def run_autograder(
    *,
    submission: Path,
    solutions: Path,
    output_dir: Path,
    repo_root: Path,
    autograder_cmd: str,
    local: bool = False,
    timeout: int = 120,
) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    raw_json = output_dir / "autograder_raw.json"
    command = [autograder_cmd]
    if local:
        command.append("--local")
    command.extend([str(submission), str(solutions)])
    proc = subprocess.run(
        command,
        cwd=repo_root,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )
    if raw_json.exists():
        rows = [normalize_autograder_payload(payload, source) for payload, source in iter_json_docs(raw_json)]
    else:
        rows = [
            normalize_autograder_payload(
                {
                    "problems": [
                        {
                            "name": "autograder_process",
                            "kind": "process",
                            "passed": proc.returncode == 0,
                            "earned": 1 if proc.returncode == 0 else 0,
                            "points": 1,
                            "message": (proc.stderr or proc.stdout or f"exit {proc.returncode}").strip(),
                        }
                    ],
                    "stdout": proc.stdout,
                    "stderr": proc.stderr,
                },
                raw_json,
            )
        ]
    (output_dir / "autograder_stdout.txt").write_text(proc.stdout, encoding="utf-8")
    (output_dir / "autograder_stderr.txt").write_text(proc.stderr, encoding="utf-8")
    return write_outputs(rows, output_dir, input_ref=f"{submission}::{solutions}", command=command)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--input", type=Path, help="Existing autograder JSON report or directory")
    mode.add_argument("--submission", type=Path, help="Submission Lean file; requires --solutions")
    parser.add_argument("--solutions", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--autograder-cmd", default=".lake/build/bin/autograder")
    parser.add_argument("--local", action="store_true")
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()
    if args.input:
        summary = normalize_existing_reports(args.input, args.output_dir)
    else:
        if not args.solutions:
            raise SystemExit("--solutions is required with --submission")
        summary = run_autograder(
            submission=args.submission,
            solutions=args.solutions,
            output_dir=args.output_dir,
            repo_root=args.repo_root,
            autograder_cmd=args.autograder_cmd,
            local=bool(args.local),
            timeout=args.timeout,
        )
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0 if int(summary["failed_count"]) == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
