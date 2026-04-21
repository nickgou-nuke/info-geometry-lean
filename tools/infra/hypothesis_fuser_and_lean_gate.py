#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _stamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _slug(text: str) -> str:
    s = re.sub(r"[^a-zA-Z0-9]+", "-", text.strip().lower()).strip("-")
    return s[:96] or "goal"


def _tokenize(text: str) -> set[str]:
    return set(re.findall(r"[A-Za-z0-9_]+", text.lower()))


def _iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                rows.append(row)
    return rows


def _read_goal(goal: str, goal_file: str) -> str:
    g = goal.strip()
    if goal_file:
        p = Path(goal_file).resolve()
        if not p.exists():
            raise FileNotFoundError(f"goal file not found: {p}")
        g = p.read_text(encoding="utf-8", errors="ignore").strip()
    if not g:
        raise SystemExit("goal is required (set --goal or --goal-file)")
    return g


def _extract_theorem_name(lean_code: str) -> str:
    m = re.search(r"\b(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)\b", lean_code)
    if not m:
        return ""
    return str(m.group(1)).strip()


def _preferred_target_name(row: dict[str, Any]) -> str:
    target_source = str(row.get("target_source", "")).strip().lower()
    target_name = str(row.get("target_name", "")).strip()
    if target_source == "compiled_decl" and target_name:
        return target_name
    return target_name or _extract_theorem_name(str(row.get("lean_code", "")))


def _score_row(row: dict[str, Any], *, goal_tokens: set[str]) -> tuple[float, dict[str, float]]:
    status = str(row.get("status", "")).strip()
    if status and status != "ok":
        return (-10.0, {"status_penalty": -10.0})

    model_role = str(row.get("model_role", "")).strip().lower()
    lean_code = str(row.get("lean_code", "")).strip()
    response = str(row.get("response", "")).strip()
    target_source = str(row.get("target_source", "")).strip().lower()

    score_parts: dict[str, float] = {}
    score_parts["base"] = 0.0
    score_parts["has_lean_code"] = 2.0 if lean_code else -1.5
    score_parts["model_role"] = 0.8 if model_role == "tuned" else 0.35

    code_tokens = _tokenize(lean_code) if lean_code else _tokenize(response)
    if goal_tokens and code_tokens:
        overlap = len(goal_tokens & code_tokens)
        score_parts["goal_overlap"] = min(1.2, overlap * 0.08)
    else:
        score_parts["goal_overlap"] = 0.0

    lc = response.lower()
    score_parts["bridge_hint"] = 0.35 if any(k in lc for k in ("bridge", "intertwiner", "obstruction", "nonstandard")) else 0.0
    score_parts["compiled_target_preference"] = 0.5 if target_source == "compiled_decl" else 0.0

    line_count = len([ln for ln in lean_code.splitlines() if ln.strip()])
    if line_count == 0:
        score_parts["length_shape"] = -0.8
    elif line_count < 4:
        score_parts["length_shape"] = -0.2
    elif line_count <= 160:
        score_parts["length_shape"] = 0.4
    else:
        score_parts["length_shape"] = -0.3

    total = sum(score_parts.values())
    return (float(total), score_parts)


def _compile_candidate(
    *,
    lean_file: Path,
    timeout_sec: int,
) -> dict[str, Any]:
    cmd = ["lake", "env", "lean", str(lean_file)]
    try:
        proc = subprocess.run(
            cmd,
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            timeout=max(10, int(timeout_sec)),
            check=False,
        )
        stderr = (proc.stderr or "").strip()
        stdout = (proc.stdout or "").strip()
        return {
            "ok": proc.returncode == 0,
            "returncode": int(proc.returncode),
            "command": cmd,
            "stdout_head": "\n".join(stdout.splitlines()[:60]),
            "stderr_head": "\n".join(stderr.splitlines()[:80]),
        }
    except subprocess.TimeoutExpired:
        return {
            "ok": False,
            "returncode": 124,
            "command": cmd,
            "stdout_head": "",
            "stderr_head": "timeout",
        }


def _write_skill(
    *,
    out_dir: Path,
    run_id: str,
    goal: str,
    candidate: dict[str, Any],
    rank: int,
) -> tuple[str, str]:
    hypothesis_id = str(candidate.get("hypothesis_id", "")).strip() or f"hyp-r{rank}"
    short = re.sub(r"[^A-Za-z0-9_-]+", "-", hypothesis_id).strip("-")[:48] or f"hyp-r{rank}"
    name = f"generated-lean-hypothesis-{short}"
    file_name = f"{run_id}-{short}.md"
    out_path = out_dir / file_name
    theorem_name = _extract_theorem_name(str(candidate.get("lean_code", "")))
    preferred_name = _preferred_target_name(candidate)
    content = (
        f"---\n"
        f"name: {name}\n"
        f"description: Generated Lean4 hypothesis skill from compile-passing candidate.\n"
        f"---\n\n"
        f"# Generated Lean Hypothesis Skill\n\n"
        f"Goal:\n"
        f"- {goal}\n\n"
        f"Candidate:\n"
        f"- hypothesis_id: `{hypothesis_id}`\n"
        f"- model_role: `{candidate.get('model_role', '')}`\n"
        f"- theorem_name: `{preferred_name or theorem_name or 'unknown'}`\n"
        f"- target_source: `{candidate.get('target_source', '')}`\n\n"
        f"Lean sketch:\n\n"
        f"```lean\n{str(candidate.get('lean_code', '')).strip()}\n```\n\n"
        f"Execution:\n"
        f"1. Insert or adapt theorem in target module.\n"
        f"2. Run `lake env lean <file>` locally.\n"
        f"3. If stable, run `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <module>`.\n"
        f"4. Keep nonstandard repo-specific structure; do not normalize away unusual links.\n"
    )
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path.write_text(content, encoding="utf-8")
    return name, str(out_path)


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Fuse hypotheses from dual_hypothesis_sampler, rank them, run Lean compile gate, "
            "and optionally emit generated Hermes skill templates for accepted candidates."
        )
    )
    ap.add_argument("--input", required=True, help="Sampler output JSONL.")
    ap.add_argument("--goal", default="", help="Goal text (used for ranking features).")
    ap.add_argument("--goal-file", default="", help="Optional goal text file.")
    ap.add_argument("--top-k", type=int, default=8, help="Candidates to send to Lean gate.")
    ap.add_argument("--max-pass", type=int, default=2, help="Max accepted candidates retained.")
    ap.add_argument("--compile-timeout-sec", type=int, default=120)
    ap.add_argument("--skip-lean-gate", action="store_true")
    ap.add_argument("--strict-check", action="store_true", help="Run scripts/quality/strict-check.sh if any candidate passes.")

    ap.add_argument("--lean-import", default="import InfoGeometry.All")
    ap.add_argument("--lean-preamble", default="")
    ap.add_argument("--out", default="")
    ap.add_argument("--rows-out", default="")
    ap.add_argument("--gate-dir", default="")

    ap.add_argument("--emit-skills", action="store_true")
    ap.add_argument("--skill-out-dir", default="quarantine/hermes_skills/generated")
    ap.add_argument("--skill-index", default="quarantine/hermes_memory/generated_skills.jsonl")
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    input_path = Path(args.input).resolve()
    if not input_path.exists():
        raise FileNotFoundError(f"input not found: {input_path}")

    goal = _read_goal(args.goal, args.goal_file)
    goal_tokens = _tokenize(goal)
    run_id = _stamp()
    rows = _iter_jsonl(input_path)
    if not rows:
        raise RuntimeError("no rows loaded from sampler output")

    scored: list[dict[str, Any]] = []
    for row in rows:
        fused_score, parts = _score_row(row, goal_tokens=goal_tokens)
        rr = dict(row)
        rr["fuser"] = {
            "score": fused_score,
            "parts": parts,
        }
        scored.append(rr)
    scored.sort(key=lambda r: float(r.get("fuser", {}).get("score", -9999.0)), reverse=True)
    for rank, row in enumerate(scored, start=1):
        row.setdefault("fuser", {})
        row["fuser"]["rank"] = rank

    gated = scored[: max(0, int(args.top_k))]
    gate_dir = Path(args.gate_dir).resolve() if args.gate_dir else (REPO_ROOT / "reports" / "training" / "hypothesis" / "gate" / run_id)
    gate_dir.mkdir(parents=True, exist_ok=True)

    accepted: list[dict[str, Any]] = []
    gate_results: list[dict[str, Any]] = []
    for row in gated:
        lean_code = str(row.get("lean_code", "")).strip()
        if not lean_code:
            gate_result = {
                "ok": False,
                "returncode": 2,
                "command": [],
                "stderr_head": "missing lean_code",
                "stdout_head": "",
            }
            row["lean_gate"] = gate_result
            gate_results.append(row)
            continue

        hyp_id = str(row.get("hypothesis_id", "")).strip() or f"rank-{row.get('fuser', {}).get('rank', 0)}"
        lean_file = gate_dir / f"{hyp_id}.lean"
        preamble = str(args.lean_preamble).strip()
        payload = f"{args.lean_import.strip()}\n\n{preamble}\n\n{lean_code}\n"
        lean_file.write_text(payload, encoding="utf-8")

        if args.skip_lean_gate:
            gate_result = {
                "ok": True,
                "returncode": 0,
                "command": [],
                "stderr_head": "",
                "stdout_head": "skip-lean-gate",
            }
        else:
            gate_result = _compile_candidate(lean_file=lean_file, timeout_sec=args.compile_timeout_sec)

        row["lean_gate"] = gate_result
        row["lean_gate"]["lean_file"] = str(lean_file)
        gate_results.append(row)
        if gate_result.get("ok"):
            accepted.append(row)

    if int(args.max_pass) > 0:
        accepted = accepted[: int(args.max_pass)]

    strict_check_result: dict[str, Any] = {"ran": False, "ok": True, "returncode": 0, "stderr_head": "", "stdout_head": ""}
    if args.strict_check and accepted:
        proc = subprocess.run(
            ["bash", "scripts/quality/strict-check.sh"],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        strict_check_result = {
            "ran": True,
            "ok": proc.returncode == 0,
            "returncode": int(proc.returncode),
            "stderr_head": "\n".join((proc.stderr or "").splitlines()[:80]),
            "stdout_head": "\n".join((proc.stdout or "").splitlines()[:80]),
        }

    emitted_skills: list[dict[str, str]] = []
    if args.emit_skills and accepted:
        skill_out_dir = Path(args.skill_out_dir).resolve()
        skill_index = Path(args.skill_index).resolve()
        skill_index.parent.mkdir(parents=True, exist_ok=True)
        with skill_index.open("a", encoding="utf-8") as idx:
            for rank, row in enumerate(accepted, start=1):
                skill_name, skill_path = _write_skill(
                    out_dir=skill_out_dir,
                    run_id=run_id,
                    goal=goal,
                    candidate=row,
                    rank=rank,
                )
                skill_row = {
                    "created_at": _utc_now(),
                    "run_id": run_id,
                    "skill_name": skill_name,
                    "skill_path": skill_path,
                    "hypothesis_id": str(row.get("hypothesis_id", "")),
                    "model_role": str(row.get("model_role", "")),
                    "fuser_score": float(row.get("fuser", {}).get("score", 0.0)),
                    "lean_file": str(row.get("lean_gate", {}).get("lean_file", "")),
                }
                idx.write(json.dumps(skill_row, ensure_ascii=True) + "\n")
                emitted_skills.append({"name": skill_name, "path": skill_path})

    out = Path(args.out).resolve() if args.out else (REPO_ROOT / "reports" / "training" / "hypothesis" / f"{run_id}-fused-gated.json")
    rows_out = Path(args.rows_out).resolve() if args.rows_out else (REPO_ROOT / "reports" / "training" / "hypothesis" / f"{run_id}-fused-gated.rows.jsonl")
    out.parent.mkdir(parents=True, exist_ok=True)
    rows_out.parent.mkdir(parents=True, exist_ok=True)

    with rows_out.open("w", encoding="utf-8") as handle:
        for row in gate_results:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")

    report = {
        "schema": "lean.hypothesis.fuser_gate.report.v1",
        "run_id": run_id,
        "created_at": _utc_now(),
        "input": str(input_path),
        "goal": goal,
        "params": {
            "top_k": int(args.top_k),
            "max_pass": int(args.max_pass),
            "compile_timeout_sec": int(args.compile_timeout_sec),
            "skip_lean_gate": bool(args.skip_lean_gate),
            "strict_check": bool(args.strict_check),
            "emit_skills": bool(args.emit_skills),
        },
        "counts": {
            "input_rows": len(rows),
            "gated_rows": len(gated),
            "accepted_rows": len(accepted),
            "rejected_rows": max(0, len(gated) - len(accepted)),
        },
        "strict_check": strict_check_result,
        "accepted": accepted,
        "emitted_skills": emitted_skills,
        "rows_out": str(rows_out),
    }
    out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")

    print(f"fuser report: {out}")
    print(f"fuser rows:   {rows_out}")
    print(
        f"counts: input={report['counts']['input_rows']} "
        f"gated={report['counts']['gated_rows']} "
        f"accepted={report['counts']['accepted_rows']} "
        f"skills={len(emitted_skills)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
