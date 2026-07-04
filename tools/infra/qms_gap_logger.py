#!/usr/bin/env python3
from __future__ import annotations

"""QMS stage-2 gap logger for isolated Lean payloads."""

import argparse
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.pathing import normalize_user_path, repo_root
from tools.quality import audit_constructivity

ROOT = repo_root()
LEAN_TOOLCHAIN = "leanprover/lean4:v4.28.0"
DIAG_RE = re.compile(
    r"^(?P<path>.*?):(?P<line>\d+):(?P<col>\d+): (?P<kind>error|warning)(?:\([^)]*\))?: (?P<msg>.*)$"
)
PLACEHOLDER_RE = re.compile(r"(?<!\w)(sorry|admit|axiom)(?!\w)")
TYPE_1_PATTERNS = (
    "failed to synthesize",
    "type mismatch",
    "unknown identifier",
    "stuck",
    "no instance",
    "instance problem",
    "failed to infer",
)
TYPE_2_PATTERNS = (
    "unsolved goals",
    "goal is not trivial",
    "cannot prove",
    "failed to prove",
    "rewrite tactic failed",
    "tactic 'simp' failed",
    "ring_nf",
    "linarith",
    "omega",
)
TYPE_3_PATTERNS = (
    "induction hypothesis",
    "structural recursion",
    "termination",
    "recursor",
    "motive",
    "equation compiler",
)


@dataclass(frozen=True)
class GapFinding:
    gap_type: str
    path: str
    line: int | None
    col: int | None
    message: str
    rationale: str
    evidence: str
    counter_model_attempt: dict[str, Any]


def sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def rel(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def classify_gap(message: str) -> tuple[str, str]:
    lower = message.lower()
    if any(token in lower for token in TYPE_1_PATTERNS):
        return ("gap_type_1", "type mismatch or missing typeclass instance")
    if any(token in lower for token in TYPE_3_PATTERNS):
        return ("gap_type_3", "structural divergence or induction mismatch")
    if any(token in lower for token in TYPE_2_PATTERNS):
        return ("gap_type_2", "unproven side-condition or auxiliary-lemma gap")
    return ("gap_type_2", "unclassified Lean diagnostic; treated as auxiliary-lemma gap")


def scan_placeholders(text: str) -> list[dict[str, Any]]:
    stripped = audit_constructivity.strip_comments(text, strip_strings=False, strip_quoted_identifiers=False)
    hits: list[dict[str, Any]] = []
    for lineno, line in enumerate(stripped.splitlines(), start=1):
        for match in PLACEHOLDER_RE.finditer(line):
            hits.append({
                "line": lineno,
                "token": match.group(1),
            })
    return hits


def parse_diagnostics(output: str) -> list[dict[str, Any]]:
    diags: list[dict[str, Any]] = []
    for raw in output.splitlines():
        match = DIAG_RE.match(raw)
        if not match:
            continue
        diags.append({
            "path": match.group("path"),
            "line": int(match.group("line")),
            "col": int(match.group("col")),
            "kind": match.group("kind"),
            "message": match.group("msg"),
        })
    return diags


def run_lean(target: Path, *, timeout: int) -> tuple[int, str]:
    proc = subprocess.run(
        ["lake", "env", "lean", str(target)],
        cwd=str(ROOT),
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )
    output = "\n".join(part for part in [proc.stdout, proc.stderr] if part)
    return proc.returncode, output


def build_counter_model_attempt(gap: GapFinding) -> dict[str, Any]:
    return {
        "status": "not_implemented",
        "reason": "No semantic model synthesizer is wired into the mock QMS logger.",
        "gap_type": gap.gap_type,
        "attempted": False,
    }


def make_report(
    *,
    target: Path,
    rc: int,
    output: str,
    timeout: int,
) -> dict[str, Any]:
    text = target.read_text(encoding="utf-8")
    placeholders = scan_placeholders(text)
    diags = parse_diagnostics(output)
    gaps: list[GapFinding] = []
    for diag in diags:
        if diag["kind"] != "error":
            continue
        gap_type, rationale = classify_gap(diag["message"])
        gap = GapFinding(
            gap_type=gap_type,
            path=diag["path"],
            line=diag["line"],
            col=diag["col"],
            message=diag["message"],
            rationale=rationale,
            evidence=f"{diag['path']}:{diag['line']}:{diag['col']}",
            counter_model_attempt={},
        )
        gaps.append(GapFinding(
            gap_type=gap.gap_type,
            path=gap.path,
            line=gap.line,
            col=gap.col,
            message=gap.message,
            rationale=gap.rationale,
            evidence=gap.evidence,
            counter_model_attempt=build_counter_model_attempt(gap),
        ))

    placeholder_count = len(placeholders)
    gap_counts = {
        "gap_type_1": sum(1 for g in gaps if g.gap_type == "gap_type_1"),
        "gap_type_2": sum(1 for g in gaps if g.gap_type == "gap_type_2"),
        "gap_type_3": sum(1 for g in gaps if g.gap_type == "gap_type_3"),
    }
    status = "clean" if rc == 0 and not gaps and placeholder_count == 0 else "findings"
    if rc != 0 and not gaps:
        status = "blocked"

    return {
        "schema": "info_geometry.qms_gap_report.v1",
        "tool": "qms_gap_logger",
        "toolchain": LEAN_TOOLCHAIN,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "target": {
            "path": rel(target),
            "module_hint": target.stem,
            "source_hash": sha256_text(text),
        },
        "command": ["lake", "env", "lean", rel(target)],
        "exit_code": rc,
        "status": status,
        "timeout_s": timeout,
        "placeholder_scan": {
            "count": placeholder_count,
            "hits": placeholders,
        },
        "diagnostics": diags,
        "gaps": [
            {
                **{
                    "gap_type": g.gap_type,
                    "path": g.path,
                    "line": g.line,
                    "col": g.col,
                    "message": g.message,
                    "rationale": g.rationale,
                    "evidence": g.evidence,
                },
                "counter_model_attempt": g.counter_model_attempt,
            }
            for g in gaps
        ],
        "summary": {
            "diagnostic_count": len(diags),
            "gap_count": len(gaps),
            **gap_counts,
        },
        "tails": {
            "output_tail": output[-6000:],
        },
        "audit_note": "Stage-2 audit only; no acceptance decision is emitted by this logger.",
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-file", required=True, help="Lean file to audit.")
    parser.add_argument(
        "--out",
        default="artifacts/qms_sop_alc_001/audit_report.json",
        help="Destination JSON audit report.",
    )
    parser.add_argument("--timeout", type=int, default=120)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    target = normalize_user_path(args.lean_file, ROOT / "lean" / "InfoGeometry" / "Physics" / "CentralizerInvariance.lean")
    if not target.exists():
        print(f"ERROR: Lean file not found: {target}", file=sys.stderr)
        return 2

    rc, output = run_lean(target, timeout=args.timeout)
    report = make_report(target=target, rc=rc, output=output, timeout=args.timeout)

    out_path = normalize_user_path(args.out, ROOT / "artifacts" / "qms_sop_alc_001" / "audit_report.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"audit_report": rel(out_path), "status": report["status"], "gap_count": report["summary"]["gap_count"]}, ensure_ascii=False))
    return 0 if report["status"] == "clean" else 1


if __name__ == "__main__":
    raise SystemExit(main())
