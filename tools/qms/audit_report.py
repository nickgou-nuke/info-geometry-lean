#!/usr/bin/env python3
"""
A-A audit telemetry per docs/ALCHEMICAL_QMS_SOP.md section SOP-001-B.

The Audit Agent independently reads the generated artifact and relevant owner
files, classifies gaps, and recommends CAPA. Output is an audit report written
to `artifacts/qms/<task-id>-audit_report.json` with the minimum schema:

{
  "task_id": "...",
  "artifact": "...",
  "verdict": "PASS | REQUEST_CHANGES | REJECT",
  "files_read": [],
  "commands_run": [],
  "gaps": [],
  "capa": [],
  "scope_label": "..."
}

Gap taxonomy (SOP-001-B step 4):
  - G1: syntax, parser, or elaboration failure
  - G2: type mismatch, missing typeclass instance, universe problem, import/API mismatch
  - G3: missing algebraic lemma, unproved side condition, missing rewrite theorem
  - G4: false target, vacuous target, quotient collapse, countermodel found,
        theorem strength beyond owner authority
  - G5: scope pollution or import-dependent success (undeclared broad imports,
        namespace leakage, accidental instance availability)
"""

from __future__ import annotations

import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
else:
    from tools.pathing import repo_root

ROOT = repo_root()

VERDICTS = {"PASS", "REQUEST_CHANGES", "REJECT"}

GAP_CODES = {"G1", "G2", "G3", "G4", "G5"}

SCOPE_LABELS = {
    "finite-stage",
    "finite-iteration",
    "direct-limit",
    "categorical-colimit",
    "inverse-limit",
    "topological",
    "analytic",
    "external-evidence",
    "open-debt",
}

AUDIT_REPORT_SCHEMA = "info_geometry.qms.audit_report.v1"


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return "sha256:" + h.hexdigest()


def validate_verdict(value: str) -> None:
    if value not in VERDICTS:
        raise ValueError(f"invalid verdict: {value!r}; must be one of {sorted(VERDICTS)}")


def validate_gap_code(code: str) -> None:
    if code not in GAP_CODES:
        raise ValueError(f"invalid gap code: {code!r}; must be one of {sorted(GAP_CODES)}")


def validate_scope_label(label: str) -> None:
    if label not in SCOPE_LABELS:
        raise ValueError(f"invalid scope label: {label!r}; must be one of {sorted(SCOPE_LABELS)}")


def build_audit_report(
    *,
    task_id: str,
    artifact: str,
    verdict: str,
    files_read: list[str],
    commands_run: list[str],
    gaps: list[dict[str, Any]],
    capa: list[dict[str, Any]],
    scope_label: str,
    artifact_sha256: str | None = None,
    audit_agent_role: str = "A-A",
    nonconformance_table: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Build and validate an A-A audit report.

    Each gap entry must have at minimum:
      - "code": one of G1-G5
      - "description": human-readable gap description
      - "file": source file path (may be empty for cross-cutting gaps)
      - "line": 1-based line number (0 if not applicable)
      - "severity": "error" | "warning" | "advisory"

    Each capa entry must have at minimum:
      - "nonconformance_id": unique CAPA ID
      - "finding": description of the nonconformance
      - "root_cause": root cause analysis
      - "corrective_action": action to correct
      - "preventive_action": action to prevent recurrence
      - "verification_command": command to verify the fix
      - "closure_status": "open" | "closed" | "verified"
    """
    validate_verdict(verdict)
    validate_scope_label(scope_label)

    for gap in gaps:
        validate_gap_code(gap.get("code", ""))
        for required in ("description", "file", "line", "severity"):
            if required not in gap:
                raise ValueError(f"gap entry missing required field: {required}")

    for c in capa:
        for required in (
            "nonconformance_id",
            "finding",
            "root_cause",
            "corrective_action",
            "preventive_action",
            "verification_command",
            "closure_status",
        ):
            if required not in c:
                raise ValueError(f"CAPA entry missing required field: {required}")

    report: dict[str, Any] = {
        "schema": AUDIT_REPORT_SCHEMA,
        "sop_id": "QMS-SOP-ALC-001",
        "version": "4.1",
        "task_id": task_id,
        "generated_at": _now_iso(),
        "artifact": artifact,
        "artifact_sha256": artifact_sha256,
        "audit_agent_role": audit_agent_role,
        "verdict": verdict,
        "files_read": files_read,
        "commands_run": commands_run,
        "gaps": gaps,
        "capa": capa,
        "scope_label": scope_label,
        "nonconformance_table": nonconformance_table or [],
        "gap_count": len(gaps),
        "error_gap_count": sum(1 for g in gaps if g.get("severity") == "error"),
        "capa_count": len(capa),
        "open_capa_count": sum(1 for c in capa if c.get("closure_status") == "open"),
    }

    return report


def write_audit_report(report: dict[str, Any], out_path: Path) -> Path:
    """Write an audit report to disk as JSON."""
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return out_path


def load_audit_report(path: Path | str) -> dict[str, Any]:
    """Load and minimally validate an audit report from disk."""
    path = Path(path)
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"invalid audit report (not an object): {path}")
    if data.get("schema") != AUDIT_REPORT_SCHEMA:
        raise ValueError(f"unsupported audit report schema: {path}")
    required = (
        "task_id",
        "artifact",
        "artifact_sha256",
        "audit_agent_role",
        "verdict",
        "files_read",
        "commands_run",
        "gaps",
        "capa",
        "scope_label",
    )
    missing = [key for key in required if key not in data]
    if missing:
        raise ValueError(f"audit report missing required fields: {', '.join(missing)}")
    try:
        validate_verdict(data["verdict"])
        validate_scope_label(data["scope_label"])
    except (TypeError, ValueError) as exc:
        raise ValueError(f"invalid audit report fields: {exc}") from exc
    if not all(isinstance(data[key], list) for key in ("files_read", "commands_run", "gaps", "capa")):
        raise ValueError("invalid audit report: files_read, commands_run, gaps, and capa must be lists")
    return data


def gap_entry(
    *,
    code: str,
    description: str,
    file: str = "",
    line: int = 0,
    severity: str = "error",
    evidence: str | None = None,
) -> dict[str, Any]:
    """Convenience builder for a single gap entry."""
    validate_gap_code(code)
    if severity not in {"error", "warning", "advisory"}:
        raise ValueError(f"invalid severity: {severity!r}")
    entry: dict[str, Any] = {
        "code": code,
        "description": description,
        "file": file,
        "line": line,
        "severity": severity,
    }
    if evidence:
        entry["evidence"] = evidence
    return entry


def capa_entry(
    *,
    nonconformance_id: str,
    finding: str,
    root_cause: str,
    corrective_action: str,
    preventive_action: str,
    verification_command: str,
    closure_status: str = "open",
) -> dict[str, Any]:
    """Convenience builder for a single CAPA entry."""
    if closure_status not in {"open", "closed", "verified"}:
        raise ValueError(f"invalid closure_status: {closure_status!r}")
    return {
        "nonconformance_id": nonconformance_id,
        "finding": finding,
        "root_cause": root_cause,
        "corrective_action": corrective_action,
        "preventive_action": preventive_action,
        "verification_command": verification_command,
        "closure_status": closure_status,
    }


def main() -> int:
    """Smoke test: build and validate a minimal audit report."""
    report = build_audit_report(
        task_id="T-SMOKE",
        artifact="lean/InfoGeometry/Foo.lean",
        verdict="REQUEST_CHANGES",
        files_read=["lean/InfoGeometry/Foo.lean"],
        commands_run=["python3 tools/quality/semantic_vacuity_gate.py lean/InfoGeometry/Foo.lean"],
        gaps=[
            gap_entry(
                code="G3",
                description="missing rewrite theorem for zornMul_comm",
                file="lean/InfoGeometry/Foo.lean",
                line=42,
                severity="error",
                evidence="goal state at tactic boundary shows unsolved zornMul_comm subgoal",
            )
        ],
        capa=[
            capa_entry(
                nonconformance_id="CAPA-T-SMOKE-001",
                finding="proof relies on unproved zornMul_comm lemma",
                root_cause="G-A assumed auxiliary lemma exists without owner search",
                corrective_action="prove zornMul_comm as auxiliary lemma or weaken theorem",
                preventive_action="require owner-first search before auxiliary lemma use",
                verification_command="lake build InfoGeometry.Algebra.ZornMatrix",
                closure_status="open",
            )
        ],
        scope_label="finite-stage",
    )
    print(json.dumps(report, indent=2))
    print("[audit_report] smoke test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
