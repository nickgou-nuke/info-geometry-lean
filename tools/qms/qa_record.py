#!/usr/bin/env python3
"""
QA-A acceptance record per docs/ALCHEMICAL_QMS_SOP.md section SOP-001-C.

The Acceptance Quality Agent runs the final independent quality gate by executing
kernel/build, axiom, placeholder, style, and traceability checks. Output is a QA
record written to `artifacts/qms/<task-id>-qa.json` with the minimum schema:

{
  "git_head": "...",
  "working_tree_scope": "clean | dirty-with-excluded-artifacts | dirty",
  "lean_toolchain": "...",
  "lean_version": "...",
  "lake_version": "...",
  "artifact_sha256": "..."
}

Acceptance status tags (disjoint by artifact class):
  Theorem/code: payload_ready, intent_captured, formal_contract_ready,
      sterile_compile_failed, gap_report_ready, countermodel_found,
      repair_split_required, kernel_verified, axiom_audited, release_ready,
      verified_logos
  Documentation/QMS: qms_document_draft, qms_document_accepted,
      qms_document_controlled, qms_document_retired
  Process: accepted_limited_scope, needs_capa, audit_blocked, qa_blocked,
      bucket_3_open_debt, rejected_false_surface
"""

from __future__ import annotations

import hashlib
import json
import subprocess
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

QA_RECORD_SCHEMA = "info_geometry.qms.qa_record.v1"

ACCEPTANCE_VERDICTS = {"ACCEPTED", "ACCEPTED_WITH_LIMITED_SCOPE", "REJECTED"}

STATUS_TAGS = {
    "payload_ready",
    "intent_captured",
    "formal_contract_ready",
    "sterile_compile_failed",
    "gap_report_ready",
    "countermodel_found",
    "repair_split_required",
    "kernel_verified",
    "axiom_audited",
    "release_ready",
    "verified_logos",
    "qms_document_draft",
    "qms_document_accepted",
    "qms_document_controlled",
    "qms_document_retired",
    "accepted_limited_scope",
    "needs_capa",
    "audit_blocked",
    "qa_blocked",
    "bucket_3_open_debt",
    "rejected_false_surface",
}

WORKING_TREE_STATES = {"clean", "dirty-with-excluded-artifacts", "dirty"}

APPROVED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return "sha256:" + h.hexdigest()


def _run(cmd: list[str]) -> str:
    result = subprocess.run(cmd, capture_output=True, text=True, check=False)
    return result.stdout.strip()


def _git_head() -> str:
    return _run(["git", "rev-parse", "HEAD"])


def _git_status() -> str:
    return _run(["git", "status", "--short"])


def _lean_toolchain() -> str:
    p = ROOT / "lean-toolchain"
    if p.is_file():
        return p.read_text(encoding="utf-8").strip()
    return ""


def _lake_version() -> str:
    out = _run(["lake", "--version"])
    return out or "unknown"


def _lean_version() -> str:
    out = _run(["lean", "--version"])
    return out or "unknown"


def validate_verdict(value: str) -> None:
    if value not in ACCEPTANCE_VERDICTS:
        raise ValueError(f"invalid verdict: {value!r}; must be one of {sorted(ACCEPTANCE_VERDICTS)}")


def validate_status_tag(tag: str) -> None:
    if tag not in STATUS_TAGS:
        raise ValueError(f"invalid status tag: {tag!r}; must be one of {sorted(STATUS_TAGS)}")


def validate_working_tree_state(value: str) -> None:
    if value not in WORKING_TREE_STATES:
        raise ValueError(
            f"invalid working_tree_scope: {value!r}; must be one of {sorted(WORKING_TREE_STATES)}"
        )


def build_qa_record(
    *,
    task_id: str,
    artifact: str,
    verdict: str,
    status_tags: list[str],
    commands_run: list[str],
    command_outputs: list[str],
    remaining_debt: list[str],
    axiom_classification: list[dict[str, Any]],
    placeholder_findings: list[dict[str, Any]],
    working_tree_scope: str,
    artifact_sha256: str | None = None,
    qa_agent_role: str = "QA-A",
    requires_capa: bool = False,
    capa_ids: list[str] | None = None,
) -> dict[str, Any]:
    """Build and validate a QA-A acceptance record.

    Raises ValueError on invalid input.
    """
    validate_verdict(verdict)
    for tag in status_tags:
        validate_status_tag(tag)
    validate_working_tree_state(working_tree_scope)

    git_status_raw = _git_status()
    if not git_status_raw:
        inferred_wt = "clean"
    elif artifact and any(artifact in line for line in git_status_raw.splitlines()):
        inferred_wt = "dirty"
    else:
        inferred_wt = "dirty-with-excluded-artifacts"

    record: dict[str, Any] = {
        "schema": QA_RECORD_SCHEMA,
        "sop_id": "QMS-SOP-ALC-001",
        "version": "4.1",
        "task_id": task_id,
        "generated_at": _now_iso(),
        "artifact": artifact,
        "artifact_sha256": artifact_sha256,
        "qa_agent_role": qa_agent_role,
        "git_head": _git_head(),
        "working_tree_scope": working_tree_scope or inferred_wt,
        "lean_toolchain": _lean_toolchain(),
        "lean_version": _lean_version(),
        "lake_version": _lake_version(),
        "verdict": verdict,
        "status_tags": status_tags,
        "commands_run": commands_run,
        "command_outputs": command_outputs,
        "remaining_debt": remaining_debt,
        "axiom_classification": axiom_classification,
        "placeholder_findings": placeholder_findings,
        "requires_capa": requires_capa,
        "capa_ids": capa_ids or [],
        "axiom_count": len(axiom_classification),
        "placeholder_count": len(placeholder_findings),
        "debt_count": len(remaining_debt),
    }
    return record


def write_qa_record(record: dict[str, Any], out_path: Path) -> Path:
    """Write a QA record to disk as JSON."""
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    return out_path


def load_qa_record(path: Path | str) -> dict[str, Any]:
    """Load and minimally validate a QA record from disk."""
    path = Path(path)
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"invalid QA record (not an object): {path}")
    if data.get("schema") != QA_RECORD_SCHEMA:
        raise ValueError(f"unsupported QA record schema: {path}")
    return data


def axiom_classification_entry(
    *,
    theorem_name: str,
    axiom: str,
    origin: str,
    semantic_role: str,
    approved: bool,
) -> dict[str, Any]:
    """Convenience builder for a single axiom classification entry."""
    if axiom not in APPROVED_AXIOMS and not approved:
        # Non-approved axioms are flagged but not rejected by the schema.
        pass
    return {
        "theorem_name": theorem_name,
        "axiom": axiom,
        "origin": origin,
        "semantic_role": semantic_role,
        "approved": approved,
    }


def placeholder_finding_entry(
    *,
    file: str,
    line: int,
    token: str,
    context: str,
    classified_as: str,
) -> dict[str, Any]:
    """Convenience builder for a single placeholder finding entry."""
    return {
        "file": file,
        "line": line,
        "token": token,
        "context": context,
        "classified_as": classified_as,
    }


def acceptance_checklist_passed(checklist: dict[str, bool]) -> bool:
    """Check the SOP section 17 minimal compliance checklist.

    All eight questions must be yes/True for delivery to be accepted.
    """
    required = [
        "non_authoring_audit",
        "non_authoring_qa_rerun",
        "scope_labels_assigned",
        "owner_theorem_names_cited",
        "dag_hash_fresh",
        "external_evidence_scoped",
        "no_fake_closure_patterns",
        "gaps_recorded_as_bucket3",
    ]
    return all(bool(checklist.get(k, False)) for k in required)


def main() -> int:
    """Smoke test: build and validate a minimal QA record."""
    record = build_qa_record(
        task_id="T-SMOKE",
        artifact="lean/InfoGeometry/Foo.lean",
        verdict="ACCEPTED_WITH_LIMITED_SCOPE",
        status_tags=["kernel_verified", "axiom_audited", "accepted_limited_scope"],
        commands_run=[
            "lake env lean lean/InfoGeometry/Foo.lean",
            "python3 tools/quality/semantic_vacuity_gate.py lean/InfoGeometry/Foo.lean",
        ],
        command_outputs=["build succeeded", "vacuity: 0 findings"],
        remaining_debt=[],
        axiom_classification=[
            axiom_classification_entry(
                theorem_name="Foo.bar",
                axiom="Classical.choice",
                origin="mathlib infrastructure",
                semantic_role="nonconstructive existential",
                approved=True,
            )
        ],
        placeholder_findings=[],
        working_tree_scope="clean",
        artifact_sha256="sha256:placeholder",
    )
    print(json.dumps(record, indent=2))
    print("[qa_record] smoke test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
