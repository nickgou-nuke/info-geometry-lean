"""Adapt trusted Lean process output to existing Hive verification telemetry.

This parser is a policy boundary, not a kernel verifier or a signed certificate.
The caller owns subprocess provenance, import freshness, and specification review.
No worker, database, subprocess, or promotion is started here.
"""

from __future__ import annotations

import json
from typing import Any

from tools.infra.verification_contract import VerificationRecord


SCHEMA = "info_geometry.hive_epistemic_check.v1"
RECEIPT_SCHEMA = "info_geometry.hive_epistemic_admission.v1"
MARKER = "[hive-epistemic-admission] "


def check_admission_output(
    execution: dict[str, Any] | None,
    *,
    expected_declarations: list[str],
) -> dict[str, Any]:
    reasons: list[str] = []
    receipt: dict[str, Any] = {}
    expected_valid = (
        isinstance(expected_declarations, list)
        and bool(expected_declarations)
        and all(isinstance(name, str) and name for name in expected_declarations)
    )
    if not expected_valid or len(set(expected_declarations)) != len(expected_declarations):
        reasons.append("missing_or_duplicate_specification_targets")
    if not isinstance(execution, dict):
        execution = {}
    returncode = execution.get("returncode")
    if type(returncode) is not int or returncode != 0:
        reasons.append("lean_process_not_successful")
    stdout = execution.get("stdout")
    lines = [line for line in stdout.splitlines() if MARKER in line] if isinstance(stdout, str) else []
    if len(lines) != 1:
        reasons.append("missing_or_ambiguous_admission_receipt")
    else:
        try:
            candidate = json.loads(lines[0].split(MARKER, 1)[1])
            if isinstance(candidate, dict):
                receipt = candidate
        except (ValueError, TypeError):
            pass
        if receipt.get("schema") != RECEIPT_SCHEMA:
            reasons.append("invalid_admission_schema")
        if receipt.get("scheduler") != "finite_dependency_compiler":
            reasons.append("missing_certified_scheduler")
        if receipt.get("scope") != "current_kernel_environment":
            reasons.append("invalid_evidence_scope")
        if receipt.get("declarations") != expected_declarations:
            reasons.append("schedule_target_mismatch")
        reports = receipt.get("reports")
        if not isinstance(reports, list) or not reports or not all(isinstance(row, dict) for row in reports):
            reasons.append("missing_admission_reports")
        else:
            if [row.get("name") for row in reports] != expected_declarations:
                reasons.append("report_target_mismatch")
            if any(row.get("decision") != "admitted" or row.get("blockers") != [] for row in reports):
                reasons.append("qms_admission_blocked")
            if any(not isinstance(row.get("policyVersion"), str) or not row["policyVersion"] for row in reports):
                reasons.append("missing_policy_version")
    records = []
    if expected_valid:
        for name in expected_declarations:
            records.append(VerificationRecord(
                decl=name,
                module=str(execution.get("module") or ""),
                lane="hive_epistemic_compiler",
                ok=not reasons,
                severity=0 if not reasons else 2,
                checks=["process_exit", "schedule_targets", "native_admission_receipt"],
                reasons=list(reasons),
                evidence=[{"receipt": receipt}],
                provenance={"returncode": returncode, "scope": "current_kernel_environment"},
                authority_level="policy",
            ).to_payload())
    return {
        "schema": SCHEMA,
        "ok": not reasons,
        "reasons": reasons,
        "records": records,
        "promotion_allowed": False,
    }
