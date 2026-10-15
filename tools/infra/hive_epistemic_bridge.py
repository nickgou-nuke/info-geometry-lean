"""Adapt trusted Lean process output to existing Hive verification telemetry.

This parser is a policy boundary, not a kernel verifier or a signed certificate.
The caller owns subprocess provenance, import freshness, and specification review.
No worker, database, subprocess, or promotion is started here.
"""

from __future__ import annotations

import json
import re
from typing import Any

from tools.infra.verification_contract import VerificationRecord
from tools.infra.proof_artifact_receipt import verify_candidate_receipt


SCHEMA = "info_geometry.hive_epistemic_check.v1"
RECEIPT_SCHEMA = "info_geometry.hive_epistemic_admission.v1"
MARKER = "[hive-epistemic-admission] "


def validate_candidate_archive_record(record: dict[str, Any] | None) -> dict[str, Any]:
    """Validate a stored AutoMath receipt before a Hive consumer uses it.

    This checks record/receipt consistency and receipt integrity only. It does
    not re-run Lean, authenticate the writer, or allow promotion.
    """
    reasons: list[str] = []
    if not isinstance(record, dict):
        record = {}
        reasons.append("candidate_record_missing")
    if record.get("record_type") != "automath_lean_candidate":
        reasons.append("unexpected_candidate_record_type")
    if record.get("authority") != "candidate_record_not_proof_authority":
        reasons.append("invalid_candidate_record_authority")
    expected_review_status = (
        "source_context_changed_pending_review"
        if record.get("source_context_changed") is True
        else "lean_checked_pending_review"
    )
    if record.get("status") != expected_review_status:
        reasons.append("candidate_record_not_pending_owner_review")
    receipt = record.get("audit_receipt")
    if not isinstance(receipt, dict) or not verify_candidate_receipt(receipt):
        reasons.append("missing_or_invalid_receipt_digest")
        receipt = receipt if isinstance(receipt, dict) else {}
    if receipt.get("authority") != "candidate_observation_not_proof_authority":
        reasons.append("invalid_receipt_authority")
    artifact = receipt.get("artifact") if isinstance(receipt.get("artifact"), dict) else {}
    source = receipt.get("source") if isinstance(receipt.get("source"), dict) else {}
    environment = receipt.get("environment") if isinstance(receipt.get("environment"), dict) else {}
    checks = receipt.get("checks") if isinstance(receipt.get("checks"), dict) else {}
    review = receipt.get("review") if isinstance(receipt.get("review"), dict) else {}
    if not all(isinstance(receipt.get(key), dict) for key in ("artifact", "source", "environment", "checks", "review")):
        reasons.append("receipt_sections_malformed")
    if review.get("promotionAllowed") is not False:
        reasons.append("candidate_receipt_cannot_authorize_promotion")
    if review.get("status") != (
        "source_context_changed_pending_review"
        if record.get("source_context_changed") is True
        else "kernel_checked_pending_owner_review"
    ):
        reasons.append("receipt_review_status_mismatch")
    lean_check = checks.get("leanProcess") if isinstance(checks.get("leanProcess"), dict) else {}
    vacuity_check = checks.get("semanticVacuityGate") if isinstance(checks.get("semanticVacuityGate"), dict) else {}
    axiom_check = checks.get("axiomAudit") if isinstance(checks.get("axiomAudit"), dict) else {}
    if lean_check.get("returncode") != record.get("lean_check_returncode"):
        reasons.append("receipt_binding_mismatch:lean_returncode")
    if type(lean_check.get("returncode")) is not int or lean_check.get("returncode") != 0:
        reasons.append("candidate_not_kernel_checked")
    if lean_check.get("outputSha256") != record.get("lean_output_sha256", ""):
        reasons.append("receipt_binding_mismatch:lean_output")
    if vacuity_check.get("returncode") != record.get("semantic_vacuity_returncode"):
        reasons.append("receipt_binding_mismatch:vacuity_returncode")
    if type(vacuity_check.get("returncode")) is not int or vacuity_check.get("returncode") != 0:
        reasons.append("candidate_vacuity_gate_not_passed")
    if vacuity_check.get("outputSha256") != record.get("semantic_vacuity_output_sha256", ""):
        reasons.append("receipt_binding_mismatch:vacuity_output")
    if axiom_check.get("status") != record.get("axiom_audit_status", "not_requested"):
        reasons.append("receipt_binding_mismatch:axiom_status")
    if axiom_check.get("declarations") != record.get("axiom_audit_declarations", []):
        reasons.append("receipt_binding_mismatch:axiom_declarations")
    if axiom_check.get("returncode") != record.get("axiom_audit_returncode"):
        reasons.append("receipt_binding_mismatch:axiom_returncode")
    if axiom_check.get("outputSha256") != record.get("axiom_audit_output_sha256", ""):
        reasons.append("receipt_binding_mismatch:axiom_output")
    if source.get("changedSincePrompt") != (record.get("source_context_changed") is True):
        reasons.append("receipt_binding_mismatch:source_changed")
    bindings = (
        ("artifact.sha256", artifact.get("sha256"), record.get("candidate_sha256", "")),
        ("artifact.path", artifact.get("path"), record.get("lean_file", "")),
        ("source.snapshot", source.get("snapshotSha256"), record.get("source_snapshot_sha256", "")),
        ("source.path", source.get("path"), record.get("source_path", "")),
        ("source.current", source.get("currentSnapshotSha256"), record.get("source_snapshot_current_sha256", "")),
        ("environment.toolchain", environment.get("toolchain"), record.get("toolchain", "")),
        ("environment.lakefile", environment.get("lakefileSha256"), record.get("lakefile_sha256", "")),
        ("environment.manifest", environment.get("lakeManifestSha256"), record.get("lake_manifest_sha256", "")),
        ("environment.gitHead", environment.get("gitHead"), record.get("git_head", "")),
    )
    for label, actual, expected in bindings:
        if actual != expected:
            reasons.append(f"receipt_binding_mismatch:{label}")
    if not re.fullmatch(r"[0-9a-f]{64}", str(artifact.get("sha256", ""))):
        reasons.append("candidate_artifact_digest_missing_or_malformed")
    return {
        "schema": "info_geometry.hive_candidate_receipt_check.v1",
        "ok": not reasons,
        "reasons": reasons,
        "receipt": receipt if not reasons else None,
        "promotion_allowed": False,
    }


def read_candidate_receipt(record: dict[str, Any] | None) -> dict[str, Any] | None:
    """Return a candidate receipt only after integrity and record binding pass."""
    check = validate_candidate_archive_record(record)
    return check["receipt"] if check["ok"] else None


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
