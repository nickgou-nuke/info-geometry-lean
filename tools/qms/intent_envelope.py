#!/usr/bin/env python3
"""
Formal intent envelope per docs/ALCHEMICAL_QMS_SOP.md section 3.6.

The intent envelope is a hard anti-smuggling control that separates conceptual
payload, theorem candidate, model assumption, external evidence, and
documentation-only material before Lean generation begins. A claim such as
D4 triality, Bost-Connes closure, Mersenne numerology, thermodynamic completion,
or physics bridge completion may not enter the theorem contract unless the
envelope names the exact formal object, owner import, and acceptance theorem
carrying that structure.

Usage:
    python3 tools/qms/intent_envelope.py --task-id <ID> --source-text "<text>"
        --classification theorem-bearing --target-status theorem-backed \
        --risk-level R2 --out artifacts/qms/<ID>-intent_envelope.json
"""

from __future__ import annotations

import argparse
import json
import re
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

INTAKE_CLASSIFICATIONS = {
    "definition-only",
    "theorem-bearing",
    "computational-witness",
    "narrative-documentation",
    "external-system-verification",
    "conjectural-scaffold",
}

TARGET_STATUSES = {
    "definition-backed",
    "theorem-backed",
    "model-parameter",
    "computational-witness",
    "external-verified",
    "conjectural-scaffold",
    "documentation-only",
}

RISK_LEVELS = {"R0", "R1", "R2", "R3", "R4", "R5"}

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
    "accepted_limited_scope",
    "needs_capa",
    "audit_blocked",
    "qa_blocked",
    "bucket_3_open_debt",
    "rejected_false_surface",
}

# High-risk language that must not appear unqualified in a theorem-bearing claim.
INFINITE_SCOPE_WORDS = [
    "infinite",
    "thermodynamic limit",
    "continuum limit",
    "global colimit",
    "completion",
]

# Fake-closure patterns that must not hide proof debt.
PLACEHOLDER_TOKENS = [
    "sorry",
    "admit",
    "Admitted",
    "axiom",
    "Axiom",
    "Parameter",
    "Conjecture",
    "axiomatization",
    "oops",
    "Prop := True",
    ":= True",
    "_True",
    "_holds",
    "_valid",
    "_certificate",
    "_sorryProof",
]

# Known fake-closure theorem-name patterns (ambition-descriptive, not content-descriptive).
AMBITION_NAME_HINTS = [
    "complete",
    "sealed",
    "proves",
    "resolution",
    "anomalyResolution",
    "cathedral",
    "bridge_proves",
]


class IntentEnvelopeError(ValueError):
    """Raised when an intent envelope fails validation."""


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _sha256_text(text: str) -> str:
    import hashlib

    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def validate_intake_classification(value: str) -> None:
    if value not in INTAKE_CLASSIFICATIONS:
        raise IntentEnvelopeError(
            f"invalid intake_classification: {value!r}; "
            f"must be one of {sorted(INTAKE_CLASSIFICATIONS)}"
        )


def validate_target_status(value: str) -> None:
    if value not in TARGET_STATUSES:
        raise IntentEnvelopeError(
            f"invalid target_status: {value!r}; "
            f"must be one of {sorted(TARGET_STATUSES)}"
        )


def validate_risk_level(value: str) -> None:
    if value not in RISK_LEVELS:
        raise IntentEnvelopeError(
            f"invalid risk_level: {value!r}; must be one of {sorted(RISK_LEVELS)}"
        )


def validate_scope_labels(labels: list[str]) -> None:
    for label in labels:
        if label not in SCOPE_LABELS:
            raise IntentEnvelopeError(
                f"invalid scope label: {label!r}; must be one of {sorted(SCOPE_LABELS)}"
            )


def check_infinite_scope_language(source_text: str, risk_level: str) -> list[str]:
    """Flag unqualified infinite-scope language for R4/R5 artifacts."""
    warnings: list[str] = []
    lowered = source_text.lower()
    for word in INFINITE_SCOPE_WORDS:
        if word in lowered:
            if risk_level in {"R4", "R5"}:
                warnings.append(
                    f"risk_level {risk_level} artifact contains unqualified "
                    f"infinite-scope language: '{word}' — must name the exact "
                    f"owner theorem and import path carrying that scope"
                )
    return warnings


def check_placeholder_tokens(source_text: str) -> list[str]:
    """Flag placeholder tokens that may hide proof debt."""
    findings: list[str] = []
    for token in PLACEHOLDER_TOKENS:
        if token in source_text:
            findings.append(f"placeholder token detected: '{token}'")
    return findings


def check_ambition_names(formal_objects: list[str]) -> list[str]:
    """Flag ambition-descriptive formal object names."""
    findings: list[str] = []
    for obj in formal_objects:
        for hint in AMBITION_NAME_HINTS:
            if hint.lower() in obj.lower():
                findings.append(
                    f"ambition-descriptive formal object name: '{obj}' "
                    f"(contains '{hint}') — theorem names must be content-descriptive"
                )
                break
    return findings


def build_intent_envelope(
    *,
    task_id: str,
    source_text: str,
    intake_classification: str,
    classification: str,
    mathematical_domain: list[str],
    target_status: str,
    risk_level: str,
    allowed_imports: list[str],
    non_theorem_claims: list[str],
    formal_objects: list[str],
    acceptance_theorems: list[str],
    scope_labels: list[str] | None = None,
    source_paths: list[str] | None = None,
) -> dict[str, Any]:
    """Build and validate a formal intent envelope.

    Raises IntentEnvelopeError on invalid input.
    """
    validate_intake_classification(intake_classification)
    validate_target_status(target_status)
    validate_risk_level(risk_level)
    if scope_labels:
        validate_scope_labels(scope_labels)

    # Theorem-bearing claims require explicit scope labels.
    if intake_classification == "theorem-bearing" and not scope_labels:
        raise IntentEnvelopeError(
            "theorem-bearing intake_classification requires at least one scope_label"
        )

    # R4/R5 require exact formal objects and acceptance theorems.
    if risk_level in {"R4", "R5"}:
        if not formal_objects:
            raise IntentEnvelopeError(
                f"risk_level {risk_level} requires at least one formal_object"
            )
        if not acceptance_theorems:
            raise IntentEnvelopeError(
                f"risk_level {risk_level} requires at least one acceptance_theorem"
            )

    envelope: dict[str, Any] = {
        "schema": "info_geometry.qms.intent_envelope.v1",
        "sop_id": __import__("tools.qms", fromlist=["__sop_id__"]).__sop_id__,
        "version": "4.1",
        "task_id": task_id,
        "generated_at": _now_iso(),
        "source_text": source_text,
        "source_sha256": _sha256_text(source_text),
        "intake_classification": intake_classification,
        "classification": classification,
        "mathematical_domain": mathematical_domain,
        "target_status": target_status,
        "risk_level": risk_level,
        "allowed_imports": allowed_imports,
        "non_theorem_claims": non_theorem_claims,
        "formal_objects": formal_objects,
        "acceptance_theorems": acceptance_theorems,
        "scope_labels": scope_labels or [],
        "source_paths": source_paths or [],
        "warnings": [],
        "status_tag": "intent_captured",
    }

    # Anti-smuggling checks.
    envelope["warnings"].extend(check_infinite_scope_language(source_text, risk_level))
    envelope["warnings"].extend(check_placeholder_tokens(source_text))
    envelope["warnings"].extend(check_ambition_names(formal_objects))

    return envelope


def write_intent_envelope(envelope: dict[str, Any], out_path: Path) -> Path:
    """Write an intent envelope to disk as JSON."""
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(envelope, indent=2) + "\n", encoding="utf-8")
    return out_path


def load_intent_envelope(path: Path | str) -> dict[str, Any]:
    """Load and minimally validate an intent envelope from disk."""
    path = Path(path)
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise IntentEnvelopeError(f"invalid intent envelope (not an object): {path}")
    if data.get("schema") != "info_geometry.qms.intent_envelope.v1":
        raise IntentEnvelopeError(f"unsupported intent envelope schema: {path}")
    return data


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build a formal intent envelope (QMS-SOP-ALC-001 section 3.6)."
    )
    parser.add_argument("--task-id", required=True, help="Unique task identifier")
    parser.add_argument(
        "--source-text", required=True, help="Source text or prompt excerpt"
    )
    parser.add_argument(
        "--source-file",
        help="Optional file whose contents are used as source_text",
    )
    parser.add_argument(
        "--intake-classification",
        required=True,
        choices=sorted(INTAKE_CLASSIFICATIONS),
        help="Intake classification bucket",
    )
    parser.add_argument("--classification", required=True, help="Representation-level classification")
    parser.add_argument(
        "--mathematical-domain",
        nargs="*",
        default=[],
        help="Mathematical domain tags",
    )
    parser.add_argument(
        "--target-status",
        required=True,
        choices=sorted(TARGET_STATUSES),
        help="Target release status",
    )
    parser.add_argument(
        "--risk-level",
        required=True,
        choices=sorted(RISK_LEVELS),
        help="Risk class R0-R5",
    )
    parser.add_argument(
        "--allowed-import",
        action="append",
        default=[],
        help="Allowed import path (repeatable)",
    )
    parser.add_argument(
        "--non-theorem-claim",
        action="append",
        default=[],
        help="Non-theorem claim (repeatable)",
    )
    parser.add_argument(
        "--formal-object",
        action="append",
        default=[],
        help="Formal object name (repeatable)",
    )
    parser.add_argument(
        "--acceptance-theorem",
        action="append",
        default=[],
        help="Acceptance theorem name (repeatable)",
    )
    parser.add_argument(
        "--scope-label",
        action="append",
        default=[],
        choices=sorted(SCOPE_LABELS),
        help="Scope label (repeatable)",
    )
    parser.add_argument(
        "--source-path",
        action="append",
        default=[],
        help="Source file path read (repeatable)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        required=True,
        help="Output JSON path for the intent envelope",
    )
    args = parser.parse_args()

    source_text = args.source_text
    if args.source_file:
        source_text = Path(args.source_file).read_text(encoding="utf-8")

    try:
        envelope = build_intent_envelope(
            task_id=args.task_id,
            source_text=source_text,
            intake_classification=args.intake_classification,
            classification=args.classification,
            mathematical_domain=args.mathematical_domain,
            target_status=args.target_status,
            risk_level=args.risk_level,
            allowed_imports=args.allowed_import,
            non_theorem_claims=args.non_theorem_claim,
            formal_objects=args.formal_object,
            acceptance_theorems=args.acceptance_theorem,
            scope_labels=args.scope_label or None,
            source_paths=args.source_path,
        )
    except IntentEnvelopeError as exc:
        print(f"[intent_envelope] validation failed: {exc}", file=sys.stderr)
        return 2

    write_intent_envelope(envelope, args.out)
    print(
        f"[intent_envelope] wrote {args.out} "
        f"(task={args.task_id}, risk={args.risk_level}, "
        f"status={args.target_status}, warnings={len(envelope['warnings'])})"
    )
    for w in envelope["warnings"]:
        print(f"  - {w}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
