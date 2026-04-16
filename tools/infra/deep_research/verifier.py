#!/usr/bin/env python3
"""Verifier stage for deep research controller."""

from __future__ import annotations

import json
from typing import Any

from .common import output_text, parse_json_text


VERIFIER_SYSTEM = (
    "You are a research verifier. "
    "Evaluate coverage, contradictions, and evidence sufficiency. "
    "Return strict JSON only."
)


def normalize_verdict(raw: Any) -> dict[str, Any]:
    if not isinstance(raw, dict):
        raw = {}

    missing = raw.get("missing_subquestions", [])
    if not isinstance(missing, list):
        missing = []
    norm_missing: list[dict[str, Any]] = []
    for i, row in enumerate(missing, start=1):
        if not isinstance(row, dict):
            continue
        q = str(row.get("question", "")).strip()
        if not q:
            continue
        sq_id = str(row.get("id", f"extra_sq{i}")).strip() or f"extra_sq{i}"
        sources = row.get("sources", [])
        if not isinstance(sources, list):
            sources = []
        norm_missing.append(
            {
                "id": sq_id,
                "question": q,
                "sources": [str(s) for s in sources if str(s).strip()],
                "done_when": str(row.get("done_when", "Evidence threshold satisfied")).strip(),
                "reason": str(row.get("reason", "")).strip(),
            }
        )

    conflicts = raw.get("unresolved_conflicts", [])
    if not isinstance(conflicts, list):
        conflicts = []
    conflicts = [str(x).strip() for x in conflicts if str(x).strip()]

    coverage = raw.get("coverage", [])
    if not isinstance(coverage, list):
        coverage = []

    rationale = raw.get("rationale", [])
    if not isinstance(rationale, list):
        rationale = []
    rationale = [str(x).strip() for x in rationale if str(x).strip()]

    more = bool(raw.get("more_research_required", False))
    gate = str(raw.get("gate_status", "fail")).strip().lower()
    if gate not in {"pass", "fail"}:
        gate = "fail"

    return {
        "more_research_required": more,
        "missing_subquestions": norm_missing,
        "unresolved_conflicts": conflicts,
        "coverage": coverage,
        "gate_status": gate,
        "rationale": rationale,
    }


def verify_research(
    *,
    client: Any,
    model: str,
    goal: str,
    plan: dict[str, Any],
    findings: dict[str, Any],
    constraints: list[str],
) -> dict[str, Any]:
    prompt = {
        "task": "verify_coverage",
        "goal": goal,
        "plan": plan,
        "findings": findings,
        "constraints": constraints,
        "instructions": [
            "Identify missing evidence for each subquestion.",
            "Identify contradictions and unresolved conflicts.",
            "Return more_research_required=true if required coverage is missing.",
            "If missing, propose missing_subquestions with id/question/sources/done_when/reason.",
            "Return strict JSON only.",
        ],
        "required_output_schema": {
            "more_research_required": "boolean",
            "missing_subquestions": [
                {
                    "id": "string",
                    "question": "string",
                    "sources": ["string"],
                    "done_when": "string",
                    "reason": "string",
                }
            ],
            "unresolved_conflicts": ["string"],
            "coverage": [{"subquestion_id": "string", "status": "covered|partial|missing", "notes": "string"}],
            "gate_status": "pass|fail",
            "rationale": ["string"],
        },
    }

    resp = client.responses.create(
        model=model,
        input=[
            {"role": "system", "content": VERIFIER_SYSTEM},
            {"role": "user", "content": json.dumps(prompt, ensure_ascii=True)},
        ],
        text={"format": {"type": "json_object"}},
    )
    raw = parse_json_text(output_text(resp))
    return normalize_verdict(raw)

