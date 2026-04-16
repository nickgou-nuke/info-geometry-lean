#!/usr/bin/env python3
"""Research-brief rewrite stage for deep research controller."""

from __future__ import annotations

import json
from typing import Any

from .common import output_text, parse_json_text


REWRITER_SYSTEM = (
    "You are a research brief rewriter. "
    "Convert user intent + clarifications into a complete execution brief. "
    "Return strict JSON only."
)


def _normalize_list(value: Any) -> list[str]:
    if not isinstance(value, list):
        return []
    return [str(x).strip() for x in value if str(x).strip()]


def normalize_research_brief(raw: Any, *, goal: str) -> dict[str, Any]:
    if not isinstance(raw, dict):
        raw = {}

    scope = _normalize_list(raw.get("scope"))
    exclusions = _normalize_list(raw.get("exclusions"))
    source_preferences = _normalize_list(raw.get("source_preferences"))
    evaluation_criteria = _normalize_list(raw.get("evaluation_criteria"))
    desired_output = str(raw.get("desired_output", "")).strip() or "Structured report with citations and uncertainty"
    brief = str(raw.get("research_brief", "")).strip()

    if not brief:
        parts: list[str] = [f"Goal: {goal}"]
        if scope:
            parts.append("Scope: " + "; ".join(scope))
        if exclusions:
            parts.append("Exclusions: " + "; ".join(exclusions))
        if source_preferences:
            parts.append("Source preferences: " + "; ".join(source_preferences))
        parts.append("Desired output: " + desired_output)
        if evaluation_criteria:
            parts.append("Evaluation criteria: " + "; ".join(evaluation_criteria))
        brief = "\n".join(parts)

    return {
        "research_brief": brief,
        "scope": scope,
        "exclusions": exclusions,
        "source_preferences": source_preferences,
        "desired_output": desired_output,
        "evaluation_criteria": evaluation_criteria,
    }


def rewrite_research_brief(
    *,
    client: Any,
    model: str,
    goal: str,
    clarification: dict[str, Any],
    constraints: list[str],
    allowed_sources: list[str],
    trusted_domains: list[str],
) -> dict[str, Any]:
    prompt = {
        "task": "rewrite_research_brief",
        "goal": goal,
        "clarification": clarification,
        "constraints": constraints,
        "allowed_sources": allowed_sources,
        "trusted_domains": trusted_domains,
        "instructions": [
            "Rewrite into an execution-grade research brief.",
            "Make scope, exclusions, source preferences, and eval criteria explicit.",
            "Ensure constraints and allowed sources are reflected.",
            "Return strict JSON only.",
        ],
        "required_output_schema": {
            "research_brief": "string",
            "scope": ["string"],
            "exclusions": ["string"],
            "source_preferences": ["string"],
            "desired_output": "string",
            "evaluation_criteria": ["string"],
        },
    }

    resp = client.responses.create(
        model=model,
        input=[
            {"role": "system", "content": REWRITER_SYSTEM},
            {"role": "user", "content": json.dumps(prompt, ensure_ascii=True)},
        ],
        text={"format": {"type": "json_object"}},
    )
    raw = parse_json_text(output_text(resp))
    return normalize_research_brief(raw, goal=goal)

