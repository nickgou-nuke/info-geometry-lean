#!/usr/bin/env python3
"""Clarification stage for deep research controller."""

from __future__ import annotations

import json
from typing import Any

from .common import output_text, parse_json_text


CLARIFIER_SYSTEM = (
    "You are a research clarifier. "
    "Return strict JSON only. "
    "Do not perform research, only tighten scope and assumptions."
)


def normalize_clarification(raw: Any, *, goal: str) -> dict[str, Any]:
    if not isinstance(raw, dict):
        raw = {}

    clarifying_questions = raw.get("clarifying_questions", [])
    if not isinstance(clarifying_questions, list):
        clarifying_questions = []
    clarifying_questions = [str(x).strip() for x in clarifying_questions if str(x).strip()]

    assumptions = raw.get("assumptions", [])
    if not isinstance(assumptions, list):
        assumptions = []
    assumptions = [str(x).strip() for x in assumptions if str(x).strip()]

    clarified_goal = str(raw.get("clarified_goal", "")).strip() or goal
    needs = bool(raw.get("needs_clarification", False))

    return {
        "needs_clarification": needs,
        "clarifying_questions": clarifying_questions,
        "assumptions": assumptions,
        "clarified_goal": clarified_goal,
    }


def clarify_goal(
    *,
    client: Any,
    model: str,
    goal: str,
    constraints: list[str],
    allowed_sources: list[str],
    trusted_domains: list[str],
) -> dict[str, Any]:
    prompt = {
        "task": "clarify_research_intent",
        "goal": goal,
        "constraints": constraints,
        "allowed_sources": allowed_sources,
        "trusted_domains": trusted_domains,
        "instructions": [
            "Identify ambiguity that would change retrieval or verification.",
            "Ask only minimal clarifying questions.",
            "Propose explicit assumptions if user is unavailable.",
            "Return strict JSON only.",
        ],
        "required_output_schema": {
            "needs_clarification": "boolean",
            "clarifying_questions": ["string"],
            "assumptions": ["string"],
            "clarified_goal": "string",
        },
    }

    resp = client.responses.create(
        model=model,
        input=[
            {"role": "system", "content": CLARIFIER_SYSTEM},
            {"role": "user", "content": json.dumps(prompt, ensure_ascii=True)},
        ],
        text={"format": {"type": "json_object"}},
    )
    raw = parse_json_text(output_text(resp))
    return normalize_clarification(raw, goal=goal)

