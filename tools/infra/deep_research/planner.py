#!/usr/bin/env python3
"""Planner stage for deep research controller."""

from __future__ import annotations

import json
from typing import Any

from .common import output_text, parse_json_text


PLANNER_SYSTEM = (
    "You are a research controller planner. "
    "Return strict JSON only. Do not answer the research question."
)


def _normalize_sources(sources: Any, allowed_sources: list[str]) -> list[str]:
    out: list[str] = []
    if isinstance(sources, list):
        for s in sources:
            if isinstance(s, str) and s in allowed_sources and s not in out:
                out.append(s)
    if not out:
        out = allowed_sources[:]
    return out


def normalize_plan(plan: Any, *, goal: str, allowed_sources: list[str]) -> dict[str, Any]:
    if not isinstance(plan, dict):
        plan = {}

    constraints = plan.get("constraints", [])
    if not isinstance(constraints, list):
        constraints = []
    constraints = [str(c) for c in constraints if str(c).strip()]

    subqs = plan.get("subquestions", [])
    if not isinstance(subqs, list):
        subqs = []

    normalized_subqs: list[dict[str, Any]] = []
    for i, row in enumerate(subqs, start=1):
        if not isinstance(row, dict):
            continue
        q = str(row.get("question", "")).strip()
        if not q:
            continue
        sq_id = str(row.get("id", f"sq{i}")).strip() or f"sq{i}"
        normalized_subqs.append(
            {
                "id": sq_id,
                "question": q,
                "sources": _normalize_sources(row.get("sources"), allowed_sources),
                "done_when": str(row.get("done_when", "Evidence threshold satisfied")).strip(),
            }
        )

    if not normalized_subqs:
        normalized_subqs = [
            {
                "id": "sq1",
                "question": goal,
                "sources": allowed_sources[:],
                "done_when": "At least two primary sources agree or conflict is surfaced",
            }
        ]

    final_output = str(plan.get("final_output", "Structured report with citations and uncertainty")).strip()
    if not final_output:
        final_output = "Structured report with citations and uncertainty"

    return {
        "goal": str(plan.get("goal", goal)).strip() or goal,
        "constraints": constraints,
        "subquestions": normalized_subqs,
        "final_output": final_output,
    }


def create_plan(
    *,
    client: Any,
    model: str,
    goal: str,
    constraints: list[str],
    allowed_sources: list[str],
    trusted_domains: list[str],
) -> dict[str, Any]:
    user_prompt = {
        "task": "create_research_plan",
        "goal": goal,
        "constraints": constraints,
        "allowed_sources": allowed_sources,
        "trusted_domains": trusted_domains,
        "instructions": [
            "Return strict JSON object only.",
            "Create goal, constraints, subquestions, final_output.",
            "Each subquestion must include id, question, sources, done_when.",
            "Use only allowed source names in sources.",
            "Do not answer the research question.",
        ],
    }

    resp = client.responses.create(
        model=model,
        input=[
            {"role": "system", "content": PLANNER_SYSTEM},
            {"role": "user", "content": json.dumps(user_prompt, ensure_ascii=True)},
        ],
        text={"format": {"type": "json_object"}},
    )
    raw = parse_json_text(output_text(resp))
    return normalize_plan(raw, goal=goal, allowed_sources=allowed_sources)
