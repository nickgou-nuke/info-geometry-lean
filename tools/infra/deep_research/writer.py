#!/usr/bin/env python3
"""Writer stage for deep research controller."""

from __future__ import annotations

import json
from typing import Any

from .common import output_text


WRITER_SYSTEM = (
    "You are a research report writer. "
    "Write from provided findings only. "
    "Keep citations attached to claims and include uncertainty."
)


def synthesize_report(
    *,
    client: Any,
    model: str,
    goal: str,
    plan: dict[str, Any],
    findings: dict[str, Any],
    verification: dict[str, Any],
    activity_log: list[dict[str, Any]],
) -> str:
    prompt = {
        "task": "write_report",
        "goal": goal,
        "plan": plan,
        "findings": findings,
        "verification": verification,
        "activity_log": activity_log,
        "instructions": [
            "Write a structured markdown report.",
            "Every material claim must include citation markers from findings.",
            "Include sections: Executive Summary, Findings by Subquestion, Conflicts and Uncertainty, Activity Log, Open Items.",
            "Do not invent sources.",
        ],
    }

    resp = client.responses.create(
        model=model,
        input=[
            {"role": "system", "content": WRITER_SYSTEM},
            {"role": "user", "content": json.dumps(prompt, ensure_ascii=True)},
        ],
    )
    text = output_text(resp).strip()
    if not text:
        return "# Research Report\n\nNo report text returned by model."
    return text

