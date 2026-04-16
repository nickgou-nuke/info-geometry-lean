#!/usr/bin/env python3
"""Pauli-style admissibility audit."""

from __future__ import annotations

from typing import Any


REJECTION_MARKERS = (
    "numerology",
    "mystical proof",
    "category leap",
    "unsupported by evidence",
)


def _admissible(line: str) -> tuple[bool, str]:
    low = line.lower()
    for marker in REJECTION_MARKERS:
        if marker in low:
            return False, f"contains rejection marker '{marker}'"
    if len(line.strip()) < 8:
        return False, "too short to be actionable"
    return True, ""


def audit(dialogue_packet: dict[str, Any]) -> dict[str, Any]:
    lanes = dialogue_packet.get("lanes", {})
    if not isinstance(lanes, dict):
        lanes = {}

    admitted: dict[str, list[str]] = {}
    rejected: list[dict[str, str]] = []

    for lane, items in lanes.items():
        if not isinstance(items, list):
            continue
        lane_admitted: list[str] = []
        for item in items:
            text = str(item).strip()
            ok, reason = _admissible(text)
            if ok:
                lane_admitted.append(text)
            else:
                rejected.append({"lane": str(lane), "item": text, "reason": reason})
        admitted[str(lane)] = lane_admitted

    return {
        "research_goal": dialogue_packet.get("research_goal", ""),
        "admitted_lanes": admitted,
        "rejected": rejected,
        "open_problems": dialogue_packet.get("open_problems", []),
        "forbidden_moves": dialogue_packet.get("forbidden_moves", []),
        "formalization_targets": dialogue_packet.get("formalization_targets", []),
        "admission_ok": any(admitted.get("invariant_extraction", [])),
    }

