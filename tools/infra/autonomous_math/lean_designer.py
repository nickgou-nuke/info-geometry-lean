#!/usr/bin/env python3
"""Lean theorem-design synthesizer."""

from __future__ import annotations

import re
from typing import Any


def _slug(name: str) -> str:
    s = re.sub(r"[^a-zA-Z0-9]+", "_", name.strip().lower()).strip("_")
    if not s:
        s = "target"
    if s[0].isdigit():
        s = f"t_{s}"
    return s[:64]


def synthesize(audited_packet: dict[str, Any]) -> dict[str, Any]:
    admitted = audited_packet.get("admitted_lanes", {})
    if not isinstance(admitted, dict):
        admitted = {}

    invariants = admitted.get("invariant_extraction", [])
    bridges = admitted.get("bridge_to_formalization", [])
    if not isinstance(invariants, list):
        invariants = []
    if not isinstance(bridges, list):
        bridges = []

    targets: list[dict[str, str]] = []
    for i, inv in enumerate(invariants[:8], start=1):
        slug = _slug(str(inv))
        targets.append(
            {
                "kind": "theorem",
                "name": f"auto_{i}_{slug}",
                "statement_hint": str(inv)[:220],
            }
        )
    for i, br in enumerate(bridges[:4], start=1):
        slug = _slug(str(br))
        targets.append(
            {
                "kind": "definition",
                "name": f"bridge_{i}_{slug}",
                "statement_hint": str(br)[:220],
            }
        )

    return {
        "research_goal": audited_packet.get("research_goal", ""),
        "targets": targets,
        "dependencies": [
            "lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean",
            "lean/InfoGeometry/Canonical/All.lean",
        ],
        "owner_classification": {
            "owner": "Canonical",
            "translator": "bridge_to_formalization",
            "coherence": "invariant_extraction",
        },
    }

