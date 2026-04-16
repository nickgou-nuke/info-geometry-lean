#!/usr/bin/env python3
"""Socratic/Jungian expansion over evidence packet."""

from __future__ import annotations

from typing import Any

from .evidence_packet import EvidencePacket


def expand(packet: EvidencePacket) -> dict[str, Any]:
    claims = [c.claim for c in packet.evidence][:32]
    invariants = packet.candidate_invariants[:24]
    open_problems = packet.open_problems[:24]

    archetypal = [
        f"Metaphor candidate for invariant surface: {x}" for x in invariants[:8]
    ]
    skeptical = [
        f"Counter-check: can '{x}' be reduced to a naming wrapper?" for x in claims[:8]
    ]
    invariant_lane = invariants if invariants else claims[:12]
    bridge_lane = [
        f"Lean bridge candidate: formalize claim '{x[:120]}' as theorem target"
        for x in claims[:10]
    ]

    return {
        "research_goal": packet.research_goal,
        "lanes": {
            "archetypal_metaphor": archetypal,
            "skeptical_reduction": skeptical,
            "invariant_extraction": invariant_lane,
            "bridge_to_formalization": bridge_lane,
        },
        "open_problems": open_problems,
        "forbidden_moves": packet.forbidden_moves,
        "formalization_targets": [t.__dict__ for t in packet.formalization_targets],
    }

