#!/usr/bin/env python3
"""Typed evidence packet used between research and formalization phases."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any


@dataclass
class EvidenceClaim:
    claim: str
    sources: list[str]
    confidence: str
    evidence_summary: str = ""


@dataclass
class FormalizationTarget:
    kind: str
    name: str
    note: str = ""


@dataclass
class EvidencePacket:
    research_goal: str
    evidence: list[EvidenceClaim] = field(default_factory=list)
    open_problems: list[str] = field(default_factory=list)
    candidate_invariants: list[str] = field(default_factory=list)
    forbidden_moves: list[str] = field(default_factory=list)
    formalization_targets: list[FormalizationTarget] = field(default_factory=list)
    phase_log: list[dict[str, Any]] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _confidence_bucket(value: float) -> str:
    if value >= 0.8:
        return "high"
    if value >= 0.55:
        return "medium"
    return "low"


def from_deep_research_state(state: dict[str, Any]) -> EvidencePacket:
    goal = str(state.get("goal", "")).strip() or "unspecified goal"
    findings = state.get("findings", {})
    if not isinstance(findings, dict):
        findings = {}

    evidence: list[EvidenceClaim] = []
    open_problems: list[str] = []
    candidate_invariants: list[str] = []
    formalization_targets: list[FormalizationTarget] = []

    for sq_id, payload in findings.items():
        if not isinstance(payload, dict):
            continue
        conf = _confidence_bucket(float(payload.get("confidence", 0.0) or 0.0))

        claims = payload.get("claims", [])
        if isinstance(claims, list):
            for row in claims:
                if not isinstance(row, dict):
                    continue
                claim = str(row.get("claim", "")).strip()
                if not claim:
                    continue
                cits = row.get("citations", [])
                if not isinstance(cits, list):
                    cits = []
                srcs = [str(c).strip() for c in cits if str(c).strip()]
                evidence.append(
                    EvidenceClaim(
                        claim=claim,
                        sources=srcs,
                        confidence=conf,
                        evidence_summary=str(row.get("evidence_summary", "")).strip(),
                    )
                )

                low = claim.lower()
                if "invariant" in low and claim not in candidate_invariants:
                    candidate_invariants.append(claim)
                if any(k in low for k in ("define", "definition", "let ", "structure", "operator")):
                    formalization_targets.append(
                        FormalizationTarget(kind="definition", name=f"{sq_id}_definition_target")
                    )
                if any(k in low for k in ("theorem", "lemma", "prove", "iff", "equals", "commute")):
                    formalization_targets.append(
                        FormalizationTarget(kind="theorem", name=f"{sq_id}_theorem_target")
                    )

        oq = payload.get("open_questions", [])
        if isinstance(oq, list):
            for q in oq:
                qs = str(q).strip()
                if qs and qs not in open_problems:
                    open_problems.append(qs)

    verification = state.get("verification", {})
    if isinstance(verification, dict):
        unresolved = verification.get("unresolved_conflicts", [])
        if isinstance(unresolved, list):
            for u in unresolved:
                us = str(u).strip()
                if us and us not in open_problems:
                    open_problems.append(us)

    forbidden_moves = [
        "replace support restriction by generic trace argument",
        "identify metric and spectral support by definition",
        "silently weaken theorem statements to satisfy compiler",
    ]

    packet = EvidencePacket(
        research_goal=goal,
        evidence=evidence,
        open_problems=open_problems,
        candidate_invariants=candidate_invariants,
        forbidden_moves=forbidden_moves,
        formalization_targets=formalization_targets[:24],
        phase_log=[{"phase": "evidence_packet", "status": "generated"}],
    )
    return packet

