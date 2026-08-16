#!/usr/bin/env python3
"""Research packet builder + validator.

This script defines the typed handoff contract from Hermes deep-research intake
to Prompt A / Prompt B routing.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def confidence_bucket(value: float) -> str:
    if value >= 0.8:
        return "high"
    if value >= 0.55:
        return "medium"
    return "low"


def slug(text: str) -> str:
    out = re.sub(r"[^a-zA-Z0-9]+", "-", text.strip().lower()).strip("-")
    return out[:64] or "research"


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _uniq(items: list[str]) -> list[str]:
    seen = set()
    out = []
    for x in items:
        s = str(x).strip()
        if not s or s in seen:
            continue
        seen.add(s)
        out.append(s)
    return out


def build_packet_from_state(state: dict[str, Any], *, packet_id: str, state_path: str) -> dict[str, Any]:
    goal = str(state.get("goal", "")).strip() or "unspecified goal"
    allowed_sources = state.get("allowed_sources", [])
    if not isinstance(allowed_sources, list):
        allowed_sources = []
    allowed_sources = [str(s).strip() for s in allowed_sources if str(s).strip() in {"web", "files", "mcp"}]
    if not allowed_sources:
        allowed_sources = ["web"]

    trusted_domains = state.get("trusted_domains", [])
    if not isinstance(trusted_domains, list):
        trusted_domains = []
    trusted_domains = _uniq([str(d).strip() for d in trusted_domains if str(d).strip()])

    models = state.get("models", {})
    if not isinstance(models, dict):
        models = {}

    findings = state.get("findings", {})
    if not isinstance(findings, dict):
        findings = {}

    evidence: list[dict[str, Any]] = []
    candidate_invariants: list[str] = []
    facts: list[str] = []
    interpretations: list[str] = []
    metaphors: list[str] = []
    formalization_candidates: list[str] = []
    formalization_targets: list[dict[str, str]] = []

    for sq_id, payload in findings.items():
        if not isinstance(payload, dict):
            continue
        conf = confidence_bucket(float(payload.get("confidence", 0.0) or 0.0))
        claims = payload.get("claims", [])
        if not isinstance(claims, list):
            continue
        for row in claims:
            if not isinstance(row, dict):
                continue
            claim = str(row.get("claim", "")).strip()
            if not claim:
                continue
            cits = row.get("citations", [])
            if not isinstance(cits, list):
                cits = []
            sources = _uniq([str(c).strip() for c in cits if str(c).strip()])
            if not sources:
                continue
            ev = {
                "claim": claim,
                "sources": sources,
                "confidence": conf,
                "evidence_summary": str(row.get("evidence_summary", "")).strip(),
                "subquestion_id": str(sq_id),
            }
            evidence.append(ev)

            low = claim.lower()
            if conf == "high":
                facts.append(claim)
            elif conf == "medium":
                interpretations.append(claim)
            else:
                interpretations.append(claim)

            if any(k in low for k in ("metaphor", "analogy", "symbolic", "archetype", "poetic")):
                metaphors.append(claim)
            if "invariant" in low:
                candidate_invariants.append(claim)
            if any(k in low for k in ("theorem", "lemma", "iff", "commute", "closure", "proof")):
                formalization_targets.append({"kind": "theorem", "name": f"{sq_id}_theorem_target", "note": claim[:220]})
                formalization_candidates.append(claim)
            elif any(k in low for k in ("definition", "define", "structure", "operator", "interface")):
                formalization_targets.append({"kind": "definition", "name": f"{sq_id}_definition_target", "note": claim[:220]})
                formalization_candidates.append(claim)

    verification = state.get("verification", {})
    if not isinstance(verification, dict):
        verification = {}
    contradictions = verification.get("unresolved_conflicts", [])
    if not isinstance(contradictions, list):
        contradictions = []
    contradictions = _uniq([str(x).strip() for x in contradictions if str(x).strip()])

    forbidden_moves = [
        "replace support restriction by generic trace argument",
        "identify metric and spectral support by definition",
        "silently weaken theorem statements to force compilation",
        "treat metaphor as theorem evidence",
    ]

    packet = {
        "packet_id": packet_id,
        "created_at": utc_now(),
        "research_goal": goal,
        "allowed_sources": allowed_sources,
        "trusted_domains": trusted_domains,
        "provenance": {
            "source": "HermesDeepResearchController",
            "state_path": state_path,
            "models": {
                "planner": str(models.get("planner", "")),
                "research": str(models.get("research", "")),
                "verifier": str(models.get("verifier", "")),
                "writer": str(models.get("writer", "")),
            },
        },
        "evidence": evidence,
        "contradictions": contradictions,
        "candidate_invariants": _uniq(candidate_invariants),
        "forbidden_moves": forbidden_moves,
        "formalization_targets": formalization_targets[:64],
        "classification": {
            "facts": _uniq(facts),
            "interpretations": _uniq(interpretations),
            "metaphors": _uniq(metaphors),
            "formalization_candidates": _uniq(formalization_candidates),
        },
        "handoff": {
            "prompt_a_ready": True,
            "requires_nemoclaw_note": True,
            "requires_clawcode_gate": True,
        },
        "status": "draft",
    }
    return packet


def validate_packet(packet: Any) -> list[str]:
    errs: list[str] = []
    if not isinstance(packet, dict):
        return ["packet must be a JSON object"]

    req_top = [
        "packet_id",
        "created_at",
        "research_goal",
        "allowed_sources",
        "trusted_domains",
        "provenance",
        "evidence",
        "contradictions",
        "candidate_invariants",
        "forbidden_moves",
        "formalization_targets",
        "classification",
        "status",
    ]
    for k in req_top:
        if k not in packet:
            errs.append(f"missing required field: {k}")

    allowed_sources = packet.get("allowed_sources", [])
    if not isinstance(allowed_sources, list) or not allowed_sources:
        errs.append("allowed_sources must be non-empty array")
    else:
        for s in allowed_sources:
            if s not in {"web", "files", "mcp"}:
                errs.append(f"invalid allowed_sources entry: {s}")

    evidence = packet.get("evidence", [])
    if not isinstance(evidence, list):
        errs.append("evidence must be array")
    else:
        for i, row in enumerate(evidence, start=1):
            if not isinstance(row, dict):
                errs.append(f"evidence[{i}] must be object")
                continue
            claim = str(row.get("claim", "")).strip()
            if not claim:
                errs.append(f"evidence[{i}].claim missing")
            sources = row.get("sources", [])
            if not isinstance(sources, list) or not any(str(s).strip() for s in sources):
                errs.append(f"evidence[{i}].sources must contain at least one source")
            conf = str(row.get("confidence", "")).strip()
            if conf not in {"high", "medium", "low"}:
                errs.append(f"evidence[{i}].confidence invalid: {conf}")

    cls = packet.get("classification", {})
    if not isinstance(cls, dict):
        errs.append("classification must be object")
    else:
        for k in ("facts", "interpretations", "metaphors", "formalization_candidates"):
            v = cls.get(k)
            if not isinstance(v, list):
                errs.append(f"classification.{k} must be array")

    targets = packet.get("formalization_targets", [])
    if not isinstance(targets, list):
        errs.append("formalization_targets must be array")
    else:
        for i, t in enumerate(targets, start=1):
            if not isinstance(t, dict):
                errs.append(f"formalization_targets[{i}] must be object")
                continue
            kind = str(t.get("kind", "")).strip()
            if kind not in {"definition", "theorem", "lemma", "coherence", "translator", "capstone"}:
                errs.append(f"formalization_targets[{i}].kind invalid: {kind}")
            name = str(t.get("name", "")).strip()
            if not name:
                errs.append(f"formalization_targets[{i}].name missing")

    status = str(packet.get("status", "")).strip()
    if status not in {"draft", "stabilization", "admitted", "rejected"}:
        errs.append(f"invalid status: {status}")

    return errs


def cmd_build(args: argparse.Namespace) -> int:
    state_path = Path(args.state)
    if not state_path.exists():
        print(f"ERROR: state not found: {state_path}", file=sys.stderr)
        return 2
    state = load_json(state_path)
    if not isinstance(state, dict):
        print("ERROR: state must be a JSON object", file=sys.stderr)
        return 2

    pkt_id = args.packet_id.strip() if args.packet_id else f"rp-{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}-{slug(str(state.get('goal', 'research')))}"
    out = Path(args.out)
    packet = build_packet_from_state(state, packet_id=pkt_id, state_path=str(state_path))
    errs = validate_packet(packet)
    if errs:
        print("ERROR: built packet failed validation:", file=sys.stderr)
        for e in errs:
            print(f"  - {e}", file=sys.stderr)
        return 3
    write_json(out, packet)
    print(f"research packet written: {out}")
    return 0


def cmd_validate(args: argparse.Namespace) -> int:
    pkt_path = Path(args.packet)
    if not pkt_path.exists():
        print(f"ERROR: packet not found: {pkt_path}", file=sys.stderr)
        return 2
    packet = load_json(pkt_path)
    errs = validate_packet(packet)
    if errs:
        print("INVALID research packet")
        for e in errs:
            print(f"- {e}")
        return 1
    print("VALID research packet")
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    sp = p.add_subparsers(dest="cmd", required=True)

    p_build = sp.add_parser("build", help="Build typed research packet from deep-research state JSON.")
    p_build.add_argument("--state", required=True, help="Path to deep-research state JSON.")
    p_build.add_argument("--out", required=True, help="Output packet JSON path.")
    p_build.add_argument("--packet-id", default="", help="Optional explicit packet id.")

    p_val = sp.add_parser("validate", help="Validate research packet JSON.")
    p_val.add_argument("--packet", required=True, help="Path to research packet JSON.")
    return p.parse_args()


def main() -> None:
    args = parse_args()
    if args.cmd == "build":
        rc = cmd_build(args)
    elif args.cmd == "validate":
        rc = cmd_validate(args)
    else:
        rc = 2
    raise SystemExit(rc)


if __name__ == "__main__":
    main()

