#!/usr/bin/env python3
"""End-to-end autonomous mathematician controller (first production lane)."""

from __future__ import annotations

import argparse
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[3]))

from tools.infra.deep_research.common import utc_now, write_json
from tools.infra.deep_research.planner import create_plan
from tools.infra.deep_research.retriever import build_tools, research_subquestion
from tools.infra.deep_research.verifier import verify_research
from tools.infra.deep_research.writer import synthesize_report
from tools.infra.research_packet import build_packet_from_state, validate_packet

from tools.infra.autonomous_math.compiler_loop import close
from tools.infra.autonomous_math.evidence_packet import from_deep_research_state
from tools.infra.autonomous_math.lean_coder import write_scaffold
from tools.infra.autonomous_math.lean_designer import synthesize as synthesize_design
from tools.infra.autonomous_math.memory_ingest import ingest
from tools.infra.autonomous_math.pauli_auditor import audit
from tools.infra.autonomous_math.socratic_engine import expand


def _make_client() -> Any:
    try:
        from openai import OpenAI
    except Exception as exc:  # pragma: no cover
        raise SystemExit("Missing dependency: openai (pip install openai)") from exc
    return OpenAI()


def _slug(text: str) -> str:
    chars = []
    for ch in text.lower():
        if ch.isalnum():
            chars.append(ch)
        elif ch in {" ", "-", "_"}:
            chars.append("-")
    s = "".join(chars).strip("-")
    while "--" in s:
        s = s.replace("--", "-")
    return s[:64] or "autonomous-research"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--goal", required=True)
    p.add_argument("--constraint", action="append", default=[])
    p.add_argument("--allowed-sources", default="web")
    p.add_argument("--trusted-domain", action="append", default=[])
    p.add_argument("--vector-store-id", action="append", default=[])
    p.add_argument("--mcp-server", action="append", default=[])
    p.add_argument("--planner-model", default=os.environ.get("OPENAI_DR_PLANNER_MODEL", "gpt-5"))
    p.add_argument("--research-model", default=os.environ.get("OPENAI_DR_RESEARCH_MODEL", "gpt-5"))
    p.add_argument("--verifier-model", default=os.environ.get("OPENAI_DR_VERIFIER_MODEL", "gpt-5"))
    p.add_argument("--writer-model", default=os.environ.get("OPENAI_DR_WRITER_MODEL", "gpt-5"))
    p.add_argument("--max-extra-rounds", type=int, default=1)
    p.add_argument("--state-out", default="")
    p.add_argument("--report-out", default="")
    p.add_argument("--memory-log", default="reports/research/autonomous_memory.jsonl")
    p.add_argument(
        "--research-packet-out",
        default="",
        help="Output path for typed Hermes research packet.",
    )
    return p.parse_args()


def _parse_allowed_sources(value: str) -> list[str]:
    out = []
    for raw in value.split(","):
        s = raw.strip()
        if not s:
            continue
        if s not in {"web", "files", "mcp"}:
            raise ValueError(f"unknown source {s}")
        if s not in out:
            out.append(s)
    if not out:
        out = ["web"]
    return out


def _parse_mcp_servers(values: list[str]) -> list[dict[str, Any]]:
    servers: list[dict[str, Any]] = []
    for raw in values:
        obj = json.loads(raw)
        if not isinstance(obj, dict):
            raise ValueError("--mcp-server must be a JSON object")
        if not isinstance(obj.get("server_url"), str):
            raise ValueError("--mcp-server requires server_url")
        servers.append(obj)
    return servers


def _claims_cited(findings: dict[str, Any]) -> tuple[bool, list[str]]:
    missing: list[str] = []
    for sq_id, payload in findings.items():
        if not isinstance(payload, dict):
            missing.append(f"{sq_id}: invalid payload")
            continue
        claims = payload.get("claims", [])
        if not isinstance(claims, list):
            missing.append(f"{sq_id}: claims not list")
            continue
        for i, row in enumerate(claims, start=1):
            if not isinstance(row, dict):
                missing.append(f"{sq_id}: claim {i} invalid")
                continue
            text = str(row.get("claim", "")).strip()
            if not text:
                continue
            cits = row.get("citations", [])
            if not isinstance(cits, list) or not any(str(c).strip() for c in cits):
                missing.append(f"{sq_id}: uncited claim {i}")
    return (len(missing) == 0), missing


def main() -> None:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[3]
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    slug = _slug(args.goal)
    state_out = Path(args.state_out).resolve() if args.state_out else repo_root / "reports" / "research" / f"autonomous-state-{stamp}-{slug}.json"
    report_out = Path(args.report_out).resolve() if args.report_out else repo_root / "reports" / "research" / f"autonomous-report-{stamp}-{slug}.md"
    packet_out = (
        Path(args.research_packet_out).resolve()
        if args.research_packet_out
        else repo_root / "quarantine" / "hermes_memory" / "research_packets" / f"{stamp}-{slug}.json"
    )
    memory_log = Path(args.memory_log)
    if not memory_log.is_absolute():
        memory_log = repo_root / memory_log

    allowed_sources = _parse_allowed_sources(args.allowed_sources)
    trusted_domains = [d.strip() for d in args.trusted_domain if d.strip()]
    mcp_servers = _parse_mcp_servers(args.mcp_server)
    constraints = list(args.constraint) or [
        "Use only allowed sources",
        "Cite each material claim",
        "Surface unresolved conflicts",
    ]

    client = _make_client()
    activity: list[dict[str, Any]] = []
    findings: dict[str, Any] = {}

    # Research planner
    plan = create_plan(
        client=client,
        model=args.planner_model,
        goal=args.goal,
        constraints=constraints,
        allowed_sources=allowed_sources,
        trusted_domains=trusted_domains,
    )
    activity.append({"phase": "planner", "ts": utc_now(), "subquestions": len(plan.get("subquestions", []))})

    # Deep research executor
    tools = build_tools(
        allowed_sources=allowed_sources,
        trusted_domains=trusted_domains,
        vector_store_ids=args.vector_store_id,
        mcp_servers=mcp_servers,
    )
    if not tools:
        raise SystemExit("No tools enabled for allowed sources.")

    for subq in plan.get("subquestions", []):
        if not isinstance(subq, dict):
            continue
        sq_id = str(subq.get("id", "")).strip()
        if not sq_id:
            continue
        finding = research_subquestion(
            client=client,
            model=args.research_model,
            subquestion=subq,
            goal=args.goal,
            constraints=constraints,
            allowed_sources=allowed_sources,
            tools=tools,
        )
        findings[sq_id] = finding
        activity.append(
            {
                "phase": "deep_research",
                "ts": utc_now(),
                "subquestion_id": sq_id,
                "claims": len(finding.get("claims", [])),
                "evidence": len(finding.get("evidence", [])),
                "confidence": finding.get("confidence", 0.0),
            }
        )

    verification = verify_research(
        client=client,
        model=args.verifier_model,
        goal=args.goal,
        plan=plan,
        findings=findings,
        constraints=constraints,
    )
    activity.append(
        {
            "phase": "verification",
            "ts": utc_now(),
            "more_research_required": bool(verification.get("more_research_required", False)),
            "missing_subquestions": len(verification.get("missing_subquestions", [])),
            "unresolved_conflicts": len(verification.get("unresolved_conflicts", [])),
        }
    )

    # Optional extra rounds
    extra = 0
    while bool(verification.get("more_research_required", False)) and extra < max(0, args.max_extra_rounds):
        extra += 1
        miss = verification.get("missing_subquestions", [])
        if not isinstance(miss, list):
            break
        for subq in miss:
            if not isinstance(subq, dict):
                continue
            sq_id = str(subq.get("id", "")).strip()
            if not sq_id or sq_id in findings:
                continue
            finding = research_subquestion(
                client=client,
                model=args.research_model,
                subquestion=subq,
                goal=args.goal,
                constraints=constraints,
                allowed_sources=allowed_sources,
                tools=tools,
            )
            findings[sq_id] = finding
            activity.append(
                {
                    "phase": "deep_research_extra",
                    "ts": utc_now(),
                    "round": extra,
                    "subquestion_id": sq_id,
                    "claims": len(finding.get("claims", [])),
                    "evidence": len(finding.get("evidence", [])),
                    "confidence": finding.get("confidence", 0.0),
                }
            )

        verification = verify_research(
            client=client,
            model=args.verifier_model,
            goal=args.goal,
            plan=plan,
            findings=findings,
            constraints=constraints,
        )
        activity.append(
            {
                "phase": "verification",
                "ts": utc_now(),
                "round": extra,
                "more_research_required": bool(verification.get("more_research_required", False)),
                "missing_subquestions": len(verification.get("missing_subquestions", [])),
                "unresolved_conflicts": len(verification.get("unresolved_conflicts", [])),
            }
        )

    # Gate: every material claim cited and verifier no-more-research
    citations_ok, uncited = _claims_cited(findings)
    verifier_ok = not bool(verification.get("more_research_required", False))

    gate_failures: list[str] = []
    if not citations_ok:
        gate_failures.append(f"uncited claims: {uncited}")
    if not verifier_ok:
        gate_failures.append("verifier requires additional research")

    report_text = ""
    status = "blocked_by_gates"

    # Socratic/Jungian -> Pauli -> Lean design/coder -> compile loop
    deep_state = {
        "goal": args.goal,
        "findings": findings,
        "verification": verification,
    }
    evidence_packet = from_deep_research_state(deep_state)
    dialogue_packet = expand(evidence_packet)
    audited_packet = audit(dialogue_packet)
    formal_packet = synthesize_design(audited_packet)
    generated_lean = write_scaffold(formal_packet, repo_root / "reports" / "research" / "generated_lean")
    compile_result = close(generated_lean, repo_root)

    activity.extend(
        [
            {"phase": "socratic_engine", "ts": utc_now(), "invariant_items": len(dialogue_packet.get("lanes", {}).get("invariant_extraction", []))},
            {"phase": "pauli_audit", "ts": utc_now(), "admission_ok": bool(audited_packet.get("admission_ok", False)), "rejected": len(audited_packet.get("rejected", []))},
            {"phase": "lean_designer", "ts": utc_now(), "targets": len(formal_packet.get("targets", []))},
            {"phase": "lean_coder", "ts": utc_now(), "generated_file": str(generated_lean)},
            {"phase": "compiler_loop", "ts": utc_now(), "ok": compile_result.ok, "statement_invalid": compile_result.statement_invalid},
        ]
    )

    if not gate_failures:
        report_text = synthesize_report(
            client=client,
            model=args.writer_model,
            goal=args.goal,
            plan=plan,
            findings=findings,
            verification=verification,
            activity_log=activity,
        )
        report_out.parent.mkdir(parents=True, exist_ok=True)
        report_out.write_text(report_text, encoding="utf-8")
        status = "completed"

    state = {
        "generated_at": utc_now(),
        "status": status,
        "goal": args.goal,
        "constraints": constraints,
        "allowed_sources": allowed_sources,
        "trusted_domains": trusted_domains,
        "models": {
            "planner": args.planner_model,
            "research": args.research_model,
            "verifier": args.verifier_model,
            "writer": args.writer_model,
        },
        "tools": {"vector_store_ids": args.vector_store_id, "mcp_servers": mcp_servers, "count": len(tools)},
        "plan": plan,
        "findings": findings,
        "verification": verification,
        "gates": {
            "citations_ok": citations_ok,
            "verifier_ok": verifier_ok,
            "failures": gate_failures,
        },
        "autonomous_pipeline": {
            "evidence_packet": evidence_packet.to_dict(),
            "dialogue_packet": dialogue_packet,
            "audited_packet": audited_packet,
            "formal_packet": formal_packet,
            "generated_lean_file": str(generated_lean),
            "compiler_result": {
                "ok": compile_result.ok,
                "statement_invalid": compile_result.statement_invalid,
                "feedback": compile_result.feedback,
                "command": compile_result.command,
            },
        },
        "activity_log": activity,
        "report_out": str(report_out) if report_text else "",
    }
    write_json(state_out, state)

    packet = build_packet_from_state(
        {"goal": args.goal, "allowed_sources": allowed_sources, "trusted_domains": trusted_domains, "models": state.get("models", {}), "findings": findings, "verification": verification},
        packet_id=f"rp-{stamp}-{slug}",
        state_path=str(state_out),
    )
    packet_errors = validate_packet(packet)
    if packet_errors:
        state["status"] = "blocked_by_packet_validation"
        state["packet_validation_errors"] = packet_errors
        write_json(state_out, state)
        print(f"[autonomous-math] state: {state_out}")
        print("[autonomous-math] packet validation failed:")
        for err in packet_errors:
            print(f"  - {err}")
        sys.exit(3)
    write_json(packet_out, packet)
    state["research_packet_out"] = str(packet_out)
    write_json(state_out, state)
    ingest(packet=evidence_packet, run_state=state, out_file=memory_log)

    print(f"[autonomous-math] state: {state_out}")
    print(f"[autonomous-math] research packet: {packet_out}")
    print(f"[autonomous-math] memory: {memory_log}")
    if report_text:
        print(f"[autonomous-math] report: {report_out}")
    if gate_failures:
        print("[autonomous-math] blocked by gates:")
        for f in gate_failures:
            print(f"  - {f}")
        sys.exit(2)
    sys.exit(0)


if __name__ == "__main__":
    main()
