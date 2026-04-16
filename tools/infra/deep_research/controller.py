#!/usr/bin/env python3
"""Official-pattern deep research controller.

Implements:
1) planner pass
2) controlled retrieval pass
3) verifier pass
4) final synthesis pass

With explicit source constraints, persisted state, and hard gates.
"""

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


ALLOWED_SOURCES = {"web", "files", "mcp"}


def _make_client() -> Any:
    try:
        from openai import OpenAI
    except Exception as exc:  # pragma: no cover
        raise SystemExit("Missing dependency: openai (pip install openai)") from exc
    return OpenAI()


def _slug(text: str) -> str:
    out = []
    for ch in text.lower():
        if ch.isalnum():
            out.append(ch)
        elif ch in {" ", "-", "_"}:
            out.append("-")
    s = "".join(out).strip("-")
    while "--" in s:
        s = s.replace("--", "-")
    return s[:64] or "research"


def _parse_allowed_sources(value: str) -> list[str]:
    items = [x.strip() for x in value.split(",") if x.strip()]
    out = []
    for item in items:
        if item not in ALLOWED_SOURCES:
            raise ValueError(f"Unknown source '{item}'. Allowed: web,files,mcp")
        if item not in out:
            out.append(item)
    if not out:
        raise ValueError("allowed-sources cannot be empty")
    return out


def _parse_mcp_servers(values: list[str]) -> list[dict[str, Any]]:
    servers: list[dict[str, Any]] = []
    for raw in values:
        obj = json.loads(raw)
        if not isinstance(obj, dict):
            raise ValueError("--mcp-server must be a JSON object")
        if "server_url" not in obj:
            raise ValueError("--mcp-server JSON must include server_url")
        servers.append(obj)
    return servers


def _ensure_claim_citations(findings: dict[str, Any]) -> tuple[bool, list[str]]:
    missing: list[str] = []
    for sq_id, payload in findings.items():
        if not isinstance(payload, dict):
            missing.append(f"{sq_id}: finding payload is not object")
            continue
        claims = payload.get("claims", [])
        if not isinstance(claims, list):
            missing.append(f"{sq_id}: claims is not list")
            continue
        for i, claim in enumerate(claims, start=1):
            if not isinstance(claim, dict):
                missing.append(f"{sq_id}: claim #{i} is not object")
                continue
            text = str(claim.get("claim", "")).strip()
            if not text:
                continue
            cits = claim.get("citations", [])
            if not isinstance(cits, list) or not any(str(c).strip() for c in cits):
                missing.append(f"{sq_id}: claim #{i} has no citation")
    return (len(missing) == 0), missing


def _required_subquestions_covered(plan: dict[str, Any], findings: dict[str, Any]) -> tuple[bool, list[str]]:
    missing: list[str] = []
    subqs = plan.get("subquestions", [])
    if not isinstance(subqs, list):
        return False, ["plan.subquestions invalid"]
    for row in subqs:
        if not isinstance(row, dict):
            continue
        sq_id = str(row.get("id", "")).strip()
        if not sq_id:
            continue
        if sq_id not in findings:
            missing.append(sq_id)
    return (len(missing) == 0), missing


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--goal", required=True)
    p.add_argument("--constraint", action="append", default=[], help="Repeatable constraint.")
    p.add_argument("--allowed-sources", default="web", help="Comma-separated from: web,files,mcp")
    p.add_argument("--trusted-domain", action="append", default=[], help="Repeatable trusted domain.")
    p.add_argument("--vector-store-id", action="append", default=[], help="Repeatable vector store id for file_search.")
    p.add_argument(
        "--mcp-server",
        action="append",
        default=[],
        help='Repeatable JSON object: {"server_label":"name","server_url":"https://...","require_approval":"never"}',
    )
    p.add_argument("--planner-model", default=os.environ.get("OPENAI_DR_PLANNER_MODEL", "gpt-5"))
    p.add_argument("--research-model", default=os.environ.get("OPENAI_DR_RESEARCH_MODEL", "gpt-5"))
    p.add_argument("--verifier-model", default=os.environ.get("OPENAI_DR_VERIFIER_MODEL", "gpt-5"))
    p.add_argument("--writer-model", default=os.environ.get("OPENAI_DR_WRITER_MODEL", "gpt-5"))
    p.add_argument("--max-extra-rounds", type=int, default=1)
    p.add_argument("--state-out", default="")
    p.add_argument("--report-out", default="")
    p.add_argument(
        "--research-packet-out",
        default="",
        help="Output path for typed research packet (default: quarantine/hermes_memory/research_packets/<timestamp>-<slug>.json).",
    )
    return p.parse_args()


def main() -> None:
    args = parse_args()
    allowed_sources = _parse_allowed_sources(args.allowed_sources)
    trusted_domains = [d.strip() for d in args.trusted_domain if d.strip()]
    mcp_servers = _parse_mcp_servers(args.mcp_server)

    repo_root = Path(__file__).resolve().parents[3]
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    default_state_out = repo_root / "reports" / "research" / f"deep-research-state-{stamp}-{_slug(args.goal)}.json"
    default_report_out = repo_root / "reports" / "research" / f"deep-research-report-{stamp}-{_slug(args.goal)}.md"
    default_packet_out = repo_root / "quarantine" / "hermes_memory" / "research_packets" / f"{stamp}-{_slug(args.goal)}.json"
    state_out = Path(args.state_out).resolve() if args.state_out else default_state_out
    report_out = Path(args.report_out).resolve() if args.report_out else default_report_out
    packet_out = Path(args.research_packet_out).resolve() if args.research_packet_out else default_packet_out

    constraints = list(args.constraint)
    if not constraints:
        constraints = [
            "Use only allowed sources.",
            "Cite every material claim.",
            "Surface unresolved conflicts explicitly.",
        ]

    client = _make_client()
    activity_log: list[dict[str, Any]] = []
    findings: dict[str, Any] = {}

    # 1) Planner pass
    plan = create_plan(
        client=client,
        model=args.planner_model,
        goal=args.goal,
        constraints=constraints,
        allowed_sources=allowed_sources,
        trusted_domains=trusted_domains,
    )
    activity_log.append(
        {
            "ts": utc_now(),
            "phase": "plan",
            "model": args.planner_model,
            "subquestion_count": len(plan.get("subquestions", [])),
        }
    )

    # 2) Controlled execution loop
    tools = build_tools(
        allowed_sources=allowed_sources,
        trusted_domains=trusted_domains,
        vector_store_ids=args.vector_store_id,
        mcp_servers=mcp_servers,
    )
    if not tools:
        raise SystemExit("No enabled tools. Configure allowed sources + tool configuration.")

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
        activity_log.append(
            {
                "ts": utc_now(),
                "phase": "retrieve",
                "model": args.research_model,
                "subquestion_id": sq_id,
                "claims": len(finding.get("claims", [])),
                "evidence": len(finding.get("evidence", [])),
                "confidence": finding.get("confidence", 0.0),
            }
        )

    # 3) Verifier pass
    verification = verify_research(
        client=client,
        model=args.verifier_model,
        goal=args.goal,
        plan=plan,
        findings=findings,
        constraints=constraints,
    )
    activity_log.append(
        {
            "ts": utc_now(),
            "phase": "verify",
            "model": args.verifier_model,
            "more_research_required": bool(verification.get("more_research_required", False)),
            "missing_subquestions": len(verification.get("missing_subquestions", [])),
            "unresolved_conflicts": len(verification.get("unresolved_conflicts", [])),
        }
    )

    extra_round = 0
    while bool(verification.get("more_research_required", False)) and extra_round < max(0, args.max_extra_rounds):
        extra_round += 1
        missing_subqs = verification.get("missing_subquestions", [])
        if not isinstance(missing_subqs, list):
            break
        for subq in missing_subqs:
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
            activity_log.append(
                {
                    "ts": utc_now(),
                    "phase": "retrieve_extra",
                    "round": extra_round,
                    "model": args.research_model,
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
        activity_log.append(
            {
                "ts": utc_now(),
                "phase": "verify",
                "round": extra_round,
                "model": args.verifier_model,
                "more_research_required": bool(verification.get("more_research_required", False)),
                "missing_subquestions": len(verification.get("missing_subquestions", [])),
                "unresolved_conflicts": len(verification.get("unresolved_conflicts", [])),
            }
        )

    # 4) Verification gates before synthesis
    covered_ok, missing_ids = _required_subquestions_covered(plan, findings)
    citation_ok, citation_missing = _ensure_claim_citations(findings)
    verifier_ok = not bool(verification.get("more_research_required", False))

    gate_failures: list[str] = []
    if not covered_ok:
        gate_failures.append(f"required subquestions missing: {missing_ids}")
    if not citation_ok:
        gate_failures.append(f"uncited material claims: {citation_missing}")
    if not verifier_ok:
        gate_failures.append("verifier requested additional research")

    report_md = ""
    status = "completed"
    if gate_failures:
        status = "blocked_by_gates"
    else:
        report_md = synthesize_report(
            client=client,
            model=args.writer_model,
            goal=args.goal,
            plan=plan,
            findings=findings,
            verification=verification,
            activity_log=activity_log,
        )
        report_out.parent.mkdir(parents=True, exist_ok=True)
        report_out.write_text(report_md, encoding="utf-8")
        activity_log.append(
            {
                "ts": utc_now(),
                "phase": "synthesize",
                "model": args.writer_model,
                "report_out": str(report_out),
            }
        )

    state = {
        "generated_at": utc_now(),
        "status": status,
        "goal": args.goal,
        "constraints": constraints,
        "allowed_sources": allowed_sources,
        "trusted_domains": trusted_domains,
        "tools_config": {
            "vector_store_ids": args.vector_store_id,
            "mcp_servers": mcp_servers,
            "tool_count": len(tools),
        },
        "models": {
            "planner": args.planner_model,
            "research": args.research_model,
            "verifier": args.verifier_model,
            "writer": args.writer_model,
        },
        "plan": plan,
        "findings": findings,
        "verification": verification,
        "gates": {
            "required_subquestions_covered": covered_ok,
            "all_material_claims_cited": citation_ok,
            "verifier_requires_more_research": bool(verification.get("more_research_required", False)),
            "failures": gate_failures,
        },
        "activity_log": activity_log,
        "report_out": str(report_out) if report_md else "",
    }
    write_json(state_out, state)

    packet = build_packet_from_state(
        state,
        packet_id=f"rp-{stamp}-{_slug(args.goal)}",
        state_path=str(state_out),
    )
    packet_errors = validate_packet(packet)
    if packet_errors:
        state["status"] = "blocked_by_packet_validation"
        state.setdefault("packet_validation_errors", packet_errors)
        write_json(state_out, state)
        print(f"[deep-research] state: {state_out}")
        print("[deep-research] packet validation failed:")
        for err in packet_errors:
            print(f"  - {err}")
        sys.exit(3)
    write_json(packet_out, packet)

    print(f"[deep-research] state: {state_out}")
    print(f"[deep-research] research packet: {packet_out}")
    if report_md:
        print(f"[deep-research] report: {report_out}")
    if gate_failures:
        print("[deep-research] blocked by verification gates:")
        for x in gate_failures:
            print(f"  - {x}")
        sys.exit(2)
    sys.exit(0)


if __name__ == "__main__":
    main()
