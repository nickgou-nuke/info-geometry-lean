#!/usr/bin/env python3
"""Retriever/reader stage for deep research controller."""

from __future__ import annotations

import json
from typing import Any

from .common import output_text, parse_json_text, to_dict


RETRIEVER_SYSTEM = (
    "You are a research evidence extractor. "
    "Use tools only from allowed_sources. "
    "Return strict JSON with claims, evidence, open_questions, citations."
)


def build_tools(
    *,
    allowed_sources: list[str],
    trusted_domains: list[str],
    vector_store_ids: list[str],
    mcp_servers: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    tools: list[dict[str, Any]] = []

    if "web" in allowed_sources:
        if trusted_domains:
            tools.append({"type": "web_search", "filters": {"allowed_domains": trusted_domains}})
        else:
            tools.append({"type": "web_search"})

    if "files" in allowed_sources and vector_store_ids:
        tools.append({"type": "file_search", "vector_store_ids": vector_store_ids[:5]})

    if "mcp" in allowed_sources:
        for server in mcp_servers:
            server_url = server.get("server_url")
            if not isinstance(server_url, str) or not server_url.strip():
                continue
            tools.append(
                {
                    "type": "mcp",
                    "server_label": str(server.get("server_label", "remote_mcp")).strip() or "remote_mcp",
                    "server_url": server_url.strip(),
                    "require_approval": str(server.get("require_approval", "never")).strip() or "never",
                }
            )

    return tools


def _collect_urls(node: Any, out: set[str]) -> None:
    if isinstance(node, dict):
        for k, v in node.items():
            if k == "url" and isinstance(v, str) and v.strip():
                out.add(v.strip())
            else:
                _collect_urls(v, out)
        return
    if isinstance(node, list):
        for item in node:
            _collect_urls(item, out)


def normalize_finding(payload: Any, subq_id: str) -> dict[str, Any]:
    if not isinstance(payload, dict):
        payload = {}

    claims = payload.get("claims", [])
    if not isinstance(claims, list):
        claims = []
    normalized_claims: list[dict[str, Any]] = []
    for row in claims:
        if not isinstance(row, dict):
            continue
        text = str(row.get("claim", "")).strip()
        if not text:
            continue
        cits = row.get("citations", [])
        if not isinstance(cits, list):
            cits = []
        cits = [str(c).strip() for c in cits if str(c).strip()]
        normalized_claims.append(
            {
                "claim": text,
                "evidence_summary": str(row.get("evidence_summary", "")).strip(),
                "citations": cits,
            }
        )

    evidence = payload.get("evidence", [])
    if not isinstance(evidence, list):
        evidence = []
    normalized_evidence: list[dict[str, Any]] = []
    for row in evidence:
        if not isinstance(row, dict):
            continue
        normalized_evidence.append(
            {
                "source_type": str(row.get("source_type", "")).strip(),
                "title": str(row.get("title", "")).strip(),
                "url": str(row.get("url", "")).strip(),
                "snippet": str(row.get("snippet", "")).strip(),
            }
        )

    oq = payload.get("open_questions", [])
    if not isinstance(oq, list):
        oq = []
    open_questions = [str(x).strip() for x in oq if str(x).strip()]

    confidence = payload.get("confidence", 0.0)
    try:
        confidence = float(confidence)
    except Exception:
        confidence = 0.0

    return {
        "subquestion_id": subq_id,
        "claims": normalized_claims,
        "evidence": normalized_evidence,
        "open_questions": open_questions,
        "confidence": max(0.0, min(1.0, confidence)),
    }


def research_subquestion(
    *,
    client: Any,
    model: str,
    subquestion: dict[str, Any],
    goal: str,
    constraints: list[str],
    allowed_sources: list[str],
    tools: list[dict[str, Any]],
) -> dict[str, Any]:
    subq_id = str(subquestion.get("id", "sq")).strip() or "sq"
    q = str(subquestion.get("question", "")).strip()
    done_when = str(subquestion.get("done_when", "")).strip()
    sq_sources = subquestion.get("sources", [])
    if not isinstance(sq_sources, list):
        sq_sources = []
    sq_sources = [str(s) for s in sq_sources if str(s) in allowed_sources]

    prompt = {
        "task": "research_subquestion",
        "goal": goal,
        "subquestion": {
            "id": subq_id,
            "question": q,
            "done_when": done_when,
            "sources": sq_sources,
        },
        "constraints": constraints,
        "allowed_sources": allowed_sources,
        "required_output_schema": {
            "subquestion_id": "string",
            "claims": [
                {
                    "claim": "string",
                    "evidence_summary": "string",
                    "citations": ["string"],
                }
            ],
            "evidence": [
                {
                    "source_type": "string",
                    "title": "string",
                    "url": "string",
                    "snippet": "string",
                }
            ],
            "open_questions": ["string"],
            "confidence": "number 0..1",
        },
        "rules": [
            "Every material claim must include at least one citation.",
            "If evidence is insufficient, keep confidence low and add open_questions.",
            "Return strict JSON object only.",
        ],
    }

    include = [
        "web_search_call.action.sources",
        "file_search_call.results",
        "mcp_call",
    ]

    resp = client.responses.create(
        model=model,
        tools=tools,
        input=[
            {"role": "system", "content": RETRIEVER_SYSTEM},
            {"role": "user", "content": json.dumps(prompt, ensure_ascii=True)},
        ],
        text={"format": {"type": "json_object"}},
        include=include,
    )

    parsed = parse_json_text(output_text(resp))
    finding = normalize_finding(parsed, subq_id)

    resp_payload = to_dict(resp)
    urls: set[str] = set()
    _collect_urls(resp_payload, urls)
    finding["tool_trace_urls"] = sorted(urls)[:120]
    finding["response_id"] = str(resp_payload.get("id", ""))
    return finding

