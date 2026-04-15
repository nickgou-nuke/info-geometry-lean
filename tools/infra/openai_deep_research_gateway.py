#!/usr/bin/env python3
"""Codex-facing MCP gateway for OpenAI Deep Research.

Architecture:
1) Codex-facing MCP tools (`dr_start`, `dr_status`, `dr_result`, ...)
2) Deep-research execution via OpenAI Responses API
3) Optional packet-ingest bridge into `handover/injections/*`

This script intentionally keeps the Codex tool surface narrow while allowing the
underlying deep-research run to use web/file search and nested remote MCP data
sources.
"""

from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Literal

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[2]))

try:
    from openai import OpenAI
except Exception as exc:  # pragma: no cover - runtime dependency guard
    raise SystemExit("Missing dependency: openai (pip install openai)") from exc

try:
    from fastmcp import FastMCP
except Exception as exc:  # pragma: no cover - runtime dependency guard
    raise SystemExit("Missing dependency: fastmcp (pip install fastmcp)") from exc

from tools.infra.injection_common import (
    acquire_packet_lock,
    append_history_event,
    injections_root,
    repo_root,
    resolve_packet,
    validate_packet_schema,
    write_json_atomic,
)

DRModel = Literal["o4-mini-deep-research", "o3-deep-research"]
UseAs = Literal["creative", "verification", "both"]

DEFAULT_MODEL = os.environ.get("OPENAI_DR_DEFAULT_MODEL", "o4-mini-deep-research")
DEFAULT_PREFLIGHT_MODEL = os.environ.get("OPENAI_DR_PREFLIGHT_MODEL", "gpt-5.4-mini")
DEFAULT_TIMEOUT_SEC = float(os.environ.get("OPENAI_DR_TIMEOUT_SEC", "3600"))

TERMINAL_STATUSES = {"completed", "failed", "cancelled", "canceled", "incomplete", "errored"}

INCLUDE_TOOL_TRACES = [
    "web_search_call.action.sources",
    "file_search_call.results",
    "code_interpreter_call.outputs",
    "mcp_call",
]

client = OpenAI(timeout=DEFAULT_TIMEOUT_SEC)

mcp = FastMCP(
    name="openai-deep-research-gateway",
    instructions=(
        "Launch and retrieve OpenAI deep-research jobs. "
        "Use dr_start first, then dr_status and dr_result."
    ),
)


def _asdict(obj: Any) -> dict[str, Any]:
    if isinstance(obj, dict):
        return obj
    if hasattr(obj, "model_dump"):
        return obj.model_dump()  # type: ignore[no-any-return]
    if hasattr(obj, "to_dict"):
        return obj.to_dict()  # type: ignore[no-any-return]
    return {"repr": repr(obj)}


def _extract_output_text(resp: Any) -> str:
    text = getattr(resp, "output_text", None)
    if isinstance(text, str) and text.strip():
        return text

    payload = _asdict(resp)
    text2 = payload.get("output_text")
    if isinstance(text2, str):
        return text2
    return ""


def _extract_status(resp: Any) -> str:
    status = getattr(resp, "status", None)
    if isinstance(status, str):
        return status
    payload = _asdict(resp)
    status2 = payload.get("status")
    return status2 if isinstance(status2, str) else "unknown"


def _build_tools(
    *,
    web: bool,
    vector_store_ids: list[str] | None,
    remote_mcp_url: str | None,
    remote_mcp_label: str | None,
    use_code_interpreter: bool,
) -> list[dict[str, Any]]:
    tools: list[dict[str, Any]] = []

    if web:
        tools.append({"type": "web_search_preview"})

    if vector_store_ids:
        tools.append(
            {
                "type": "file_search",
                "vector_store_ids": vector_store_ids[:2],
            }
        )

    if remote_mcp_url:
        tools.append(
            {
                "type": "mcp",
                "server_label": remote_mcp_label or "private_data",
                "server_url": remote_mcp_url,
                "require_approval": "never",
            }
        )

    if use_code_interpreter:
        tools.append(
            {
                "type": "code_interpreter",
                "container": {"type": "auto"},
            }
        )

    if not tools:
        raise ValueError(
            "Deep research requires at least one data source: web, file_search, or remote MCP."
        )

    return tools


def _normalize_brief(brief: str) -> str:
    s = brief.strip()
    if not s:
        raise ValueError("brief must be non-empty")
    return s


def _iter_dicts(node: Any) -> Iterable[dict[str, Any]]:
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from _iter_dicts(value)
        return
    if isinstance(node, list):
        for item in node:
            yield from _iter_dicts(item)


def _collect_evidence_rows(output_payload: Any) -> list[dict[str, str]]:
    seen: dict[str, dict[str, str]] = {}

    for d in _iter_dicts(output_payload):
        url = d.get("url")
        if not isinstance(url, str) or not url.strip():
            continue
        key = url.strip()
        if key in seen:
            continue
        row: dict[str, str] = {
            "url": key,
            "summary": "Source captured from deep-research tool trace.",
        }
        title = d.get("title")
        if isinstance(title, str) and title.strip():
            row["title"] = title.strip()
        date = d.get("date")
        if isinstance(date, str) and date.strip():
            row["date"] = date.strip()
        source_type = d.get("type")
        if isinstance(source_type, str) and source_type.strip():
            row["relevance"] = source_type.strip()
        seen[key] = row

    return list(seen.values())[:80]


def _ensure_research(packet: dict[str, Any]) -> dict[str, Any]:
    research = packet.setdefault("research", {})
    if not isinstance(research, dict):
        raise ValueError("packet.research must be an object")

    workflow = research.setdefault(
        "workflow",
        {
            "mode": "gemini-hermes-codex",
            "creative_provider": "gemini_cli",
            "verification_provider": "hermes",
            "coding_provider": "codex",
            "creative_complete": False,
            "verification_complete": False,
        },
    )
    if not isinstance(workflow, dict):
        raise ValueError("packet.research.workflow must be an object")

    segments = research.setdefault("segments", [])
    if not isinstance(segments, list):
        raise ValueError("packet.research.segments must be a list")
    return research


def _find_or_create_segment(research: dict[str, Any], segment_id: str, seed_text: str) -> dict[str, Any]:
    segments = research["segments"]
    for seg in segments:
        if isinstance(seg, dict) and str(seg.get("segment_id", "")).strip() == segment_id:
            return seg

    seg = {
        "segment_id": segment_id,
        "title": segment_id,
        "source_span": "",
        "seed_text": seed_text,
        "creative_notes": "",
        "enriched_context": "",
        "claims": [],
        "inference_flags": [],
        "confidence": 0.0,
        "literature_evidence": [],
    }
    segments.append(seg)
    return seg


def _merge_text(existing: str, incoming: str, append_mode: bool) -> str:
    incoming_s = incoming.strip()
    if not incoming_s:
        return existing
    if append_mode and existing.strip():
        return f"{existing.rstrip()}\n\n{incoming_s}"
    return incoming_s


def _merge_evidence(existing: list[dict[str, str]], incoming: list[dict[str, str]]) -> list[dict[str, str]]:
    seen: dict[str, dict[str, str]] = {}
    for row in existing + incoming:
        if not isinstance(row, dict):
            continue
        url = row.get("url")
        summary = row.get("summary")
        if not isinstance(url, str) or not url.strip():
            continue
        if not isinstance(summary, str) or not summary.strip():
            continue
        key = url.strip()
        if key in seen:
            continue
        clean: dict[str, str] = {"url": key, "summary": summary.strip()}
        for k in ("title", "date", "relevance"):
            v = row.get(k)
            if isinstance(v, str) and v.strip():
                clean[k] = v.strip()
        seen[key] = clean
    return list(seen.values())[:80]


def _packet_ingest(
    *,
    response_id: str,
    result_text: str,
    output_payload: Any,
    packet_ref: str,
    segment_id: str,
    seed_text: str,
    use_as: UseAs,
    append_mode: bool,
    mark_creative_complete: bool,
    mark_verification_complete: bool,
    note: str,
) -> dict[str, Any]:
    root = repo_root()
    injections = injections_root(root)
    packet_path = resolve_packet(injections, packet_ref)
    packet_id = packet_path.stem

    lock_owner = f"openai_dr_ingest:{os.getpid()}:{packet_id}:{segment_id}"
    with acquire_packet_lock(packet_id, lock_owner, block=True):
        packet = json.loads(packet_path.read_text(encoding="utf-8"))
        validate_packet_schema(packet)

        research = _ensure_research(packet)
        segment = _find_or_create_segment(research, segment_id, seed_text)

        workflow = research["workflow"]
        if use_as in ("creative", "both"):
            segment["creative_notes"] = _merge_text(
                str(segment.get("creative_notes", "")),
                result_text,
                append_mode,
            )
            workflow["creative_provider"] = "openai_deep_research"

        if use_as in ("verification", "both"):
            segment["enriched_context"] = _merge_text(
                str(segment.get("enriched_context", "")),
                result_text,
                append_mode,
            )
            workflow["verification_provider"] = "openai_deep_research"

        evidence_rows = _collect_evidence_rows(output_payload)
        existing_evidence = segment.get("literature_evidence", [])
        if not isinstance(existing_evidence, list):
            existing_evidence = []
        segment["literature_evidence"] = _merge_evidence(existing_evidence, evidence_rows)

        if mark_creative_complete:
            workflow["creative_complete"] = True
        if mark_verification_complete:
            workflow["verification_complete"] = True

        note_parts = [f"response_id={response_id}", f"segment={segment_id}", f"use_as={use_as}"]
        if note.strip():
            note_parts.append(note.strip())
        append_history_event(
            packet,
            event="openai-deep-research:ingest",
            note="; ".join(note_parts),
            idempotent=False,
        )

        validate_packet_schema(packet)
        write_json_atomic(packet_path, packet)

    return {
        "packet": str(packet_path),
        "packet_id": packet_id,
        "segment_id": segment_id,
        "evidence_count": len(_collect_evidence_rows(output_payload)),
    }


@mcp.tool()
def dr_preflight_rewrite(
    brief: str,
    rewrite_instructions: str | None = None,
    model: str = DEFAULT_PREFLIGHT_MODEL,
) -> dict[str, Any]:
    """Rewrite a rough research ask into a deep-research-ready brief."""
    prompt = _normalize_brief(brief)
    prompt_instructions = rewrite_instructions or (
        "Rewrite the user request into a complete deep-research brief. "
        "Preserve intent, define scope, add explicit deliverables, and include "
        "citation expectations. Return plain text only."
    )

    resp = client.responses.create(
        model=model,
        input=prompt,
        instructions=prompt_instructions,
        store=False,
    )

    return {
        "response_id": getattr(resp, "id", ""),
        "model": model,
        "rewritten_brief": _extract_output_text(resp),
        "status": _extract_status(resp),
    }


@mcp.tool()
def dr_start(
    brief: str,
    instructions: str | None = None,
    model: DRModel = DEFAULT_MODEL,  # type: ignore[assignment]
    web: bool = True,
    vector_store_ids: list[str] | None = None,
    remote_mcp_url: str | None = None,
    remote_mcp_label: str | None = None,
    use_code_interpreter: bool = False,
    max_tool_calls: int | None = None,
    store: bool = True,
) -> dict[str, Any]:
    """Start a deep-research job and return response_id for polling."""
    normalized_brief = _normalize_brief(brief)

    resp = client.responses.create(
        model=model,
        input=normalized_brief,
        instructions=instructions,
        background=True,
        reasoning={"summary": "auto"},
        max_tool_calls=max_tool_calls,
        store=store,
        tools=_build_tools(
            web=web,
            vector_store_ids=vector_store_ids,
            remote_mcp_url=remote_mcp_url,
            remote_mcp_label=remote_mcp_label,
            use_code_interpreter=use_code_interpreter,
        ),
    )

    return {
        "response_id": getattr(resp, "id", ""),
        "status": _extract_status(resp),
        "model": model,
    }


@mcp.tool()
def dr_status(response_id: str) -> dict[str, Any]:
    """Retrieve current deep-research job status."""
    rid = response_id.strip()
    if not rid:
        raise ValueError("response_id must be non-empty")

    resp = client.responses.retrieve(rid)
    payload = _asdict(resp)
    return {
        "response_id": getattr(resp, "id", rid),
        "status": _extract_status(resp),
        "error": payload.get("error"),
        "incomplete_details": payload.get("incomplete_details"),
    }


@mcp.tool()
def dr_result(
    response_id: str,
    include_tool_traces: bool = True,
) -> dict[str, Any]:
    """Fetch deep-research result text and optional tool traces."""
    rid = response_id.strip()
    if not rid:
        raise ValueError("response_id must be non-empty")

    if include_tool_traces:
        resp = client.responses.retrieve(rid, include=INCLUDE_TOOL_TRACES)
    else:
        resp = client.responses.retrieve(rid)

    payload = _asdict(resp)
    return {
        "response_id": getattr(resp, "id", rid),
        "status": _extract_status(resp),
        "text": _extract_output_text(resp),
        "output": payload.get("output", []),
        "error": payload.get("error"),
        "incomplete_details": payload.get("incomplete_details"),
    }


@mcp.tool()
def dr_run_blocking(
    brief: str,
    instructions: str | None = None,
    model: DRModel = DEFAULT_MODEL,  # type: ignore[assignment]
    web: bool = True,
    vector_store_ids: list[str] | None = None,
    remote_mcp_url: str | None = None,
    remote_mcp_label: str | None = None,
    use_code_interpreter: bool = False,
    max_tool_calls: int | None = None,
    store: bool = True,
    poll_interval_sec: float = 5.0,
    timeout_sec: float = 1800.0,
) -> dict[str, Any]:
    """Convenience helper: start a job and poll until terminal state."""
    started = dr_start(
        brief=brief,
        instructions=instructions,
        model=model,
        web=web,
        vector_store_ids=vector_store_ids,
        remote_mcp_url=remote_mcp_url,
        remote_mcp_label=remote_mcp_label,
        use_code_interpreter=use_code_interpreter,
        max_tool_calls=max_tool_calls,
        store=store,
    )

    response_id = str(started.get("response_id", "")).strip()
    if not response_id:
        raise RuntimeError("dr_start returned empty response_id")

    deadline = time.monotonic() + max(1.0, timeout_sec)
    last_status = str(started.get("status", "unknown"))

    while time.monotonic() < deadline:
        st = dr_status(response_id)
        last_status = str(st.get("status", "unknown"))
        if last_status in TERMINAL_STATUSES:
            result = dr_result(response_id)
            result["poll_status"] = last_status
            return result
        time.sleep(max(0.5, poll_interval_sec))

    return {
        "response_id": response_id,
        "status": "timeout",
        "last_status": last_status,
        "timeout_sec": timeout_sec,
    }


@mcp.tool()
def dr_ingest_result_to_packet(
    response_id: str,
    packet: str,
    segment_id: str = "S1",
    seed_text: str = "",
    use_as: UseAs = "verification",
    include_tool_traces: bool = True,
    append_mode: bool = True,
    mark_creative_complete: bool = False,
    mark_verification_complete: bool = False,
    note: str = "",
) -> dict[str, Any]:
    """Retrieve deep-research result and ingest it into an injection packet segment."""
    rid = response_id.strip()
    if not rid:
        raise ValueError("response_id must be non-empty")

    result = dr_result(response_id=rid, include_tool_traces=include_tool_traces)
    status = str(result.get("status", ""))
    if status != "completed":
        return {
            "ok": False,
            "reason": "response_not_completed",
            "response_id": rid,
            "status": status,
        }

    ingest = _packet_ingest(
        response_id=rid,
        result_text=str(result.get("text", "")),
        output_payload=result.get("output", []),
        packet_ref=packet,
        segment_id=segment_id.strip() or "S1",
        seed_text=seed_text,
        use_as=use_as,
        append_mode=append_mode,
        mark_creative_complete=mark_creative_complete,
        mark_verification_complete=mark_verification_complete,
        note=note,
    )

    return {
        "ok": True,
        "response_id": rid,
        "status": status,
        "packet": ingest["packet"],
        "packet_id": ingest["packet_id"],
        "segment_id": ingest["segment_id"],
        "evidence_count": ingest["evidence_count"],
    }


def main() -> int:
    transport = os.environ.get("OPENAI_DR_MCP_TRANSPORT", "")
    if not transport:
        mcp.run()
        return 0

    # Compatibility path for fastmcp versions that expose transport kwargs.
    kwargs: dict[str, Any] = {"transport": transport}
    host = os.environ.get("OPENAI_DR_MCP_HOST", "127.0.0.1")
    port = os.environ.get("OPENAI_DR_MCP_PORT", "8787")
    try:
        kwargs["host"] = host
        kwargs["port"] = int(port)
        mcp.run(**kwargs)
    except TypeError:
        mcp.run()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
