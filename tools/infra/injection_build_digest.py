#!/usr/bin/env python3
"""Build a cited literature digest markdown from an injection packet."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[2]))

from tools.infra.injection_common import (
    acquire_packet_lock,
    append_history_event,
    injections_root,
    repo_root,
    resolve_packet,
    validate_packet_schema,
    write_json_atomic,
    write_run_manifest,
)


def normalize_sources(packet: dict[str, Any]) -> list[dict[str, str]]:
    research = packet.get("research", {})
    raw_sources = research.get("sources", [])
    out: list[dict[str, str]] = []
    for s in raw_sources:
        if isinstance(s, dict):
            kind = str(s.get("kind", "source"))
            ref = str(s.get("ref", "")).strip()
            title = str(s.get("title", "")).strip()
            date = str(s.get("date", "")).strip()
        else:
            kind = "source"
            ref = str(s).strip()
            title = ""
            date = ""
        if ref:
            out.append({"kind": kind, "ref": ref, "title": title, "date": date})
    return out


def format_sources_md(sources: list[dict[str, str]]) -> tuple[str, list[str]]:
    lines: list[str] = []
    keys: list[str] = []
    for i, s in enumerate(sources, start=1):
        sid = f"S{i}"
        keys.append(sid)
        kind = s["kind"].upper()
        ref = s["ref"]
        title = s.get("title", "")
        date = s.get("date", "")
        extras = []
        if title:
            extras.append(f"title: {title}")
        if date:
            extras.append(f"date: {date}")
        tail = f" ({'; '.join(extras)})" if extras else ""
        lines.append(f"- [{sid}] {kind}: {ref}{tail}")
    if not lines:
        lines.append("- (no sources recorded)")
    return "\n".join(lines), keys


def as_list(v: Any) -> list[str]:
    if isinstance(v, list):
        return [str(x) for x in v if str(x).strip()]
    if isinstance(v, str) and v.strip():
        return [v.strip()]
    return []


def latest_history_time(packet: dict[str, Any], fallback: str) -> str:
    history = packet.get("history", [])
    if isinstance(history, list):
        times = [str(h.get("at", "")).strip() for h in history if isinstance(h, dict)]
        times = [t for t in times if t]
        if times:
            return max(times)
    return fallback


def main() -> int:
    parser = argparse.ArgumentParser(description="Build a markdown digest from an injection packet")
    parser.add_argument("packet", help="Packet id or packet path")
    parser.add_argument("--out", default=None, help="Output markdown path (default: handover/injections/digests/<id>.md)")
    parser.add_argument("--update-packet", action="store_true", help="Append digest event to packet history")
    args = parser.parse_args()

    root = repo_root()
    injections = injections_root(root)

    packet_path = resolve_packet(injections, args.packet)
    lane = packet_path.parent.name
    packet = json.loads(packet_path.read_text(encoding="utf-8"))
    validate_packet_schema(packet)

    packet_id = str(packet.get("packet_id", packet_path.stem))
    title = str(packet.get("title", packet_id))
    status = str(packet.get("status", "unknown"))
    authority_tier = str(packet.get("authority_tier", "repo_native"))
    source = packet.get("source", {}) if isinstance(packet.get("source", {}), dict) else {}
    source_type = str(source.get("type", "other"))
    source_ref = str(source.get("ref", ""))
    source_date = str(source.get("date", ""))

    research = packet.get("research", {}) if isinstance(packet.get("research", {}), dict) else {}
    topic = str(research.get("topic", packet.get("raw_text", "")))
    questions = as_list(research.get("questions", []))
    coverage = str(research.get("coverage", "draft"))
    workflow = research.get("workflow", {}) if isinstance(research.get("workflow", {}), dict) else {}
    workflow_mode = str(workflow.get("mode", "standard"))
    creative_provider = str(workflow.get("creative_provider", ""))
    verification_provider = str(workflow.get("verification_provider", ""))
    coding_provider = str(workflow.get("coding_provider", ""))
    creative_complete = bool(workflow.get("creative_complete", False))
    verification_complete = bool(workflow.get("verification_complete", False))
    segments = research.get("segments", []) if isinstance(research.get("segments", []), list) else []

    distilled_claim = str(packet.get("distilled_claim", "")).strip()

    sources = normalize_sources(packet)
    sources_md, source_keys = format_sources_md(sources)

    repo_mapping = packet.get("repo_mapping", {}) if isinstance(packet.get("repo_mapping", {}), dict) else {}
    owner_files = as_list(repo_mapping.get("owner_files", []))
    symbols = as_list(repo_mapping.get("symbols", []))
    target_theorems = as_list(repo_mapping.get("target_theorems", []))

    verification = packet.get("verification_plan", {}) if isinstance(packet.get("verification_plan", {}), dict) else {}
    build_targets = as_list(verification.get("build_targets", []))
    audit_targets = as_list(verification.get("audit_targets", []))

    digest_path = Path(args.out) if args.out else (injections / "digests" / f"{packet_id}.md")
    digest_path.parent.mkdir(parents=True, exist_ok=True)

    questions_md = "\n".join(f"- {q}" for q in questions) if questions else "- (none)"
    owners_md = "\n".join(f"- `{x}`" for x in owner_files) if owner_files else "- (not mapped yet)"
    symbols_md = "\n".join(f"- `{x}`" for x in symbols) if symbols else "- (not mapped yet)"
    theorems_md = "\n".join(f"- `{x}`" for x in target_theorems) if target_theorems else "- (not mapped yet)"
    builds_md = "\n".join(f"- `{x}`" for x in build_targets) if build_targets else "- (not set)"
    audits_md = "\n".join(f"- `{x}`" for x in audit_targets) if audit_targets else "- (not set)"

    deterministic_generated_at = latest_history_time(packet, source_date)

    if source_keys:
        trace_line = f"Current claims are grounded in {', '.join(f'[{k}]' for k in source_keys)}."
    else:
        trace_line = "No source grounding recorded yet."

    segment_lines: list[str] = []
    for i, seg in enumerate(segments):
        if not isinstance(seg, dict):
            continue
        sid = str(seg.get("segment_id", f"S{i+1}"))
        title_seg = str(seg.get("title", "")).strip()
        evs = seg.get("literature_evidence", [])
        ev_count = len(evs) if isinstance(evs, list) else 0
        creative = "yes" if str(seg.get("creative_notes", "")).strip() else "no"
        segment_lines.append(
            f"- `{sid}` {f'({title_seg})' if title_seg else ''}: creative={creative}, evidence={ev_count}"
        )
    segments_md = "\n".join(segment_lines) if segment_lines else "- (no segments)"

    md = f"""# Literature Digest: {title}

## Packet Metadata
- Packet ID: `{packet_id}`
- Lane: `{lane}`
- Status: `{status}`
- Authority tier: `{authority_tier}`
- Coverage: `{coverage}`
- Generated: `{deterministic_generated_at}`

## Provenance
- Source type: `{source_type}`
- Source ref: `{source_ref}`
- Source date: `{source_date}`

## Topic
{topic}

## Workflow
- Mode: `{workflow_mode}`
- Creative provider: `{creative_provider}`
- Verification provider: `{verification_provider}`
- Coding provider: `{coding_provider}`
- Creative complete: `{str(creative_complete).lower()}`
- Verification complete: `{str(verification_complete).lower()}`
- Segment count: `{len(segments)}`

### Segment Coverage
{segments_md}

## Research Questions
{questions_md}

## Distilled Claim
{distilled_claim if distilled_claim else '(not distilled yet)'}

## Source Bibliography
{sources_md}

## Claim-to-Source Traceability
{trace_line}

## Repo Translation Targets
### Owner Files
{owners_md}

### Symbols
{symbols_md}

### Target Theorems
{theorems_md}

## Verification Surface
### Build Targets
{builds_md}

### Audit Targets
{audits_md}

## Reviewer Briefing Notes
- Confirm source quality and recency.
- Mark inferred statements explicitly before promotion to `translated`.
- Block canonical edits until owner/symbol mapping is concrete.
- External-analogy packets must not be promoted to `gated/accepted` by automation.
"""

    digest_path.write_text(md, encoding="utf-8")

    if args.update_packet:
        lock_owner = f"injection_digest:{packet_id}"
        with acquire_packet_lock(packet_id, lock_owner, block=True) as lock:
            # Re-read under lock before mutation.
            locked_packet = json.loads(packet_path.read_text(encoding="utf-8"))
            validate_packet_schema(locked_packet)
            append_history_event(
                locked_packet,
                event="digest:built",
                note=str(digest_path.relative_to(root)),
                idempotent=True,
            )
            validate_packet_schema(locked_packet)
            write_json_atomic(packet_path, locked_packet)
            write_run_manifest(
                root,
                packet=locked_packet,
                stage="digest:build",
                command_argv=list(sys.argv),
                result={"ok": True, "digest": str(digest_path.relative_to(root))},
                extra={"lock_wait_sec": lock.wait_seconds},
            )

    print(digest_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
