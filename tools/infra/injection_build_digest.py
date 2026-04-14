#!/usr/bin/env python3
"""Build a cited literature digest markdown from an injection packet."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

LANES = ("raw", "distilled", "translated", "gated", "accepted", "rejected", "archive")


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def resolve_packet(injections: Path, ref: str) -> Path:
    p = Path(ref)
    if p.exists():
        return p
    for lane in LANES:
        cand = injections / lane / f"{ref}.json"
        if cand.exists():
            return cand
    raise FileNotFoundError(f"packet not found for ref={ref}")


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


def main() -> int:
    parser = argparse.ArgumentParser(description="Build a markdown digest from an injection packet")
    parser.add_argument("packet", help="Packet id or packet path")
    parser.add_argument("--out", default=None, help="Output markdown path (default: handover/injections/digests/<id>.md)")
    parser.add_argument("--update-packet", action="store_true", help="Append digest event to packet history")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    injections = repo_root / "handover" / "injections"

    packet_path = resolve_packet(injections, args.packet)
    lane = packet_path.parent.name
    packet = json.loads(packet_path.read_text(encoding="utf-8"))

    packet_id = str(packet.get("packet_id", packet_path.stem))
    title = str(packet.get("title", packet_id))
    status = str(packet.get("status", "unknown"))
    source = packet.get("source", {}) if isinstance(packet.get("source", {}), dict) else {}
    source_type = str(source.get("type", "other"))
    source_ref = str(source.get("ref", ""))
    source_date = str(source.get("date", ""))

    research = packet.get("research", {}) if isinstance(packet.get("research", {}), dict) else {}
    topic = str(research.get("topic", packet.get("raw_text", "")))
    questions = as_list(research.get("questions", []))
    coverage = str(research.get("coverage", "draft"))

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

    if source_keys:
        trace_line = f"Current claims are grounded in {', '.join(f'[{k}]' for k in source_keys)}."
    else:
        trace_line = "No source grounding recorded yet."

    md = f"""# Literature Digest: {title}

## Packet Metadata
- Packet ID: `{packet_id}`
- Lane: `{lane}`
- Status: `{status}`
- Coverage: `{coverage}`
- Generated: `{utc_now()}`

## Provenance
- Source type: `{source_type}`
- Source ref: `{source_ref}`
- Source date: `{source_date}`

## Topic
{topic}

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
"""

    digest_path.write_text(md, encoding="utf-8")

    if args.update_packet:
        hist = packet.setdefault("history", [])
        hist.append(
            {
                "at": utc_now(),
                "event": "digest:built",
                "note": str(digest_path.relative_to(repo_root)),
            }
        )
        packet_path.write_text(json.dumps(packet, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")

    print(digest_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
