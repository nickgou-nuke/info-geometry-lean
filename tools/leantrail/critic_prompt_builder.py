#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

SYSTEM_INSTRUCTION = """You are a LeanTrail critic agent. Your job is to review structured evidence and produce bounded audit findings. You are not allowed to modify source code, invent proof terms, hide proof debt, or certify theorem truth. Explicit sorry is permitted as honest proof debt; disguised closure through axioms, opaque placeholders, certificate fields, or witness fields is not permitted. Return only JSON matching the requested schema."""

OUTPUT_SCHEMA = {
    "type": "object",
    "required": ["packet_id", "verdict", "confidence", "rationale", "recommended_next_actions"],
    "properties": {
        "packet_id": {"type": "string"},
        "verdict": {
            "type": "string",
            "enum": [
                "confirm_issue",
                "likely_issue",
                "false_positive",
                "needs_human_review",
                "needs_kernel_obligation",
            ],
        },
        "confidence": {"type": "number", "minimum": 0, "maximum": 1},
        "rationale": {"type": "string"},
        "recommended_next_actions": {"type": "array", "items": {"type": "string"}},
        "protect_from_surgery": {"type": "boolean"},
        "bridge_candidate": {"type": "boolean"},
        "proof_hole_priority": {"type": "string", "enum": ["none", "low", "medium", "high"]},
    },
    "additionalProperties": False,
}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            raw = line.strip()
            if not raw:
                continue
            try:
                obj = json.loads(raw)
            except Exception:
                continue
            if isinstance(obj, dict):
                yield obj


def build_prompt(packet: dict[str, Any]) -> dict[str, Any]:
    packet_id = str(packet.get("packet_id", ""))
    user_payload = {
        "task": "Review this LeanTrail critic packet and return a bounded audit verdict.",
        "safety_rules": [
            "Do not propose direct source patches.",
            "Do not certify theorem truth; Lean kernel is authority.",
            "Treat explicit sorry as honest proof debt, not obfuscation.",
            "Treat hidden axioms, opaque proof stand-ins, certificate/witness placeholders, and placeholder proofs as unsafe closure.",
            "If structural alignment is plausible, request a kernel obligation rather than approving a rewrite.",
        ],
        "packet": packet,
        "required_output_schema": OUTPUT_SCHEMA,
    }
    return {
        "prompt_id": f"prompt_{packet_id}",
        "created_at": utc_now(),
        "packet_id": packet_id,
        "target": packet.get("target"),
        "critic_kind": packet.get("critic_kind"),
        "system": SYSTEM_INSTRUCTION,
        "user": user_payload,
        "source_modification_allowed": False,
    }


def render_md(prompts: list[dict[str, Any]], out_jsonl: Path, top_n: int) -> str:
    lines = [
        "# LeanTrail Critic Prompt Report",
        "",
        f"- generated_at: `{utc_now()}`",
        f"- output_jsonl: `{out_jsonl}`",
        f"- prompt_count: `{len(prompts)}`",
        "",
        "## Top Prompts",
        "",
        "| rank | packet | kind | target |",
        "|---:|---|---|---|",
    ]
    for i, p in enumerate(prompts[: max(0, top_n)], start=1):
        lines.append(
            f"| {i} | `{p.get('packet_id','')}` | `{p.get('critic_kind','')}` | `{p.get('target','')}` |"
        )
    return "\n".join(lines) + "\n"


def run(*, packets_path: Path, out_path: Path, md_out: Path | None, limit: int | None, top_n: int) -> dict[str, Any]:
    packets = list(iter_jsonl(packets_path))
    if limit is not None:
        packets = packets[: max(0, int(limit))]
    prompts = [build_prompt(p) for p in packets]

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        for p in prompts:
            handle.write(json.dumps(p, ensure_ascii=True, sort_keys=True) + "\n")

    if md_out is not None:
        md_out.parent.mkdir(parents=True, exist_ok=True)
        md_out.write_text(render_md(prompts, out_path, top_n), encoding="utf-8")

    report = {
        "created_at": utc_now(),
        "packets": str(packets_path),
        "output_jsonl": str(out_path),
        "output_md": str(md_out) if md_out else None,
        "prompt_count": len(prompts),
        "source_modification_allowed": False,
    }
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build bounded prompt packets from LeanTrail critic packets.")
    parser.add_argument("--packets", default="artifacts/leantrail/critic_packets.jsonl")
    parser.add_argument("--out", default="artifacts/leantrail/critic_prompts.jsonl")
    parser.add_argument("--md-out", default="artifacts/leantrail/critic_prompts.md")
    parser.add_argument("--json-out", default="artifacts/leantrail/critic_prompt_report.json")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--top-n", type=int, default=50)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    packets_path = Path(args.packets).resolve()
    if not packets_path.exists():
        raise FileNotFoundError(f"Critic packets not found: {packets_path}")
    report = run(
        packets_path=packets_path,
        out_path=Path(args.out).resolve(),
        md_out=Path(args.md_out).resolve() if str(args.md_out).strip() else None,
        limit=args.limit,
        top_n=max(0, int(args.top_n)),
    )
    json_out = Path(args.json_out).resolve()
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Critic prompts written: {report['output_jsonl']} (prompts={report['prompt_count']})")
    if report.get("output_md"):
        print(f"Critic prompt markdown written: {report['output_md']}")
    print(f"Operation report written: {json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
