#!/usr/bin/env python3
"""ChatGPT External Audit protocol: parse responses under the authority membrane.

External ChatGPT responses are proposal-only and must never claim promotion
authority. This module parses the structured audit response format, validates the
authority membrane, and emits a schema-valid ChatGPTSocraticAuditPacket.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

ROOT = Path(__file__).resolve().parents[2]

_SECTION_RE = re.compile(r"^([A-Z][A-Z0-9_]*)::(.*)$")
_FORBIDDEN_EMITTED = frozenset(
    {"LeanVerificationPacket", "BuildPacket", "AuditPacket", "PromotionDecisionPacket"}
)
_VALID_ROLES = frozenset(
    {"owner", "translator", "coherence", "capstone", "nominal_shell"}
)


class ExternalAuditError(Exception):
    pass


def _sha256(content: str | bytes) -> str:
    if isinstance(content, str):
        content = content.encode("utf-8")
    return "sha256:" + hashlib.sha256(content).hexdigest()


def _parse_sections(text: str) -> dict[str, str]:
    sections: dict[str, str] = {}
    current_key: str | None = None
    current_parts: list[str] = []

    for line in text.splitlines():
        m = _SECTION_RE.match(line)
        if m:
            if current_key is not None:
                sections[current_key] = "\n".join(current_parts)
            current_key = m.group(1)
            rest = (m.group(2) or "").strip()
            current_parts = [rest] if rest else []
        elif current_key is not None:
            current_parts.append(line)

    if current_key is not None:
        sections[current_key] = "\n".join(current_parts)

    return sections


def extract_drop_in_replacement(response_text: str) -> str:
    sections = _parse_sections(response_text)
    raw = sections.get("DROP_IN_REPLACEMENT", "")
    if not raw and "DROP_IN_REPLACEMENT" not in sections:
        raise ExternalAuditError("DROP_IN_REPLACEMENT section not found in response")

    stripped = raw.strip()

    # Fenced code block: ```lean ... ``` or ``` ... ```
    m = re.match(r"^```(?:lean)?\n(.*?)\n```$", stripped, re.DOTALL)
    if m:
        return m.group(1)

    # Plain text: strip leading "lean" line if present
    lines = stripped.split("\n")
    if lines and lines[0].strip().lower() == "lean":
        lines = lines[1:]
    return "\n".join(lines).strip()


def _parse_role(sections: dict[str, str]) -> str:
    role = sections.get("ROLE", "").strip().lower()
    return role if role in _VALID_ROLES else "unknown"


def _parse_promotion_allowed(sections: dict[str, str]) -> bool:
    val = sections.get("PROMOTION_ALLOWED", "no").strip().lower()
    return val == "yes"


def make_packet(
    response_text: str,
    target_file: str,
    target_module: str,
    lineage_ref: str,
    transcript_ref: str | None = None,
    replacement_ref: str | None = None,
) -> dict[str, Any]:
    sections = _parse_sections(response_text)

    if _parse_promotion_allowed(sections):
        raise ExternalAuditError(
            "PROMOTION_ALLOWED::yes is forbidden for external audit responses"
        )

    replacement = extract_drop_in_replacement(response_text)
    role = _parse_role(sections)
    now = datetime.now(timezone.utc).isoformat()

    packet: dict[str, Any] = {
        "id": str(uuid.uuid4()),
        "kind": "ChatGPTSocraticAuditPacket",
        "status": "parsed",
        "lineage_id": lineage_ref,
        "revision": 1,
        "origin_run_id": str(uuid.uuid4()),
        "created_at": now,
        "updated_at": now,
        "authority": "proposal",
        "authority_ceiling": "proposal",
        "promotion_allowed": False,
        "source": {
            "system": "chatgpt_web",
            "authority_negative": True,
        },
        "target_module": target_module,
        "target_file": target_file,
        "lineage_ref": lineage_ref,
        "role_classification": role,
        "response_hash": _sha256(response_text),
        "replacement_hash": _sha256(replacement),
        "patch_proposal": {
            "kind": "drop_in_replacement",
            "target_file": target_file,
            "content_hash": _sha256(replacement),
        },
        "emitted_packet_kinds": [],
        "forbidden_output_kinds": ["LeanVerificationPacket"],
        "requires_local_lean_check": True,
        "local_lean_check": {"status": "not_run"},
        "external_promotion_claim_seen": False,
    }

    if transcript_ref is not None:
        packet["transcript_ref"] = transcript_ref
    if replacement_ref is not None:
        packet["replacement_ref"] = replacement_ref

    return packet


def ensure_proposal_only(packet: dict[str, Any]) -> None:
    if packet.get("promotion_allowed") is not False:
        raise ExternalAuditError(
            "PROMOTION_ALLOWED must be false for external audit proposals"
        )
    for kind in packet.get("emitted_packet_kinds", []):
        if kind in _FORBIDDEN_EMITTED:
            raise ExternalAuditError(
                f"Forbidden authority packet in emitted_packet_kinds: {kind}"
            )


def _cmd_parse(args: argparse.Namespace) -> int:
    response_path = Path(args.response)
    if not response_path.exists():
        print(f"ERROR: response file not found: {response_path}", file=sys.stderr)
        return 2

    response_text = response_path.read_text(encoding="utf-8")
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    try:
        packet = make_packet(
            response_text=response_text,
            target_file=args.target_file,
            target_module=args.target_module,
            lineage_ref=args.lineage_ref,
        )
    except ExternalAuditError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    replacement = extract_drop_in_replacement(response_text)

    packet_path = out_dir / "packet.json"
    replacement_path = out_dir / "replacement.lean"
    packet_path.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    replacement_path.write_text(replacement + "\n", encoding="utf-8")

    print(json.dumps({"packet": str(packet_path.resolve()), "replacement": str(replacement_path.resolve())}))
    return 0


def _build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    sp = p.add_subparsers(dest="cmd", required=True)

    p_parse = sp.add_parser("parse", help="Parse a ChatGPT audit response into a packet.")
    p_parse.add_argument("--response", required=True, help="Path to response text file.")
    p_parse.add_argument("--target-file", required=True, help="Lean file path.")
    p_parse.add_argument("--target-module", required=True, help="Lean module name.")
    p_parse.add_argument("--lineage-ref", required=True, help="Lineage reference string.")
    p_parse.add_argument("--out-dir", required=True, help="Output directory.")

    return p


def main() -> int:
    args = _build_arg_parser().parse_args()
    if args.cmd == "parse":
        return _cmd_parse(args)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
