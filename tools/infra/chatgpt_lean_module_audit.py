#!/usr/bin/env python3
"""ChatGPT Lean Module Audit: generate and process Socratic audit prompts.

Drives the ChatGPT Socratic Audit Protocol for a single Lean module. Generates
a structured audit prompt with authority membrane constraints, then (optionally)
imports an offline ChatGPT response and emits a ChatGPTSocraticAuditPacket.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.infra.chatgpt_external_audit import (
    ExternalAuditError,
    extract_drop_in_replacement,
    make_packet,
)

ROOT = Path(__file__).resolve().parents[2]


def infer_module_name(path: Path) -> str:
    parts = path.with_suffix("").parts
    if parts and parts[0] == "lean":
        parts = parts[1:]
    return ".".join(parts)


def build_prompt(
    module_name: str,
    target_file: str,
    lineage_ref: str,
    lean_source: str,
    context: str,
) -> str:
    return f"""\
You are a Lean 4 / Mathlib translator operating under the ChatGPT Socratic Audit Protocol.

AUTHORITY CEILING: proposal
PROMOTION_ALLOWED must be no

Your task is to analyze the following Lean 4 module and produce a DROP_IN_REPLACEMENT
proposal. The proposal must not claim promotion authority.

TARGET_MODULE: {module_name}
TARGET_FILE: {target_file}
LINEAGE_REF: {lineage_ref}

=== BEGIN_TARGET_LEAN_MODULE ===
{lean_source}
=== END_TARGET_LEAN_MODULE ===

=== BEGIN_ADDITIONAL_CONTEXT ===
{context}
=== END_ADDITIONAL_CONTEXT ===

Respond using the following structured format:

ROLE::<owner|translator|coherence|capstone|nominal_shell>

SUMMARY::
<Brief description of the module's role.>

MATHLIB_ROOTING::
- <Note relevant Mathlib 4 dependencies and owners.>

THEOREM_STRENGTH::
- <Classify each theorem: bridge / derived / closure / transport / invariance.>

OWNER_SHADOW_DRIFT::
- <Note any drift from the module's owner.>

ASSUMPTION_PACKAGING::
- <Describe assumption packaging and typeclass usage.>

MINIMAL_REFACTOR_PLAN::
1. <List minimal steps required.>

DROP_IN_REPLACEMENT::
```lean
<Full replacement Lean 4 source.>
```

RISKS::
- <Any risks that require local review.>

LOCAL_VERIFICATION_REQUIRED::
- lake env lean <file>

PROMOTION_ALLOWED::no
"""


def _read_lean_source(file_arg: str) -> str:
    p = Path(file_arg)
    if p.exists():
        return p.read_text(encoding="utf-8")
    # Try relative to ROOT
    alt = ROOT / file_arg
    if alt.exists():
        return alt.read_text(encoding="utf-8")
    return ""


def _cmd_run(args: argparse.Namespace) -> int:
    file_path = Path(args.file)
    module_name = infer_module_name(file_path)
    lineage_ref = getattr(args, "lineage_ref", "") or ""
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    lean_source = _read_lean_source(args.file)

    response_path: Path | None = Path(args.response) if getattr(args, "response", None) else None

    if response_path is None:
        # Prompt-only mode
        prompt = build_prompt(
            module_name=module_name,
            target_file=args.file,
            lineage_ref=lineage_ref,
            lean_source=lean_source,
            context="",
        )
        prompt_path = out_dir / "prompt.txt"
        prompt_path.write_text(prompt, encoding="utf-8")
        print(json.dumps({"prompt": str(prompt_path.resolve()), "target_module": module_name}))
        return 0

    # Response import mode
    if not response_path.exists():
        print(f"ERROR: response file not found: {response_path}", file=sys.stderr)
        return 2

    response_text = response_path.read_text(encoding="utf-8")
    no_lean_check: bool = getattr(args, "no_lean_check", False)

    try:
        packet = make_packet(
            response_text=response_text,
            target_file=args.file,
            target_module=module_name,
            lineage_ref=lineage_ref or "unset",
        )
    except ExternalAuditError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    if no_lean_check:
        packet["local_lean_check"] = {"status": "not_run"}

    replacement = extract_drop_in_replacement(response_text)

    packet_path = out_dir / "packet.json"
    replacement_path = out_dir / "replacement.lean"
    packet_path.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    replacement_path.write_text(replacement + "\n", encoding="utf-8")

    print(json.dumps({
        "packet": str(packet_path.resolve()),
        "replacement": str(replacement_path.resolve()),
        "target_module": module_name,
    }))
    return 0


def _build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--file", required=True, help="Path to target Lean file.")
    p.add_argument("--out-dir", required=True, help="Output directory.")
    p.add_argument("--lineage-ref", default="", help="Lineage reference string.")
    p.add_argument("--response", default=None, help="Path to ChatGPT response file.")
    p.add_argument("--no-lean-check", action="store_true", help="Skip local Lean check.")
    return p


def main() -> int:
    args = _build_arg_parser().parse_args()
    return _cmd_run(args)


if __name__ == "__main__":
    raise SystemExit(main())
