#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

DECL_RE = re.compile(r"^\s*(?:@[^\n]*\s*)?(theorem|lemma|example)\b")

SOCKET_TOKENS = (
    "packet",
    "socket",
    "witness",
    "certificate",
    "nonempty",
    "context",
)


def _read_lines(path: Path) -> list[str]:
    return path.read_text(encoding="utf-8").splitlines()


def _decl_name(line: str, fallback: str) -> str:
    chunks = line.strip().split()
    if not chunks:
        return fallback
    if chunks[0] in {"theorem", "lemma", "example"} and len(chunks) > 1:
        raw = chunks[1]
        return raw.split("(")[0].split(":")[0].split("{")[0]
    return fallback


def _collect_theorem_blocks(lines: list[str]) -> list[dict]:
    out: list[dict] = []
    i = 0
    while i < len(lines):
        if not DECL_RE.match(lines[i]):
            i += 1
            continue
        start = i
        j = i + 1
        while j < len(lines):
            if DECL_RE.match(lines[j]) and (len(lines[j]) - len(lines[j].lstrip(" "))) <= (len(lines[start]) - len(lines[start].lstrip(" "))):
                break
            if lines[j].strip().startswith("end "):
                break
            j += 1
        block = lines[start:j]
        joined = "\n".join(block)
        if ":= by" in joined or any(ln.strip() == "by" for ln in block):
            out.append({
                "name": _decl_name(lines[start], f"example_at_{start+1}"),
                "start": start + 1,
                "end": j,
                "text": joined,
            })
        i = max(j, i + 1)
    return out


def _classify(block: dict, imports: list[str]) -> tuple[str, list[str]]:
    text = (block["text"] or "").lower()
    name = str(block["name"]).lower()
    signals: list[str] = []

    has_mathlib_root = any(line.strip().startswith("import Mathlib") for line in imports)
    if has_mathlib_root:
        signals.append("mathlib:import")

    socket_hits = [tok for tok in SOCKET_TOKENS if tok in text or tok in name]
    if socket_hits:
        signals.append("socket:" + ",".join(socket_hits[:4]))

    if has_mathlib_root and socket_hits:
        return "mixed_root_and_socket", signals
    if has_mathlib_root:
        return "mathlib_rooted_proof_chain", signals
    if socket_hits:
        return "interface_socket", signals
    return "unclassified_local_proof", signals


def build_queue(file_path: Path, target_limit: int) -> dict:
    lines = _read_lines(file_path)
    imports = [ln for ln in lines if ln.strip().startswith("import ")]
    blocks = _collect_theorem_blocks(lines)

    details = []
    for blk in blocks[:target_limit]:
        authority_class, authority_signals = _classify(blk, imports)
        details.append(
            {
                "name": blk["name"],
                "startLine": blk["start"],
                "endLine": blk["end"],
                "authorityClass": authority_class,
                "authoritySignals": authority_signals,
            }
        )

    return {
        "schema": "info_geometry.lean_canonical_refactor_queue.v1",
        "file": str(file_path),
        "targetLimit": int(target_limit),
        "targetDetails": details,
        "closureRules": [
            "preserve theorem statements and declaration names",
            "distinguish mathlib/repo-rooted proof chains from interface/socket wrappers",
            "optimize only after authority class review and targeted Lean gate",
        ],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Build a conservative Lean canonical refactor queue")
    ap.add_argument("--file", required=True, type=Path)
    ap.add_argument("--json-out", required=True, type=Path)
    ap.add_argument("--target-limit", type=int, default=20)
    args = ap.parse_args()

    payload = build_queue(args.file, args.target_limit)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
