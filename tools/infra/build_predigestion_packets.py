#!/usr/bin/env python3
"""Build non-authoritative predigestion claim packets from source chunks.

Predigestion packets are semantic proposal artifacts. They may guide retrieval,
Hive tasks, and later formalization attempts, but they are not Lean proofs and
must not be promoted without the normal Lean/build/audit gates.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.predigested_claim.v1"
SUMMARY_SCHEMA = "info_geometry.predigestion_summary.v1"

SOURCE_KINDS = {"paper", "blackbook", "old_doc", "doc"}
RISKS = {"source_text", "metaphor", "informal", "formalizable", "already_supported", "unsupported"}
AUTHORITIES = {
    "source_text",
    "semantic",
    "proposal",
    "execution_intent",
    "lean_checked",
    "build_checked",
    "audit_checked",
    "promoted",
}

AUTHORITY_BOUNDARY = {
    "semantic_artifact_can_propose": True,
    "not_a_proof": True,
    "lean_remains_proof_authority": True,
}


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


def require_enum(value: str, allowed: set[str], name: str) -> str:
    if value not in allowed:
        raise SystemExit(f"invalid {name}: {value!r}; expected one of {sorted(allowed)}")
    return value


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def first_string(row: dict[str, Any], keys: tuple[str, ...], default: str = "") -> str:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value:
            return value
    return default


def list_of_strings(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value] if value else []
    if isinstance(value, list):
        return [str(item) for item in value if item is not None and str(item)]
    return []


def default_claim(text: str) -> str:
    clean = re.sub(r"\s+", " ", text or "").strip()
    if not clean:
        return ""
    pieces = re.split(r"(?<=[.!?])\s+", clean)
    return pieces[0][:1000]


def infer_risk(row: dict[str, Any], source_kind: str, explicit_risk: str | None) -> str:
    if explicit_risk:
        return require_enum(explicit_risk, RISKS, "risk")
    value = row.get("risk")
    if isinstance(value, str) and value:
        return require_enum(value, RISKS, "risk")
    if source_kind == "blackbook":
        return "metaphor"
    if source_kind in {"paper", "old_doc", "doc"}:
        return "informal"
    return "source_text"


def make_packet(row: dict[str, Any], *, source_kind: str, risk_override: str | None = None) -> dict[str, Any]:
    source_kind = require_enum(source_kind, SOURCE_KINDS, "source_kind")
    risk = infer_risk(row, source_kind, risk_override)
    authority = require_enum(str(row.get("authority") or "semantic"), AUTHORITIES, "authority")
    if authority not in {"source_text", "semantic", "proposal"}:
        raise SystemExit(f"predigestion packet cannot be emitted with assertive authority: {authority!r}")

    source_id = first_string(row, ("id", "chunk_id", "key", "_key"), "")
    text = first_string(row, ("text", "content", "chunk", "body"), "")
    claim = first_string(row, ("claim", "summary", "statement"), default_claim(text))
    lang = first_string(row, ("lang", "language"), "unknown")

    packet = {
        "schema": SCHEMA,
        "id": "",
        "source_kind": source_kind,
        "source_ref": {
            "id": source_id,
            "source": first_string(row, ("source", "path", "document"), ""),
            "title": first_string(row, ("title", "paper_title", "document_title"), ""),
            "citation": first_string(row, ("citation", "bibtex", "ref"), ""),
        },
        "text": {
            "original": text,
            "lang": lang,
        },
        "claim": claim,
        "definitions": list_of_strings(row.get("definitions")),
        "symbols": list_of_strings(row.get("symbols")),
        "hidden_assumptions": list_of_strings(row.get("hidden_assumptions") or row.get("assumptions")),
        "repo_owner_candidates": list_of_strings(row.get("repo_owner_candidates") or row.get("owners")),
        "lean_target_candidates": list_of_strings(row.get("lean_target_candidates") or row.get("lean_targets")),
        "risk": risk,
        "authority": authority,
        "provenance": {
            "builder": "build_predigestion_packets.py",
            "method": "chunk_to_claim_v1",
        },
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }
    packet["id"] = stable_hash(
        {
            "schema": SCHEMA,
            "source_kind": source_kind,
            "source_ref": packet["source_ref"],
            "claim": claim,
            "text": text,
            "risk": risk,
            "authority": authority,
        }
    )
    return packet


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def build_packets(input_path: Path, *, source_kind: str, risk: str | None = None) -> list[dict[str, Any]]:
    return [make_packet(row, source_kind=source_kind, risk_override=risk) for row in iter_jsonl(input_path)]


def summary_for(rows: list[dict[str, Any]], *, input_path: Path, out: Path) -> dict[str, Any]:
    by_risk: dict[str, int] = {}
    by_authority: dict[str, int] = {}
    for row in rows:
        by_risk[row["risk"]] = by_risk.get(row["risk"], 0) + 1
        by_authority[row["authority"]] = by_authority.get(row["authority"], 0) + 1
    return {
        "schema": SUMMARY_SCHEMA,
        "input": str(input_path),
        "output": str(out),
        "records": len(rows),
        "by_risk": by_risk,
        "by_authority": by_authority,
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="Source chunk JSONL")
    parser.add_argument("--source-kind", required=True, choices=sorted(SOURCE_KINDS))
    parser.add_argument("--risk", choices=sorted(RISKS), help="Override risk for all emitted packets")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--summary-out", type=Path, required=True)
    args = parser.parse_args()

    rows = build_packets(args.input, source_kind=args.source_kind, risk=args.risk)
    write_jsonl(args.out, rows)
    summary = summary_for(rows, input_path=args.input, out=args.out)
    args.summary_out.parent.mkdir(parents=True, exist_ok=True)
    args.summary_out.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
