#!/usr/bin/env python3
"""Local AriaScorer-lite semantic grounding report.

AriaScorer uses Jixia + Mathlib metadata + an LLM judge.  This local variant is
deliberately weaker and dependency-free: it extracts Lean-looking identifiers
from candidate code, grounds them against `leansearch_local` records, and emits
coverage/risk signals for Hive review.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.leansearch_local import DEFAULT_RECORDS, iter_jsonl, search_records, tokenize


SCHEMA = "info_geometry.aria_scorer_lite.v1"
LEAN_KEYWORD_BLOCKLIST = {
    "by",
    "def",
    "class",
    "theorem",
    "lemma",
    "structure",
    "where",
    "import",
    "namespace",
    "variable",
    "variables",
    "example",
    "sorry",
    "Prop",
    "Type",
}


def load_record_names(path: Path) -> set[str]:
    return {str(row.get("name")) for row in iter_jsonl(path) if row.get("name")}


def extract_lean_identifiers(code: str) -> list[str]:
    candidates = re.findall(r"\b[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\b", code)
    out: list[str] = []
    seen: set[str] = set()
    for cand in candidates:
        if cand in LEAN_KEYWORD_BLOCKLIST:
            continue
        if cand.startswith("_"):
            continue
        if cand not in seen:
            seen.add(cand)
            out.append(cand)
    return out


def grounded_terms(*, agent_output: str, records: Path, top_k: int) -> tuple[list[dict[str, Any]], list[str]]:
    names = load_record_names(records)
    grounded: list[dict[str, Any]] = []
    ungrounded: list[str] = []
    for ident in extract_lean_identifiers(agent_output):
        if ident in names:
            grounded.append({"term": ident, "grounding": ident, "method": "exact_record_name", "score": None})
            continue
        result = search_records(records_path=records, query=ident, top_k=top_k)
        hits = result.get("hits") or []
        if hits:
            hit = hits[0]
            grounded.append(
                {
                    "term": ident,
                    "grounding": hit.get("name"),
                    "method": "leansearch_local",
                    "score": hit.get("score"),
                    "kind": hit.get("kind"),
                    "type": hit.get("type"),
                }
            )
        else:
            ungrounded.append(ident)
    return grounded, ungrounded


def score_alignment(*, informal_statement: str, agent_output: str, records: Path, top_k: int = 3) -> dict[str, Any]:
    grounded, ungrounded = grounded_terms(agent_output=agent_output, records=records, top_k=top_k)
    informal_tokens = set(tokenize(informal_statement))
    output_tokens = set(tokenize(agent_output))
    overlap = sorted(informal_tokens & output_tokens)
    coverage = len(grounded) / max(len(grounded) + len(ungrounded), 1)
    if coverage >= 0.8 and overlap:
        status = "match"
    elif coverage >= 0.5:
        status = "partial"
    elif grounded:
        status = "weak"
    else:
        status = "unknown"
    risks = []
    if ungrounded:
        risks.append("ungrounded_lean_identifiers")
    if not overlap:
        risks.append("low_informal_formal_token_overlap")
    return {
        "schema": SCHEMA,
        "informal_statement": informal_statement,
        "agent_output": agent_output,
        "records": str(records),
        "semantic_status": status,
        "grounding_coverage": coverage,
        "grounded_terms": grounded,
        "ungrounded_terms": ungrounded,
        "token_overlap": overlap,
        "risks": risks,
        "authority": {
            "semantic_score_is_audit_signal": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--informal-statement", required=True)
    parser.add_argument("--agent-output", required=True)
    parser.add_argument("--records", type=Path, default=DEFAULT_RECORDS)
    parser.add_argument("--top-k", type=int, default=3)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    payload = score_alignment(
        informal_statement=args.informal_statement,
        agent_output=args.agent_output,
        records=args.records,
        top_k=args.top_k,
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"out": str(args.out), "semantic_status": payload["semantic_status"], "grounding_coverage": payload["grounding_coverage"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
