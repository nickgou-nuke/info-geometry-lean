#!/usr/bin/env python3
"""Match Blueprint-style nodes to repo declarations and cone seeds.

This is the lightweight bridge between paper-roadmap nodes and the Lean DAG
owner surface.  The first implementation uses local LeanSearch records; live
Arango cone expansion remains a downstream step once an apex declaration is
chosen.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.leansearch_local import DEFAULT_RECORDS, search_records


SCHEMA = "info_geometry.blueprint_arango_match.v1"


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    if not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                yield row


def node_query(node: dict[str, Any]) -> str:
    entities = " ".join(str(e.get("normalized") or e.get("surface") or "") for e in node.get("entities") or [] if isinstance(e, dict))
    candidates = " ".join(str(c.get("name") or "") for c in node.get("candidate_repo_decls") or [] if isinstance(c, dict))
    return " ".join(
        [
            str(node.get("title") or ""),
            str(node.get("suggested_lean_name") or ""),
            entities,
            candidates,
            str(node.get("informal_statement") or "")[:800],
        ]
    )


def match_node(node: dict[str, Any], *, records: Path, top_k: int) -> dict[str, Any]:
    result = search_records(records_path=records, query=node_query(node), top_k=top_k)
    apex_candidates = []
    for hit in result.get("hits") or []:
        if not isinstance(hit, dict):
            continue
        apex_candidates.append(
            {
                "decl": hit.get("name"),
                "kind": hit.get("kind"),
                "module": hit.get("module"),
                "file": hit.get("file"),
                "line": hit.get("line"),
                "score": hit.get("score"),
                "reason": "leansearch_local lexical match over blueprint title/entities/statement",
            }
        )
    return {
        "schema": SCHEMA,
        "blueprint_node_id": node.get("id"),
        "blueprint_title": node.get("title"),
        "blueprint_kind": node.get("kind"),
        "suggested_lean_name": node.get("suggested_lean_name"),
        "apex_candidates": apex_candidates,
        "recommended_apex": apex_candidates[0] if apex_candidates else None,
        "next_step": "run arango_causal_chiral_cone_prompt.py on recommended_apex.decl, then jixiaTrainingData --cone-packet",
        "authority": {
            "matching_only": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
            count += 1
    return count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blueprint-nodes", type=Path, required=True)
    parser.add_argument("--records", type=Path, default=DEFAULT_RECORDS)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--top-k", type=int, default=8)
    args = parser.parse_args()

    rows = [match_node(node, records=args.records, top_k=args.top_k) for node in iter_jsonl(args.blueprint_nodes)]
    count = write_jsonl(args.out, rows)
    print(json.dumps({"schema": SCHEMA + ".summary", "matches": count, "out": str(args.out)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
