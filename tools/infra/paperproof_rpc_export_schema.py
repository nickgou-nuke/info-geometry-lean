#!/usr/bin/env python3
"""Normalize Paperproof RPC/webview proof trees into local trace packets.

Paperproof's Lean side returns a proof tree shaped like:

  [
    {
      "tacticString": "...",
      "goalBefore": {"type": "...", "hyps": [...]},
      "goalsAfter": [...],
      "spawnedGoals": [...],
      "position": {"start": ..., "stop": ...}
    }
  ]

The webview/export layer may wrap this array in objects such as
`{"proofTree": [...]}` or `{"steps": [...]}`.  This bridge accepts those
variants and emits the same `info_geometry.paperproof_trace.v1` schema used by
our Jixia-derived Paperproof-style packets.
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
_SRC = ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from igf.common.hashing import stable_hash
from igf.common.json_io import write_jsonl


SCHEMA = "info_geometry.paperproof_trace.v1"


def load_docs(path: Path) -> list[Any]:
    if path.suffix == ".jsonl":
        docs: list[Any] = []
        with path.open("r", encoding="utf-8") as handle:
            for raw in handle:
                line = raw.strip()
                if line:
                    docs.append(json.loads(line))
        return docs
    return [json.loads(path.read_text(encoding="utf-8"))]


def proof_tree_from_doc(doc: Any) -> list[dict[str, Any]]:
    if isinstance(doc, list):
        return [row for row in doc if isinstance(row, dict)]
    if not isinstance(doc, dict):
        return []
    for key in ("proofTree", "proof_tree", "tree", "steps", "value", "result"):
        value = doc.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, dict)]
        if isinstance(value, dict):
            nested = proof_tree_from_doc(value)
            if nested:
                return nested
    return []


def hyp_to_packet(hyp: Any, idx: int) -> dict[str, Any]:
    if not isinstance(hyp, dict):
        return {"name": f"h{idx}", "type": str(hyp), "raw": hyp}
    return {
        "name": str(hyp.get("username") or hyp.get("name") or hyp.get("id") or f"h{idx}"),
        "type": str(hyp.get("type") or ""),
        "value": hyp.get("value"),
        "is_proof": hyp.get("isProof") if "isProof" in hyp else hyp.get("is_proof"),
        "id": hyp.get("id"),
        "raw": hyp,
    }


def goal_to_packet(goal: Any) -> dict[str, Any]:
    if not isinstance(goal, dict):
        return {"pp": str(goal), "raw": goal}
    hyps = goal.get("hyps") if isinstance(goal.get("hyps"), list) else goal.get("hypotheses")
    if not isinstance(hyps, list):
        hyps = []
    goal_type = str(goal.get("type") or goal.get("pp") or "")
    return {
        "pp": goal_type,
        "username": goal.get("username"),
        "id": goal.get("id"),
        "hyps": [hyp_to_packet(hyp, idx) for idx, hyp in enumerate(hyps)],
        "raw": goal,
    }


def hypotheses_from_goal(goal: Any) -> list[dict[str, Any]]:
    if not isinstance(goal, dict):
        return []
    hyps = goal.get("hyps") if isinstance(goal.get("hyps"), list) else goal.get("hypotheses")
    if not isinstance(hyps, list):
        return []
    return [hyp_to_packet(hyp, idx) for idx, hyp in enumerate(hyps)]


def range_from_position(value: Any) -> Any:
    if not isinstance(value, dict):
        return value
    if "start" in value or "stop" in value:
        return {"start": value.get("start"), "stop": value.get("stop")}
    return value


def step_to_packet(row: dict[str, Any], idx: int) -> dict[str, Any]:
    tactic = str(row.get("tacticString") or row.get("tactic") or row.get("tactic_syntax") or "").strip()
    goal_before = row.get("goalBefore") if "goalBefore" in row else row.get("goal_before")
    goals_after = row.get("goalsAfter") if isinstance(row.get("goalsAfter"), list) else row.get("goals_after")
    spawned = row.get("spawnedGoals") if isinstance(row.get("spawnedGoals"), list) else row.get("spawned_goals")
    if not isinstance(goals_after, list):
        goals_after = []
    if isinstance(spawned, list):
        goals_after = goals_after + spawned
    before_goals = [goal_to_packet(goal_before)] if goal_before is not None else []
    after_goals = [goal_to_packet(goal) for goal in goals_after]
    return {
        "index": idx,
        "source": "paperproof_rpc",
        "tactic": tactic,
        "range": range_from_position(row.get("position") or row.get("range")),
        "references": row.get("tacticDependsOn") if isinstance(row.get("tacticDependsOn"), list) else row.get("references", []),
        "hypotheses_before": hypotheses_from_goal(goal_before),
        "goals_before": before_goals,
        "hypotheses_after": [],
        "goals_after": after_goals,
        "solved": len(after_goals) == 0,
        "theorems": row.get("theorems") if isinstance(row.get("theorems"), list) else [],
    }


def packet_from_doc(doc: Any, *, source_file: str = "", theorem: str = "", packet_index: int = 0) -> dict[str, Any]:
    tree = proof_tree_from_doc(doc)
    if isinstance(doc, dict):
        source_file = source_file or str(doc.get("source_file") or doc.get("leanFile") or doc.get("file") or "")
        theorem = theorem or str(doc.get("theorem") or doc.get("declaration") or doc.get("name") or "")
    steps = [step_to_packet(row, idx) for idx, row in enumerate(tree)]
    packet_id = theorem or source_file or stable_hash(packet_index, tree)
    return {
        "schema": SCHEMA,
        "id": packet_id,
        "source": "paperproof_rpc",
        "theorem": theorem,
        "source_file": source_file,
        "step_count": len(steps),
        "steps": steps,
        "authority": {
            "paperproof_rpc_export": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--out-jsonl", type=Path, required=True)
    parser.add_argument("--source-file", default="")
    parser.add_argument("--theorem", default="")
    args = parser.parse_args()

    packets = [
        packet_from_doc(doc, source_file=args.source_file, theorem=args.theorem, packet_index=idx)
        for idx, doc in enumerate(load_docs(args.input))
    ]
    count = write_jsonl(args.out_jsonl, packets)
    print(json.dumps({"schema": SCHEMA + ".rpc_summary", "packets": count, "out": str(args.out_jsonl)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
