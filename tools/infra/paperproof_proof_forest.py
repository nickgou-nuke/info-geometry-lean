#!/usr/bin/env python3
"""Build proof-forest graphs from Paperproof-style trace packets.

Paperproof's key modeling insight is that goal evolution is naturally a tree,
while hypothesis evolution is better understood as a collection of smaller
history trees.  This script turns our canonical
`info_geometry.paperproof_trace.v1` packets into explicit graph artifacts:

  goal nodes
  tactic nodes
  hypothesis nodes
  transformed_by / produces_goal / available_hypothesis / depends_on edges

The output is for visualization, retrieval, and training.  It is not proof
authority; Lean remains the verifier.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.paperproof_forest.v1"


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


def normalize(text: Any) -> str:
    return re.sub(r"\s+", " ", str(text or "")).strip()


def tactic_family(tactic: str) -> str:
    parts = tactic.strip().split()
    return parts[0] if parts else ""


def goal_text(goal: Any) -> str:
    if isinstance(goal, dict):
        return normalize(goal.get("pp") or goal.get("type") or goal.get("raw") or "")
    return normalize(goal)


def goal_raw_id(goal: Any) -> str:
    if isinstance(goal, dict):
        raw = goal.get("raw")
        if isinstance(raw, dict):
            return normalize(raw.get("id") or raw.get("mvar_id") or raw.get("mvarId") or "")
        return normalize(goal.get("id") or goal.get("mvar_id") or goal.get("mvarId") or "")
    return ""


def hyp_name(hyp: Any, idx: int) -> str:
    if isinstance(hyp, dict):
        return normalize(hyp.get("name") or hyp.get("username") or hyp.get("id") or f"h{idx}")
    return f"h{idx}"


def hyp_type(hyp: Any) -> str:
    if isinstance(hyp, dict):
        return normalize(hyp.get("type") or hyp.get("pp") or "")
    return normalize(hyp)


def hyp_raw_id(hyp: Any) -> str:
    if isinstance(hyp, dict):
        raw = hyp.get("raw")
        if isinstance(raw, dict):
            return normalize(raw.get("id") or raw.get("fvarId") or raw.get("fvar_id") or "")
        return normalize(hyp.get("id") or hyp.get("fvarId") or hyp.get("fvar_id") or "")
    return ""


def add_node(nodes: dict[str, dict[str, Any]], node: dict[str, Any]) -> str:
    nodes.setdefault(str(node["id"]), node)
    return str(node["id"])


def add_edge(edges: list[dict[str, Any]], src: str, dst: str, role: str, **extra: Any) -> None:
    edges.append({"from": src, "to": dst, "role": role, **extra})


def goal_node_id(packet_id: str, step_index: int, side: str, idx: int, goal: Any) -> str:
    raw_id = goal_raw_id(goal)
    if raw_id:
        return f"goal:{stable_hash(packet_id, raw_id)}"
    return f"goal:{stable_hash(packet_id, step_index, side, idx, goal_text(goal))}"


def hyp_node_id(packet_id: str, step_index: int, side: str, idx: int, hyp: Any) -> str:
    raw_id = hyp_raw_id(hyp)
    if raw_id:
        return f"hyp:{stable_hash(packet_id, raw_id)}"
    return f"hyp:{stable_hash(packet_id, step_index, side, idx, hyp_name(hyp, idx), hyp_type(hyp))}"


def build_forest(packet: dict[str, Any]) -> dict[str, Any]:
    packet_id = str(packet.get("id") or packet.get("theorem") or packet.get("source_file") or stable_hash(packet))
    nodes: dict[str, dict[str, Any]] = {}
    edges: list[dict[str, Any]] = []

    root_id = add_node(
        nodes,
        {
            "id": f"proof:{stable_hash(packet_id)}",
            "kind": "proof",
            "theorem": packet.get("theorem"),
            "source_file": packet.get("source_file"),
            "source": packet.get("source"),
        },
    )

    for step in packet.get("steps") or []:
        if not isinstance(step, dict):
            continue
        step_index = int(step.get("index") or 0)
        tactic = normalize(step.get("tactic"))
        tactic_id = add_node(
            nodes,
            {
                "id": f"tactic:{stable_hash(packet_id, step_index, tactic, step.get('range'))}",
                "kind": "tactic",
                "step_index": step_index,
                "text": tactic,
                "family": tactic_family(tactic),
                "range": step.get("range"),
                "references": step.get("references") if isinstance(step.get("references"), list) else [],
            },
        )
        add_edge(edges, root_id, tactic_id, "contains_tactic", step_index=step_index)

        before_goal_ids: list[str] = []
        for idx, goal in enumerate(step.get("goals_before") or []):
            gid = add_node(
                nodes,
                {
                    "id": goal_node_id(packet_id, step_index, "before", idx, goal),
                    "kind": "goal",
                    "side": "before",
                    "step_index": step_index,
                    "text": goal_text(goal),
                    "raw_id": goal_raw_id(goal),
                    "raw": goal,
                },
            )
            before_goal_ids.append(gid)
            add_edge(edges, gid, tactic_id, "transformed_by", step_index=step_index)

        after_goals = step.get("goals_after") or []
        for idx, goal in enumerate(after_goals):
            gid = add_node(
                nodes,
                {
                    "id": goal_node_id(packet_id, step_index, "after", idx, goal),
                    "kind": "goal",
                    "side": "after",
                    "step_index": step_index,
                    "text": goal_text(goal),
                    "raw_id": goal_raw_id(goal),
                    "raw": goal,
                },
            )
            add_edge(edges, tactic_id, gid, "produces_goal", step_index=step_index)
            for before_id in before_goal_ids:
                add_edge(edges, before_id, gid, "goal_child", via=tactic_id, step_index=step_index)

        if not after_goals:
            closed_id = add_node(
                nodes,
                {
                    "id": f"closed:{stable_hash(packet_id, step_index, tactic)}",
                    "kind": "closed_goal",
                    "step_index": step_index,
                    "text": "no goals",
                },
            )
            add_edge(edges, tactic_id, closed_id, "closes_goal", step_index=step_index)

        for side_key, side in (("hypotheses_before", "before"), ("hypotheses_after", "after")):
            for idx, hyp in enumerate(step.get(side_key) or []):
                hid = add_node(
                    nodes,
                    {
                        "id": hyp_node_id(packet_id, step_index, side, idx, hyp),
                        "kind": "hypothesis",
                        "side": side,
                        "step_index": step_index,
                        "name": hyp_name(hyp, idx),
                        "type": hyp_type(hyp),
                        "raw_id": hyp_raw_id(hyp),
                        "raw": hyp,
                    },
                )
                add_edge(edges, hid, tactic_id, "available_hypothesis", side=side, step_index=step_index)

        for ref in step.get("references") or []:
            ref_text = normalize(ref)
            if not ref_text:
                continue
            ref_id = f"ref:{stable_hash(packet_id, ref_text)}"
            add_node(nodes, {"id": ref_id, "kind": "reference", "text": ref_text})
            add_edge(edges, tactic_id, ref_id, "depends_on", step_index=step_index)

    return {
        "schema": SCHEMA,
        "id": f"forest:{stable_hash(packet_id)}",
        "packet_id": packet_id,
        "theorem": packet.get("theorem"),
        "source_file": packet.get("source_file"),
        "source": packet.get("source"),
        "nodes": list(nodes.values()),
        "edges": edges,
        "summary": {
            "nodes": len(nodes),
            "edges": len(edges),
            "goals": sum(1 for node in nodes.values() if node.get("kind") == "goal"),
            "hypotheses": sum(1 for node in nodes.values() if node.get("kind") == "hypothesis"),
            "tactics": sum(1 for node in nodes.values() if node.get("kind") == "tactic"),
        },
        "authority": {
            "proof_forest_visualization": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paperproof-trace", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    forests = [build_forest(packet) for packet in iter_jsonl(args.paperproof_trace)]
    count = write_jsonl(args.out, forests)
    totals = {
        "forests": count,
        "nodes": sum(row["summary"]["nodes"] for row in forests),
        "edges": sum(row["summary"]["edges"] for row in forests),
        "goals": sum(row["summary"]["goals"] for row in forests),
        "hypotheses": sum(row["summary"]["hypotheses"] for row in forests),
        "tactics": sum(row["summary"]["tactics"] for row in forests),
    }
    print(json.dumps({"schema": SCHEMA + ".summary", "out": str(args.out), **totals}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
