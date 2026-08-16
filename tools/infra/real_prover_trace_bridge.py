#!/usr/bin/env python3
"""Normalize REAL-Prover traces into info-geometry training telemetry.

REAL-Prover is a retrieval-augmented stepwise prover.  Its result payloads carry
proof-search nodes, generator calls, success flags, and sometimes a final
`formal_proof`.  This bridge is intentionally dependency-free: it does not run
REAL-Prover, vLLM, FAISS, Jixia, or Lean.  It only converts saved REAL-Prover
JSON/JSONL logs into a stable JSONL sidecar that Hive and dataset builders can
consume later.
"""

from __future__ import annotations

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


SCHEMA = "info_geometry.real_prover_trace.v1"
SUMMARY_SCHEMA = "info_geometry.real_prover_trace.summary.v1"


def iter_json_records(path: Path) -> Iterable[tuple[dict[str, Any], Path, int | None]]:
    if path.is_dir():
        for child in sorted(path.rglob("*")):
            if child.suffix.lower() in {".json", ".jsonl"}:
                yield from iter_json_records(child)
        return

    if path.suffix.lower() == ".jsonl":
        with path.open("r", encoding="utf-8") as handle:
            for lineno, line in enumerate(handle, start=1):
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                if isinstance(row, dict):
                    yield row, path, lineno
        return

    if path.suffix.lower() == ".json":
        payload = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(payload, list):
            for idx, row in enumerate(payload):
                if isinstance(row, dict):
                    yield row, path, idx
        elif isinstance(payload, dict):
            yield payload, path, None


def normalize_state(state: Any) -> list[str]:
    if state is None:
        return []
    if isinstance(state, str):
        return [state]
    if isinstance(state, list):
        out: list[str] = []
        for item in state:
            if isinstance(item, str):
                out.append(item)
            elif isinstance(item, dict):
                pretty = item.get("pretty") or item.get("type") or item.get("goal")
                if pretty is not None:
                    out.append(str(pretty))
                else:
                    out.append(json.dumps(item, ensure_ascii=True, sort_keys=True))
            else:
                out.append(str(item))
        return out
    return [str(state)]


def normalize_node(node: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": node.get("id") if node.get("id") is not None else node.get("sid"),
        "parent": node.get("parent") if node.get("parent") is not None else node.get("parent_sid"),
        "depth": node.get("depth", 0),
        "tactic": str(node.get("tactic") or ""),
        "state": normalize_state(node.get("state")),
    }


def normalize_call(call: Any) -> dict[str, Any]:
    """Normalize REAL generator call variants.

    Common REAL shapes:
    * [state_str, tactics, logprobs, prompt]
    * [state, prompt, [responses, logprobs]]
    """
    if isinstance(call, dict):
        state = call.get("state") or call.get("stateBefore") or call.get("goal_before")
        tactics = call.get("tactics") or call.get("responses") or []
        logprobs = call.get("logprobs") or call.get("scores") or []
        prompt = call.get("prompt")
    elif isinstance(call, list | tuple):
        state = call[0] if len(call) >= 1 else None
        prompt = None
        tactics = []
        logprobs = []
        if len(call) >= 4:
            tactics = call[1] if isinstance(call[1], list) else []
            logprobs = call[2] if isinstance(call[2], list) else []
            prompt = call[3]
        elif len(call) >= 3 and isinstance(call[2], list | tuple) and len(call[2]) >= 1:
            prompt = call[1]
            tactics = call[2][0] if isinstance(call[2][0], list) else []
            if len(call[2]) >= 2 and isinstance(call[2][1], list):
                logprobs = call[2][1]
    else:
        state = None
        tactics = []
        logprobs = []
        prompt = None

    normalized_tactics = []
    for idx, tactic in enumerate(tactics):
        normalized_tactics.append(
            {
                "tactic": str(tactic),
                "score": logprobs[idx] if idx < len(logprobs) else None,
            }
        )
    return {
        "state": "\n".join(normalize_state(state)),
        "prompt": prompt,
        "tactics": normalized_tactics,
    }


def normalize_collect_result(result: dict[str, Any]) -> dict[str, Any]:
    nodes = [normalize_node(node) for node in result.get("nodes", []) if isinstance(node, dict)]
    calls = [normalize_call(call) for call in result.get("calls", [])]
    return {
        "declaration": result.get("declaration"),
        "success": bool(result.get("success", False)),
        "nodes": nodes,
        "calls": calls,
        "stop_cause": result.get("stop_cause") or {},
        "node_count": len(nodes),
        "call_count": len(calls),
        "tactic_candidate_count": sum(len(call["tactics"]) for call in calls),
    }


def normalize_real_record(raw: dict[str, Any], source_file: Path, source_line: int | None) -> dict[str, Any]:
    formal_statement = raw.get("formal_statement") or raw.get("formalStatement") or raw.get("statement")
    collect_results = raw.get("collect_results") or raw.get("collectResults") or []
    if isinstance(collect_results, dict):
        collect_results = [collect_results]
    normalized_results = [
        normalize_collect_result(result)
        for result in collect_results
        if isinstance(result, dict)
    ]
    payload = {
        "schema": SCHEMA,
        "id": "",
        "source": "real_prover",
        "formal_statement": formal_statement,
        "formal_proof": raw.get("formal_proof") or raw.get("formalProof"),
        "success": any(result["success"] for result in normalized_results),
        "collect_results": normalized_results,
        "raw_ref": {
            "source_file": str(source_file),
            "source_line": source_line,
        },
        "authority": {
            "trace_is_training_telemetry": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }
    payload["id"] = stable_hash(
        {
            "formal_statement": formal_statement,
            "source_file": str(source_file),
            "source_line": source_line,
            "collect_results": [
                {
                    "declaration": result["declaration"],
                    "success": result["success"],
                    "node_count": result["node_count"],
                    "call_count": result["call_count"],
                }
                for result in normalized_results
            ],
        }
    )
    return payload


def run_bridge(input_path: Path, output_dir: Path) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    out_path = output_dir / "real_prover_trace_bridge.jsonl"
    rows = []
    for raw, source_file, source_line in iter_json_records(input_path):
        rows.append(normalize_real_record(raw, source_file, source_line))

    with out_path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")

    summary = {
        "schema": SUMMARY_SCHEMA,
        "input": str(input_path),
        "output": str(out_path),
        "records": len(rows),
        "successful_records": sum(1 for row in rows if row["success"]),
        "collect_results": sum(len(row["collect_results"]) for row in rows),
        "search_nodes": sum(
            result["node_count"]
            for row in rows
            for result in row["collect_results"]
        ),
        "generator_calls": sum(
            result["call_count"]
            for row in rows
            for result in row["collect_results"]
        ),
        "tactic_candidates": sum(
            result["tactic_candidate_count"]
            for row in rows
            for result in row["collect_results"]
        ),
    }
    summary_path = output_dir / "real_prover_trace_bridge_summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="REAL-Prover JSON/JSONL file or directory")
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    summary = run_bridge(args.input, args.output_dir)
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
