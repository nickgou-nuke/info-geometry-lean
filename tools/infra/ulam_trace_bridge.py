#!/usr/bin/env python3
"""Normalize UlamAI run.jsonl traces into info-geometry tactic telemetry.

UlamAI traces contain proof-state/tactic transitions produced by a search and
repair loop.  This bridge preserves those transitions as training telemetry only;
it does not treat UlamAI success flags as repository proof authority.
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

SCHEMA = "info_geometry.ulam_trace.v1"
SUMMARY_SCHEMA = "info_geometry.ulam_trace.summary.v1"
DEFAULT_OUTPUT_DIR = Path("artifacts/ulam")


def as_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value.strip()
    return json.dumps(value, ensure_ascii=True, sort_keys=True)


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
            rows = payload
        elif isinstance(payload, dict):
            for key in ("steps", "trace", "records", "rows", "data"):
                value = payload.get(key)
                if isinstance(value, list):
                    rows = value
                    break
            else:
                rows = [payload]
        else:
            rows = []
        for idx, row in enumerate(rows, start=1):
            if isinstance(row, dict):
                yield row, path, idx


def normalize_record(raw: dict[str, Any], source_file: Path, source_line: int | None) -> dict[str, Any]:
    theorem = as_text(raw.get("theorem") or raw.get("declaration") or raw.get("declName"))
    tactic = as_text(raw.get("tactic") or raw.get("action") or raw.get("command"))
    goal_before = as_text(raw.get("state_pretty") or raw.get("statePretty") or raw.get("goal_before") or raw.get("before"))
    goal_after = as_text(raw.get("new_state_pretty") or raw.get("newStatePretty") or raw.get("goal_after") or raw.get("after"))
    ok = bool(raw.get("ok", raw.get("success", False)))
    solved = bool(raw.get("solved", raw.get("is_solved", raw.get("isSolved", False))))
    error = as_text(raw.get("error") or raw.get("diagnostic"))
    payload = {
        "schema": SCHEMA,
        "id": "",
        "source": "ulamai",
        "theorem": theorem,
        "lean_file": as_text(raw.get("file_path") or raw.get("leanFile") or raw.get("file")),
        "state_key": as_text(raw.get("state_key") or raw.get("stateKey")),
        "state_hash": as_text(raw.get("state_hash") or raw.get("stateHash")),
        "goal_before": goal_before,
        "tactic": tactic,
        "ok": ok,
        "solved": solved,
        "goal_after": goal_after,
        "new_state_key": as_text(raw.get("new_state_key") or raw.get("newStateKey")),
        "new_state_hash": as_text(raw.get("new_state_hash") or raw.get("newStateHash")),
        "error": error,
        "error_kind": as_text(raw.get("error_kind") or raw.get("errorKind")),
        "cached": bool(raw.get("cached", False)),
        "elapsed_ms": raw.get("elapsed_ms") if isinstance(raw.get("elapsed_ms"), int) else raw.get("elapsedMs"),
        "raw_ref": {
            "source_file": str(source_file),
            "source_line": source_line,
        },
        "authority": {
            "trace_is_training_telemetry": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
            "lean_checked_claim_requires_replay": True,
        },
        "raw": raw,
    }
    payload["id"] = stable_hash(
        {
            "source": "ulamai",
            "source_file": str(source_file),
            "source_line": source_line,
            "state_key": payload["state_key"],
            "goal_before": goal_before,
            "tactic": tactic,
            "ok": ok,
            "solved": solved,
            "error": error,
        }
    )
    return payload


def run_bridge(input_path: Path, output_dir: Path) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    out_path = output_dir / "ulam_trace_bridge.jsonl"
    rows = [normalize_record(raw, source_file, source_line) for raw, source_file, source_line in iter_json_records(input_path)]
    with out_path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
    summary = {
        "schema": SUMMARY_SCHEMA,
        "input": str(input_path),
        "output": str(out_path),
        "records": len(rows),
        "successful_steps": sum(1 for row in rows if row["ok"]),
        "failed_steps": sum(1 for row in rows if not row["ok"]),
        "solved_steps": sum(1 for row in rows if row["solved"]),
        "cached_steps": sum(1 for row in rows if row["cached"]),
    }
    summary_path = output_dir / "ulam_trace_bridge_summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="UlamAI run JSON/JSONL file or directory")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    args = parser.parse_args()
    summary = run_bridge(args.input, args.output_dir)
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
