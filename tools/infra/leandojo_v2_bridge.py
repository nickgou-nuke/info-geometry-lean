#!/usr/bin/env python3
"""Phase A bridge: convert LeanDojo-v2 theorem JSON exports into IG-compatible JSONL sidecar."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

BRIDGE_VERSION = "0.1.0"


def _pos(v: Any) -> dict[str, int] | None:
    if not isinstance(v, list) or len(v) != 2:
        return None
    if not all(isinstance(x, int) for x in v):
        return None
    return {"line": v[0], "column": v[1]}


def convert_theorem_record(record: dict[str, Any], *, source_file: str, line_no: int) -> dict[str, Any]:
    tactics = record.get("traced_tactics")
    if not isinstance(tactics, list):
        tactics = []

    first_state = None
    last_state = None
    if tactics:
        first = tactics[0] if isinstance(tactics[0], dict) else {}
        last = tactics[-1] if isinstance(tactics[-1], dict) else {}
        first_state = first.get("state_before")
        last_state = last.get("state_after")

    return {
        "bridgeVersion": BRIDGE_VERSION,
        "source": "leandojo_v2",
        "sourceFile": source_file,
        "sourceLine": line_no,
        "repoUrl": record.get("url"),
        "commit": record.get("commit"),
        "leanFile": record.get("file_path"),
        "theoremFullName": record.get("full_name"),
        "theoremStatement": record.get("theorem_statement"),
        "positions": {
            "start": _pos(record.get("start")),
            "end": _pos(record.get("end")),
        },
        "proofStepCount": len(tactics),
        "firstGoalState": first_state,
        "lastGoalState": last_state,
        "tactics": [
            {
                "tactic": t.get("tactic") if isinstance(t, dict) else None,
                "stateBefore": t.get("state_before") if isinstance(t, dict) else None,
                "stateAfter": t.get("state_after") if isinstance(t, dict) else None,
            }
            for t in tactics
        ],
    }


def _iter_rows(path: Path):
    payload = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(payload, list):
        for idx, row in enumerate(payload, start=1):
            if isinstance(row, dict):
                yield row, idx


def run_bridge(*, input_dir: Path, output_dir: Path) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    out_path = output_dir / "leandojo_v2_bridge.jsonl"

    count = 0
    files = 0
    with out_path.open("w", encoding="utf-8") as out:
        for file_path in sorted(input_dir.glob("*.json")):
            files += 1
            for row, line_no in _iter_rows(file_path):
                bridged = convert_theorem_record(row, source_file=file_path.name, line_no=line_no)
                out.write(json.dumps(bridged, ensure_ascii=True) + "\n")
                count += 1

    summary = {
        "bridgeVersion": BRIDGE_VERSION,
        "inputDir": str(input_dir),
        "outputFile": str(out_path),
        "files": files,
        "rows": count,
    }
    (output_dir / "leandojo_v2_bridge_summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=True) + "\n", encoding="utf-8"
    )
    return summary


def _main() -> int:
    parser = argparse.ArgumentParser(description="Convert LeanDojo-v2 theorem JSON exports to bridge JSONL")
    parser.add_argument("--input-dir", required=True, help="Directory containing LeanDojo JSON files (*.json)")
    parser.add_argument("--output-dir", required=True, help="Directory for bridge outputs")
    args = parser.parse_args()

    summary = run_bridge(input_dir=Path(args.input_dir), output_dir=Path(args.output_dir))
    print(json.dumps(summary, indent=2, ensure_ascii=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
