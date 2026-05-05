#!/usr/bin/env python3
"""Phase A bridge: normalize LeanDojo-v2 traces into IG-compatible sidecars.

This bridge is intentionally read-only.  It does not mutate Hive queues,
Arango collections, Lean files, or promotion state.  Its job is to turn
LeanDojo-v2-style theorem/tactic trace exports into a permissive canonical
JSONL format and, optionally, compare declaration coverage against existing
InfoGeometry DAG/InfoTree declaration artifacts.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Iterable

BRIDGE_VERSION = "0.1.0"
DEFAULT_OUTPUT_DIR = Path("artifacts/leandojo_v2")


THEOREM_NAME_KEYS = (
    "full_name",
    "theoremFullName",
    "declaration",
    "declName",
    "name",
)

THEOREM_STATEMENT_KEYS = (
    "theorem_statement",
    "theoremStatement",
    "statement",
    "type",
    "pretty_type",
)

LEAN_FILE_KEYS = (
    "file_path",
    "leanFile",
    "file",
    "path",
)

TACTIC_KEYS = (
    "traced_tactics",
    "tactics",
    "proof_steps",
    "steps",
)


def _pos(v: Any) -> dict[str, int] | None:
    if not isinstance(v, list) or len(v) != 2:
        return None
    if not all(isinstance(x, int) for x in v):
        return None
    return {"line": v[0], "column": v[1]}


def _first(record: dict[str, Any], keys: Iterable[str]) -> Any:
    for key in keys:
        value = record.get(key)
        if value is not None:
            return value
    return None


def _tactics(record: dict[str, Any]) -> list[Any]:
    value = _first(record, TACTIC_KEYS)
    return value if isinstance(value, list) else []


def _state_before(tactic: dict[str, Any]) -> Any:
    return _first(tactic, ("state_before", "stateBefore", "proof_state_before", "goal_before", "before"))


def _state_after(tactic: dict[str, Any]) -> Any:
    return _first(tactic, ("state_after", "stateAfter", "proof_state_after", "goal_after", "after"))


def _tactic_text(tactic: dict[str, Any]) -> Any:
    return _first(tactic, ("tactic", "tactic_text", "code", "text"))


def convert_theorem_record(record: dict[str, Any], *, source_file: str, line_no: int) -> dict[str, Any]:
    tactics = _tactics(record)

    first_state = None
    last_state = None
    if tactics:
        first = tactics[0] if isinstance(tactics[0], dict) else {}
        last = tactics[-1] if isinstance(tactics[-1], dict) else {}
        first_state = _state_before(first)
        last_state = _state_after(last)

    theorem_name = _first(record, THEOREM_NAME_KEYS)
    theorem_statement = _first(record, THEOREM_STATEMENT_KEYS)
    lean_file = _first(record, LEAN_FILE_KEYS)
    dependencies = record.get("dependencies")
    if not isinstance(dependencies, list):
        dependencies = record.get("deps")
    if not isinstance(dependencies, list):
        dependencies = []

    return {
        "bridgeVersion": BRIDGE_VERSION,
        "source": "leandojo_v2",
        "sourceFile": source_file,
        "sourceLine": line_no,
        "repoUrl": record.get("url"),
        "commit": record.get("commit"),
        "leanFile": lean_file,
        "theoremFullName": theorem_name,
        "declaration": theorem_name,
        "theoremStatement": theorem_statement,
        "positions": {
            "start": _pos(record.get("start")),
            "end": _pos(record.get("end")),
        },
        "dependencies": [str(dep) for dep in dependencies if isinstance(dep, str)],
        "proofStepCount": len(tactics),
        "firstGoalState": first_state,
        "lastGoalState": last_state,
        "tactics": [
            {
                "tactic": _tactic_text(t) if isinstance(t, dict) else None,
                "stateBefore": _state_before(t) if isinstance(t, dict) else None,
                "stateAfter": _state_after(t) if isinstance(t, dict) else None,
            }
            for t in tactics
        ],
        "raw": record,
    }


def _iter_rows_from_payload(payload: Any):
    if isinstance(payload, list):
        for row in payload:
            if isinstance(row, dict):
                yield row
    elif isinstance(payload, dict):
        for key in ("theorems", "declarations", "records", "rows", "data"):
            rows = payload.get(key)
            if isinstance(rows, list):
                for row in rows:
                    if isinstance(row, dict):
                        yield row
                return
        yield payload


def _iter_rows(path: Path):
    if path.suffix == ".jsonl":
        with path.open("r", encoding="utf-8") as f:
            for idx, line in enumerate(f, start=1):
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                if isinstance(row, dict):
                    yield row, idx
        return

    payload = json.loads(path.read_text(encoding="utf-8"))
    for idx, row in enumerate(_iter_rows_from_payload(payload), start=1):
        yield row, idx


def _input_files(input_dir: Path) -> list[Path]:
    files = [
        path
        for path in input_dir.rglob("*")
        if path.is_file() and path.suffix in {".json", ".jsonl"}
    ]
    return sorted(files)


def _decl_name_from_row(row: dict[str, Any]) -> str | None:
    value = _first(row, ("name", "declName", "declaration", "theoremFullName", "full_name"))
    return str(value) if isinstance(value, str) and value else None


def _decl_names_from_payload(payload: Any) -> set[str]:
    out: set[str] = set()
    if isinstance(payload, list):
        for item in payload:
            if isinstance(item, str):
                out.add(item)
            elif isinstance(item, dict):
                name = _decl_name_from_row(item)
                if name:
                    out.add(name)
        return out

    if not isinstance(payload, dict):
        return out

    for key in ("decl_names", "declarations", "theorems", "records", "rows", "data"):
        value = payload.get(key)
        if isinstance(value, list):
            out |= _decl_names_from_payload(value)

    name = _decl_name_from_row(payload)
    if name:
        out.add(name)

    components = payload.get("components")
    if isinstance(components, list):
        for component in components:
            if not isinstance(component, dict):
                continue
            rep = component.get("representative")
            if isinstance(rep, str) and rep:
                out.add(rep)
            for member in component.get("members") or []:
                if isinstance(member, str) and member:
                    out.add(member)

    return out


def load_decl_names(path: Path) -> set[str]:
    if path.suffix == ".jsonl":
        names: set[str] = set()
        with path.open("r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                if isinstance(row, dict):
                    name = _decl_name_from_row(row)
                    if name:
                        names.add(name)
                elif isinstance(row, str):
                    names.add(row)
        return names
    return _decl_names_from_payload(json.loads(path.read_text(encoding="utf-8")))


def coverage_report(*, leandojo_names: set[str], compare_names: set[str], compare_paths: list[Path]) -> dict[str, Any]:
    shared = sorted(leandojo_names & compare_names)
    only_leandojo = sorted(leandojo_names - compare_names)
    only_compare = sorted(compare_names - leandojo_names)
    denominator = len(leandojo_names | compare_names)
    return {
        "schema": "info_geometry.leandojo_v2_bridge.coverage_report.v1",
        "bridgeVersion": BRIDGE_VERSION,
        "comparePaths": [str(path) for path in compare_paths],
        "leandojoDeclarationCount": len(leandojo_names),
        "compareDeclarationCount": len(compare_names),
        "sharedDeclarationCount": len(shared),
        "onlyLeanDojoCount": len(only_leandojo),
        "onlyCompareCount": len(only_compare),
        "jaccardCoverage": (len(shared) / denominator) if denominator else 1.0,
        "sharedSample": shared[:50],
        "onlyLeanDojoSample": only_leandojo[:50],
        "onlyCompareSample": only_compare[:50],
    }


def run_bridge(*, input_dir: Path, output_dir: Path, compare_decl_paths: list[Path] | None = None) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    out_path = output_dir / "leandojo_v2_bridge.jsonl"
    compare_decl_paths = compare_decl_paths or []

    count = 0
    files = 0
    proof_state_rows = 0
    tactic_rows = 0
    theorem_names: set[str] = set()
    with out_path.open("w", encoding="utf-8") as out:
        for file_path in _input_files(input_dir):
            files += 1
            for row, line_no in _iter_rows(file_path):
                bridged = convert_theorem_record(
                    row,
                    source_file=str(file_path.relative_to(input_dir)),
                    line_no=line_no,
                )
                out.write(json.dumps(bridged, ensure_ascii=True) + "\n")
                count += 1
                if bridged["theoremFullName"]:
                    theorem_names.add(str(bridged["theoremFullName"]))
                if bridged["proofStepCount"]:
                    tactic_rows += 1
                if bridged["firstGoalState"] is not None or bridged["lastGoalState"] is not None:
                    proof_state_rows += 1

    compare_names: set[str] = set()
    for path in compare_decl_paths:
        compare_names |= load_decl_names(path)

    report = None
    report_path = output_dir / "leandojo_v2_coverage_report.json"
    if compare_decl_paths:
        report = coverage_report(
            leandojo_names=theorem_names,
            compare_names=compare_names,
            compare_paths=compare_decl_paths,
        )
        report_path.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")

    summary = {
        "bridgeVersion": BRIDGE_VERSION,
        "schema": "info_geometry.leandojo_v2_bridge.summary.v1",
        "inputDir": str(input_dir),
        "outputFile": str(out_path),
        "coverageReport": str(report_path) if report is not None else None,
        "files": files,
        "rows": count,
        "declarations": len(theorem_names),
        "rowsWithTactics": tactic_rows,
        "rowsWithProofStates": proof_state_rows,
        "compareDeclarationFiles": [str(path) for path in compare_decl_paths],
    }
    (output_dir / "leandojo_v2_bridge_summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=True) + "\n", encoding="utf-8"
    )
    return summary


def _main() -> int:
    parser = argparse.ArgumentParser(description="Convert LeanDojo-v2 theorem JSON exports to bridge JSONL")
    parser.add_argument("--input-dir", required=True, help="Directory containing LeanDojo JSON/JSONL files")
    parser.add_argument(
        "--output-dir",
        default=str(DEFAULT_OUTPUT_DIR),
        help="Directory for bridge outputs (default: artifacts/leandojo_v2)",
    )
    parser.add_argument(
        "--compare-decls",
        type=Path,
        action="append",
        default=[],
        help="Optional DAG/InfoTree declaration artifact to compare against; accepts JSON or JSONL",
    )
    args = parser.parse_args()

    summary = run_bridge(
        input_dir=Path(args.input_dir),
        output_dir=Path(args.output_dir),
        compare_decl_paths=list(args.compare_decls),
    )
    print(json.dumps(summary, indent=2, ensure_ascii=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
