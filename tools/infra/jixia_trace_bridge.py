#!/usr/bin/env python3
"""Normalize Jixia analyzer outputs into info-geometry JSONL sidecars.

Jixia emits separate JSON files for declarations, symbols, elaboration trees,
and line-level proof states.  This bridge is intentionally tolerant and
dependency-free: it does not run Jixia or Lean; it normalizes already-produced
Jixia JSON into local artifacts for DAG/InfoTree comparison and training.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable


SCHEMA_DECL = "info_geometry.jixia.declaration.v1"
SCHEMA_SYMBOL = "info_geometry.jixia.symbol.v1"
SCHEMA_TACTIC = "info_geometry.jixia.tactic_transition.v1"
SCHEMA_LINE = "info_geometry.jixia.line_state.v1"
SCHEMA_SUMMARY = "info_geometry.jixia.bridge.summary.v1"


def stable_hash(payload: Any) -> str:
    text = json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    return hashlib.sha1(text.encode("utf-8")).hexdigest()


def load_json_array(path: Path | None) -> list[Any]:
    if path is None or not path.exists():
        return []
    payload = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(payload, list):
        return payload
    if isinstance(payload, dict):
        return [payload]
    return []


def name_to_string(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, list):
        return ".".join(str(part) for part in value)
    return str(value or "")


def range_to_object(value: Any) -> dict[str, Any] | None:
    if isinstance(value, list) and len(value) == 2:
        return {"start": value[0], "stop": value[1]}
    if isinstance(value, dict):
        return value
    return None


def normalize_ppsyntax(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        return {"original": None, "range": None, "pp": None}
    return {
        "original": value.get("original"),
        "range": range_to_object(value.get("range")),
        "pp": value.get("pp?") if "pp?" in value else value.get("pp"),
    }


def normalize_goal(goal: Any) -> dict[str, Any]:
    if not isinstance(goal, dict):
        return {"pp": str(goal), "type": "", "context": []}
    return {
        "tag": name_to_string(goal.get("tag")),
        "mvar_id": name_to_string(goal.get("mvarId") or goal.get("mvar_id")),
        "type": str(goal.get("type") or ""),
        "is_prop": goal.get("isProp") if "isProp" in goal else goal.get("is_prop"),
        "pp": str(goal.get("pp") or goal.get("type") or ""),
        "context": goal.get("context") if isinstance(goal.get("context"), list) else [],
        "extra": goal.get("extra?") if "extra?" in goal else goal.get("extra"),
    }


def normalize_declaration(row: dict[str, Any], source_file: Path, idx: int) -> dict[str, Any]:
    name = name_to_string(row.get("name"))
    payload = {
        "schema": SCHEMA_DECL,
        "id": "",
        "source": "jixia",
        "source_file": str(source_file),
        "name": name,
        "kind": str(row.get("kind") or ""),
        "range": normalize_ppsyntax(row.get("ref")).get("range"),
        "signature": normalize_ppsyntax(row.get("signature")),
        "type": normalize_ppsyntax(row.get("type")),
        "value": normalize_ppsyntax(row.get("value")),
        "parameters": row.get("params") if isinstance(row.get("params"), list) else [],
        "authority": {
            "jixia_static_analysis": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }
    payload["id"] = stable_hash(["decl", str(source_file), idx, name, payload["kind"]])
    return payload


def normalize_symbol(row: dict[str, Any], source_file: Path, idx: int) -> dict[str, Any]:
    name = name_to_string(row.get("name"))
    type_refs = [name_to_string(x) for x in row.get("typeReferences") or row.get("type_references") or []]
    value_refs_raw = row.get("valueReferences") if "valueReferences" in row else row.get("value_references")
    value_refs = None if value_refs_raw is None else [name_to_string(x) for x in value_refs_raw]
    payload = {
        "schema": SCHEMA_SYMBOL,
        "id": "",
        "source": "jixia",
        "source_file": str(source_file),
        "name": name,
        "kind": row.get("kind"),
        "type_full": row.get("typeFull"),
        "type_readable": row.get("typeReadable"),
        "type_fallback": row.get("typeFallback"),
        "type_references": sorted(set(type_refs)),
        "value_references": None if value_refs is None else sorted(set(value_refs)),
        "is_prop": row.get("isProp"),
        "authority": {
            "jixia_static_analysis": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }
    payload["id"] = stable_hash(["symbol", str(source_file), idx, name])
    return payload


def iter_tactic_infos(tree: Any) -> Iterable[dict[str, Any]]:
    if not isinstance(tree, dict):
        return
    info = tree.get("info")
    if isinstance(info, dict) and "tactic" in info and isinstance(info["tactic"], dict):
        yield {
            "info": info["tactic"],
            "ref": tree.get("ref"),
        }
    for child in tree.get("children") or []:
        yield from iter_tactic_infos(child)


def normalize_tactic(row: dict[str, Any], source_file: Path, idx: int) -> dict[str, Any]:
    info = row["info"]
    before = [normalize_goal(goal) for goal in info.get("before") or []]
    after = [normalize_goal(goal) for goal in info.get("after") or []]
    references = [name_to_string(x) for x in info.get("references") or []]
    ref = normalize_ppsyntax(row.get("ref"))
    payload = {
        "schema": SCHEMA_TACTIC,
        "id": "",
        "source": "jixia",
        "source_file": str(source_file),
        "range": ref.get("range"),
        "tactic_syntax": ref.get("pp"),
        "references": sorted(set(references)),
        "before": before,
        "after": after,
        "extra": info.get("extra?") if "extra?" in info else info.get("extra"),
        "authority": {
            "jixia_infotree_extraction": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }
    payload["id"] = stable_hash(["tactic", str(source_file), idx, payload["range"], payload["tactic_syntax"]])
    return payload


def normalize_line(row: dict[str, Any], source_file: Path, idx: int) -> dict[str, Any]:
    payload = {
        "schema": SCHEMA_LINE,
        "id": "",
        "source": "jixia",
        "source_file": str(source_file),
        "start": row.get("start"),
        "state": [normalize_goal(goal) for goal in row.get("state") or []],
        "authority": {
            "jixia_line_state": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }
    payload["id"] = stable_hash(["line", str(source_file), idx, payload["start"]])
    return payload


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
            count += 1
    return count


def run_bridge(
    *,
    declaration_json: Path | None,
    symbol_json: Path | None,
    elaboration_json: Path | None,
    line_json: Path | None,
    output_dir: Path,
) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    declaration_rows = [
        normalize_declaration(row, declaration_json or Path(""), idx)
        for idx, row in enumerate(load_json_array(declaration_json))
        if isinstance(row, dict)
    ]
    symbol_rows = [
        normalize_symbol(row, symbol_json or Path(""), idx)
        for idx, row in enumerate(load_json_array(symbol_json))
        if isinstance(row, dict)
    ]
    tactic_rows = [
        normalize_tactic(row, elaboration_json or Path(""), idx)
        for idx, row in enumerate(
            tactic
            for tree in load_json_array(elaboration_json)
            for tactic in iter_tactic_infos(tree)
        )
    ]
    line_rows = [
        normalize_line(row, line_json or Path(""), idx)
        for idx, row in enumerate(load_json_array(line_json))
        if isinstance(row, dict)
    ]

    counts = {
        "declarations": write_jsonl(output_dir / "jixia_declarations.jsonl", declaration_rows),
        "symbols": write_jsonl(output_dir / "jixia_symbols.jsonl", symbol_rows),
        "tactic_transitions": write_jsonl(output_dir / "jixia_tactic_transitions.jsonl", tactic_rows),
        "line_states": write_jsonl(output_dir / "jixia_line_states.jsonl", line_rows),
    }
    summary = {
        "schema": SCHEMA_SUMMARY,
        "inputs": {
            "declaration_json": str(declaration_json) if declaration_json else None,
            "symbol_json": str(symbol_json) if symbol_json else None,
            "elaboration_json": str(elaboration_json) if elaboration_json else None,
            "line_json": str(line_json) if line_json else None,
        },
        "output_dir": str(output_dir),
        "rows": counts,
    }
    (output_dir / "jixia_trace_bridge_summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--declaration-json", type=Path)
    parser.add_argument("--symbol-json", type=Path)
    parser.add_argument("--elaboration-json", type=Path)
    parser.add_argument("--line-json", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    summary = run_bridge(
        declaration_json=args.declaration_json,
        symbol_json=args.symbol_json,
        elaboration_json=args.elaboration_json,
        line_json=args.line_json,
        output_dir=args.output_dir,
    )
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
