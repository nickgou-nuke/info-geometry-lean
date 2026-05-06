#!/usr/bin/env python3
"""Normalize PDA/FormL4-style autoformalization records into IG sidecars.

This bridge is intentionally read-only.  PDA/FormL4 records are useful as
natural-language/formal-statement training and evaluation material, but they are
not proof authority for this repository.  Lean remains the only proof checker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable

SCHEMA = "info_geometry.pda_forml4_bridge.v1"
SUMMARY_SCHEMA = "info_geometry.pda_forml4_bridge.summary.v1"
DEFAULT_OUTPUT_DIR = Path("artifacts/pda_forml4")

THEOREM_KEYS = ("theorem", "name", "declName", "declaration", "full_name", "formal_name")
INFORMAL_KEYS = (
    "informal_statement",
    "informalStatement",
    "informal",
    "nl_statement",
    "natural_language_statement",
    "question",
    "problem",
)
FORMAL_KEYS = (
    "formal_statement",
    "formalStatement",
    "formal",
    "lean_statement",
    "leanStatement",
    "statement",
    "answer",
)
LEAN_CODE_KEYS = ("lean_code", "leanCode", "formalization", "prediction", "output", "completion")
FEEDBACK_KEYS = (
    "compiler_feedback",
    "compilerFeedback",
    "feedback",
    "lean_error",
    "error",
    "diagnostic",
    "process_annotation",
)
LABEL_KEYS = (
    "process_label",
    "processLabel",
    "label",
    "compile_status",
    "compileStatus",
    "status",
    "result",
)
SPLIT_KEYS = ("split", "dataset_split", "subset")


def stable_hash(payload: Any) -> str:
    data = json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(data.encode("utf-8")).hexdigest()


def first(record: dict[str, Any], keys: Iterable[str]) -> Any:
    for key in keys:
        value = record.get(key)
        if value is not None:
            return value
    return None


def as_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value.strip()
    return json.dumps(value, ensure_ascii=True, sort_keys=True)


def process_label(record: dict[str, Any]) -> str:
    raw = as_text(first(record, LABEL_KEYS)).lower()
    feedback = as_text(first(record, FEEDBACK_KEYS)).lower()
    if raw in {"valid", "success", "ok", "passed", "compile_success", "compiled"}:
        return "valid"
    if raw in {"syntax_error", "type_error", "semantic_drift", "missing_import", "unknown"}:
        return raw
    text = raw + "\n" + feedback
    if "syntax" in text or "parser" in text or "unexpected token" in text:
        return "syntax_error"
    if "unknown constant" in text or "unknown identifier" in text or "missing import" in text:
        return "missing_import"
    if "type mismatch" in text or "failed to synthesize" in text or "application type mismatch" in text:
        return "type_error"
    if "semantic" in text or "equivalence" in text or "drift" in text:
        return "semantic_drift"
    return "unknown"


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
        rows: list[Any]
        if isinstance(payload, list):
            rows = payload
        elif isinstance(payload, dict):
            rows = []
            for key in ("data", "records", "rows", "examples", "theorems"):
                value = payload.get(key)
                if isinstance(value, list):
                    rows = value
                    break
            if not rows:
                rows = [payload]
        else:
            rows = []
        for idx, row in enumerate(rows, start=1):
            if isinstance(row, dict):
                yield row, path, idx


def normalize_record(raw: dict[str, Any], source_file: Path, source_line: int | None) -> dict[str, Any]:
    theorem = as_text(first(raw, THEOREM_KEYS))
    informal = as_text(first(raw, INFORMAL_KEYS))
    formal = as_text(first(raw, FORMAL_KEYS))
    lean_code = as_text(first(raw, LEAN_CODE_KEYS))
    feedback = as_text(first(raw, FEEDBACK_KEYS))
    split = as_text(first(raw, SPLIT_KEYS)) or _split_from_path(source_file)
    label = process_label(raw)
    payload = {
        "schema": SCHEMA,
        "id": "",
        "source": "pda_forml4",
        "theorem": theorem,
        "informal_statement": informal,
        "formal_statement": formal,
        "lean_code": lean_code,
        "compiler_feedback": feedback,
        "process_label": label,
        "split": split,
        "raw_ref": {
            "source_file": str(source_file),
            "source_line": source_line,
        },
        "authority": {
            "semantic_training_material": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
        "raw": raw,
    }
    payload["id"] = stable_hash(
        {
            "source": "pda_forml4",
            "source_file": str(source_file),
            "source_line": source_line,
            "theorem": theorem,
            "informal_statement": informal,
            "formal_statement": formal,
            "lean_code": lean_code,
        }
    )
    return payload


def _split_from_path(path: Path) -> str:
    name = path.name.lower()
    if "train" in name:
        return "train"
    if "test" in name:
        return "test"
    if "val" in name or "valid" in name:
        return "val"
    return "unknown"


def run_bridge(input_path: Path, output_dir: Path) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    out_path = output_dir / "pda_forml4_bridge.jsonl"
    rows = [normalize_record(raw, source_file, source_line) for raw, source_file, source_line in iter_json_records(input_path)]
    with out_path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
    labels: dict[str, int] = {}
    splits: dict[str, int] = {}
    for row in rows:
        labels[row["process_label"]] = labels.get(row["process_label"], 0) + 1
        splits[row["split"]] = splits.get(row["split"], 0) + 1
    summary = {
        "schema": SUMMARY_SCHEMA,
        "input": str(input_path),
        "output": str(out_path),
        "records": len(rows),
        "with_informal_statement": sum(1 for row in rows if row["informal_statement"]),
        "with_formal_statement": sum(1 for row in rows if row["formal_statement"]),
        "with_lean_code": sum(1 for row in rows if row["lean_code"]),
        "process_labels": dict(sorted(labels.items())),
        "splits": dict(sorted(splits.items())),
    }
    summary_path = output_dir / "pda_forml4_bridge_summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="PDA/FormL4 JSON/JSONL file or directory")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    args = parser.parse_args()
    summary = run_bridge(args.input, args.output_dir)
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
