#!/usr/bin/env python3
"""Normalize ImProver proof-optimization traces into diagnostic telemetry.

ImProver's useful borrow is the optimization-attempt record:
original proof, proposed rewrite, metric score/delta, compiler messages,
retrieval settings, and trajectory position.  This bridge keeps those as
training/audit data only.  Correctness still means Lean/Hive revalidation in
this repository; an ImProver row is never proof authority by itself.
"""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any, Iterable

SCHEMA = "info_geometry.improver_trace.v1"
STATS_SCHEMA = "info_geometry.improver_trace.stats.v1"
DEFAULT_OUT = Path("artifacts/improver/improver_trace_bridge.jsonl")
DEFAULT_STATS = Path("artifacts/improver/improver_trace_bridge.stats.json")


def iter_input_paths(path: Path) -> Iterable[Path]:
    if not path.exists():
        raise SystemExit(f"input does not exist: {path}")
    if path.is_file():
        yield path
        return
    for child in sorted(path.rglob("*")):
        if child.is_file() and child.suffix.lower() in {".json", ".jsonl", ".csv"}:
            yield child


def iter_records(path: Path) -> Iterable[tuple[Path, dict[str, Any]]]:
    for file_path in iter_input_paths(path):
        suffix = file_path.suffix.lower()
        if suffix == ".jsonl":
            with file_path.open(encoding="utf-8") as handle:
                for line_no, raw in enumerate(handle, start=1):
                    raw = raw.strip()
                    if not raw:
                        continue
                    try:
                        row = json.loads(raw)
                    except json.JSONDecodeError as exc:
                        raise SystemExit(f"malformed JSONL at {file_path}:{line_no}: {exc}") from exc
                    if isinstance(row, dict):
                        yield file_path, row
            continue
        if suffix == ".json":
            try:
                payload = json.loads(file_path.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                raise SystemExit(f"malformed JSON at {file_path}: {exc}") from exc
            if isinstance(payload, list):
                for row in payload:
                    if isinstance(row, dict):
                        yield file_path, row
            elif isinstance(payload, dict):
                rows = payload.get("rows") or payload.get("data") or payload.get("attempts") or payload.get("trajectories")
                if isinstance(rows, list):
                    for row in rows:
                        if isinstance(row, dict):
                            yield file_path, row
                else:
                    yield file_path, payload
            continue
        if suffix == ".csv":
            with file_path.open(encoding="utf-8", newline="") as handle:
                reader = csv.DictReader(handle)
                for row in reader:
                    yield file_path, dict(row)


def as_bool(value: Any, default: bool = False) -> bool:
    if isinstance(value, bool):
        return value
    if value is None:
        return default
    if isinstance(value, str):
        value = value.strip().lower()
        if value in {"true", "1", "yes", "y", "on"}:
            return True
        if value in {"false", "0", "no", "n", "off", "", "none", "null"}:
            return False
    return bool(value)


def as_float(value: Any) -> float | None:
    if value is None:
        return None
    if isinstance(value, str) and value.strip().lower() in {"", "none", "null", "nan"}:
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def as_int(value: Any, default: int = 0) -> int:
    try:
        if value is None or value == "":
            return default
        return int(value)
    except (TypeError, ValueError):
        return default


def first_present(row: dict[str, Any], *keys: str, default: Any = None) -> Any:
    for key in keys:
        if key in row and row[key] is not None:
            return row[key]
    return default


def error_count(text: Any) -> int:
    if text is None:
        return 0
    s = str(text).strip()
    if not s:
        return 0
    return max(1, s.lower().count("error") + s.lower().count("warning: declaration uses 'sorry'"))


def metric_direction(metric: str, row: dict[str, Any]) -> str:
    explicit = first_present(row, "minmax", "direction", default=None)
    if explicit:
        value = str(explicit).upper()
        if value in {"MIN", "MINIMIZE", "LOWER_IS_BETTER"}:
            return "MIN"
        if value in {"MAX", "MAXIMIZE", "HIGHER_IS_BETTER"}:
            return "MAX"
    metric_upper = metric.upper()
    if metric_upper in {"LENGTH", "REWRITE", "COMPLETION", "ERRORS"}:
        return "MIN"
    if metric_upper in {"READABILITY", "MODULARITY"}:
        return "MAX"
    return "UNKNOWN"


def improvement_label(og_score: float | None, new_score: float | None, direction: str) -> str:
    if og_score is None or new_score is None:
        return "unknown"
    if direction == "MIN":
        if new_score < og_score:
            return "improved"
        if new_score > og_score:
            return "regressed"
        return "unchanged"
    if direction == "MAX":
        if new_score > og_score:
            return "improved"
        if new_score < og_score:
            return "regressed"
        return "unchanged"
    return "unknown"


def normalize_row(source_path: Path, row: dict[str, Any]) -> dict[str, Any]:
    decl = first_present(row, "decl", "theorem", "declaration", "name", default=None)
    metric = str(first_present(row, "metric", "metric_name", default="unknown"))
    direction = metric_direction(metric, row)
    og_correct = as_bool(first_present(row, "og_correct", "original_correct", default=True), default=True)
    new_correct = as_bool(first_present(row, "new_correct", "correct", "candidate_correct", default=False))
    og_score = as_float(first_present(row, "og_score", "original_score", default=None))
    new_score = as_float(first_present(row, "new_score", "score", "candidate_score", default=None))
    delta = as_float(first_present(row, "delta", "metric_delta", default=None))
    label = improvement_label(og_score, new_score, direction)
    if new_correct and label == "improved":
        authority_stage = "verified_improvement_candidate"
    elif new_correct:
        authority_stage = "verified_rewrite_candidate"
    else:
        authority_stage = "failed_or_unverified_rewrite"
    og_errors = first_present(row, "og_errors", "original_errors", default="")
    new_errors = first_present(row, "new_errors", "errors", "candidate_errors", default="")
    return {
        "schema": SCHEMA,
        "source": {
            "path": str(source_path),
            "raw_ref": first_present(row, "id", "raw_ref", "trace_id", default=None),
        },
        "theorem": {
            "repo": first_present(row, "repo", "src", default=None),
            "file": first_present(row, "file", "leanFile", "lean_file", default=None),
            "declaration": decl,
        },
        "method": {
            "name": first_present(row, "method", "prompt_method", default=None),
            "model": first_present(row, "model", default=None),
            "n": first_present(row, "n", default=None),
            "trajectory_position": first_present(row, "trajectory_position", default=None),
            "annotation": as_bool(first_present(row, "annotation", default=False)),
            "syntax_search": as_bool(first_present(row, "syntax_search", default=False)),
            "mathlib_search": as_bool(first_present(row, "mathlib_search", default=False)),
            "examples": as_int(first_present(row, "examples", default=0)),
            "improved_context": as_bool(first_present(row, "improved_context", default=False)),
        },
        "metric": {
            "name": metric,
            "direction": direction,
            "original_score": og_score,
            "new_score": new_score,
            "delta": delta,
            "improvement_label": label,
        },
        "correctness": {
            "original_correct": og_correct,
            "new_correct": new_correct,
            "original_error_count": error_count(og_errors),
            "new_error_count": error_count(new_errors),
            "original_errors": og_errors,
            "new_errors": new_errors,
        },
        "proofs": {
            "original_raw": first_present(row, "og_raw", "original_raw", "input", default=None),
            "new_raw": first_present(row, "new_raw", "raw", "output", default=None),
        },
        "labels": {
            "authority_stage": authority_stage,
            "usable_as_rewrite_positive": bool(new_correct and label in {"improved", "unchanged"}),
            "usable_as_failure_telemetry": not new_correct,
            "usable_as_metric_preference_pair": bool(og_score is not None and new_score is not None and new_correct),
        },
        "authority": {
            "diagnostic_only": True,
            "not_a_proof": True,
            "not_a_certificate": True,
            "requires_repo_revalidation": True,
            "lean_kernel_remains_proof_authority": True,
        },
        "raw": row,
    }


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
    return len(rows)


def summarize(rows: list[dict[str, Any]], input_path: Path, out_path: Path) -> dict[str, Any]:
    metric_counts: dict[str, int] = {}
    label_counts: dict[str, int] = {}
    authority_counts: dict[str, int] = {}
    positives = 0
    failures = 0
    preference_pairs = 0
    for row in rows:
        metric = row["metric"]["name"]
        metric_counts[metric] = metric_counts.get(metric, 0) + 1
        label = row["metric"]["improvement_label"]
        label_counts[label] = label_counts.get(label, 0) + 1
        stage = row["labels"]["authority_stage"]
        authority_counts[stage] = authority_counts.get(stage, 0) + 1
        positives += int(row["labels"]["usable_as_rewrite_positive"])
        failures += int(row["labels"]["usable_as_failure_telemetry"])
        preference_pairs += int(row["labels"]["usable_as_metric_preference_pair"])
    return {
        "schema": STATS_SCHEMA,
        "input": str(input_path),
        "output": str(out_path),
        "rows": len(rows),
        "metric_counts": dict(sorted(metric_counts.items())),
        "improvement_label_counts": dict(sorted(label_counts.items())),
        "authority_stage_counts": dict(sorted(authority_counts.items())),
        "rewrite_positive_rows": positives,
        "failure_telemetry_rows": failures,
        "metric_preference_pair_rows": preference_pairs,
        "authority_boundary": {
            "diagnostic_only": True,
            "requires_repo_revalidation": True,
            "lean_kernel_remains_proof_authority": True,
        },
    }


def run(input_path: Path, out_path: Path, stats_path: Path) -> dict[str, Any]:
    rows = [normalize_row(source, row) for source, row in iter_records(input_path)]
    written = write_jsonl(out_path, rows)
    stats = summarize(rows, input_path, out_path)
    stats["rows_written"] = written
    stats_path.parent.mkdir(parents=True, exist_ok=True)
    stats_path.write_text(json.dumps(stats, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return stats


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--stats-out", type=Path, default=DEFAULT_STATS)
    args = parser.parse_args()
    stats = run(args.input, args.out, args.stats_out)
    print(json.dumps(stats, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
