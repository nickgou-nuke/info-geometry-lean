#!/usr/bin/env python3
"""Normalize lean-auto attempt traces into info-geometry diagnostic telemetry.

This bridge borrows the useful seam from lean-auto without importing it as proof
authority.  lean-auto has a strong architecture:

* local/user/lemma-database fact collection;
* monomorphization and lambda reification;
* SMT/TPTP/native backend sockets;
* unsat-core / premise-selection traces;
* optional proof reconstruction through a Lean-native backend.

The bridge records those surfaces as diagnostic telemetry only.  In particular,
trusted SMT/TPTP modes that discharge goals through `autoSMTSorry` or
`autoTPTPSorry` are never promoted to proof authority here.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Iterable

SCHEMA = "info_geometry.lean_auto_trace.v1"
STATS_SCHEMA = "info_geometry.lean_auto_trace.stats.v1"
DEFAULT_OUT = Path("artifacts/lean_auto/lean_auto_trace_bridge.jsonl")
DEFAULT_STATS = Path("artifacts/lean_auto/lean_auto_trace_bridge.stats.json")

TRUSTED_SORRY_MARKERS = {
    "autoSMTSorry",
    "autoTPTPSorry",
    "sorryAx",
    "admitAx",
}


def iter_input_paths(path: Path) -> Iterable[Path]:
    if not path.exists():
        raise SystemExit(f"input does not exist: {path}")
    if path.is_file():
        yield path
        return
    for child in sorted(path.rglob("*")):
        if child.is_file() and child.suffix.lower() in {".json", ".jsonl"}:
            yield child


def iter_records(path: Path) -> Iterable[tuple[Path, dict[str, Any]]]:
    for file_path in iter_input_paths(path):
        if file_path.suffix.lower() == ".jsonl":
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
        try:
            payload = json.loads(file_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise SystemExit(f"malformed JSON at {file_path}: {exc}") from exc
        if isinstance(payload, list):
            for row in payload:
                if isinstance(row, dict):
                    yield file_path, row
        elif isinstance(payload, dict):
            rows = payload.get("rows") or payload.get("attempts") or payload.get("traces")
            if isinstance(rows, list):
                for row in rows:
                    if isinstance(row, dict):
                        yield file_path, row
            else:
                yield file_path, payload


def as_list(value: Any) -> list[Any]:
    if value is None:
        return []
    if isinstance(value, list):
        return value
    if isinstance(value, tuple):
        return list(value)
    return [value]


def as_bool(value: Any, default: bool = False) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() in {"1", "true", "yes", "y", "on"}
    if value is None:
        return default
    return bool(value)


def as_int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def first_present(row: dict[str, Any], *keys: str, default: Any = None) -> Any:
    for key in keys:
        if key in row and row[key] is not None:
            return row[key]
    return default


def contains_trusted_sorry(row: dict[str, Any]) -> bool:
    haystack = json.dumps(row, ensure_ascii=False, sort_keys=True)
    return any(marker in haystack for marker in TRUSTED_SORRY_MARKERS)


def normalize_solver(row: dict[str, Any]) -> dict[str, Any]:
    solver = first_present(row, "solver", "solver_name", "backend", "mode", default="unknown")
    solver_kind = first_present(row, "solver_kind", "kind", default=None)
    trusted = as_bool(first_present(row, "trusted", "trust", "used_trust", default=False))
    trusted = trusted or contains_trusted_sorry(row)
    reconstructed = as_bool(
        first_present(
            row,
            "proof_reconstructed",
            "reconstructed",
            "kernel_checked",
            "native_checked",
            default=False,
        )
    )
    if trusted:
        proof_status = "trusted_external_sorry"
    elif reconstructed:
        proof_status = "lean_reconstructed_candidate"
    else:
        proof_status = "diagnostic_only"
    return {
        "solver": str(solver),
        "solver_kind": str(solver_kind or solver),
        "trusted_external_solver": trusted,
        "proof_reconstructed": reconstructed,
        "proof_status": proof_status,
    }


def normalize_fact_inventory(row: dict[str, Any]) -> dict[str, Any]:
    local = as_list(first_present(row, "local_lemmas", "lctx_lemmas", "lctx", default=[]))
    user = as_list(first_present(row, "user_lemmas", "hints", "terms", default=[]))
    lemdb = as_list(first_present(row, "lemma_databases", "lemdbs", "lemdb", default=[]))
    defeq = as_list(first_present(row, "defeq_lemmas", "defeqs", "defeq", default=[]))
    inhab = as_list(first_present(row, "inhabitation_lemmas", "inhabitation_facts", "inhs", default=[]))
    unsat_core = as_list(first_present(row, "unsat_core", "unsat_core_ids", "core", default=[]))
    return {
        "local_lemma_count": as_int(first_present(row, "local_lemma_count", default=len(local)), len(local)),
        "user_lemma_count": as_int(first_present(row, "user_lemma_count", default=len(user)), len(user)),
        "lemma_database_count": as_int(first_present(row, "lemma_database_count", default=len(lemdb)), len(lemdb)),
        "defeq_lemma_count": as_int(first_present(row, "defeq_lemma_count", default=len(defeq)), len(defeq)),
        "inhabitation_fact_count": as_int(first_present(row, "inhabitation_fact_count", default=len(inhab)), len(inhab)),
        "unsat_core_count": as_int(first_present(row, "unsat_core_count", default=len(unsat_core)), len(unsat_core)),
        "unsat_core": unsat_core,
    }


def normalize_translation(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "monomorphization_mode": str(first_present(row, "monomorphization_mode", "mono_mode", default="unknown")),
        "reification_target": str(first_present(row, "reification_target", "target", default="unknown")),
        "used_lambda_checker": as_bool(first_present(row, "used_lambda_checker", "lambda_checker", default=False)),
        "used_premise_selection": as_bool(first_present(row, "used_premise_selection", "premise_selection", default=False)),
        "unfold_hint_count": len(as_list(first_present(row, "unfolds", "unfold_hints", default=[]))),
        "defeq_hint_count": len(as_list(first_present(row, "defeqs", "defeq_hints", default=[]))),
    }


def normalize_row(source_path: Path, row: dict[str, Any]) -> dict[str, Any]:
    solver = normalize_solver(row)
    fact_inventory = normalize_fact_inventory(row)
    translation = normalize_translation(row)
    solved = as_bool(first_present(row, "solved", "success", "proved", default=False))
    if solver["trusted_external_solver"]:
        authority_stage = "trusted_external_not_promotable"
    elif solved and solver["proof_reconstructed"]:
        authority_stage = "lean_reconstructed_candidate"
    elif solved:
        authority_stage = "solver_claim_diagnostic_only"
    else:
        authority_stage = "failed_or_unknown"
    return {
        "schema": SCHEMA,
        "source": {
            "path": str(source_path),
            "raw_ref": first_present(row, "raw_ref", "id", "trace_id", default=None),
        },
        "context": {
            "declaration": first_present(row, "declaration", "theorem", "decl", "name", default=None),
            "goal_before": first_present(row, "goal_before", "goal", "goal_state", default=None),
        },
        "lean_auto": {
            "tactic": first_present(row, "tactic", default="auto"),
            "solver": solver,
            "fact_inventory": fact_inventory,
            "translation": translation,
            "error": first_present(row, "error", "diagnostic", "message", default=None),
            "elapsed_ms": first_present(row, "elapsed_ms", "time_ms", "duration_ms", default=None),
        },
        "labels": {
            "solved": solved,
            "authority_stage": authority_stage,
            "usable_as_training_positive": bool(solved and solver["proof_reconstructed"] and not solver["trusted_external_solver"]),
            "usable_as_failure_telemetry": not solved,
            "usable_as_premise_selection_prior": fact_inventory["unsat_core_count"] > 0,
        },
        "authority": {
            "diagnostic_only": True,
            "not_a_proof": True,
            "not_a_certificate": True,
            "external_solver_claim_not_authority": True,
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
    solver_counts: dict[str, int] = {}
    authority_counts: dict[str, int] = {}
    trusted_count = 0
    reconstructed_count = 0
    unsat_core_rows = 0
    for row in rows:
        solver = row["lean_auto"]["solver"]["solver"]
        solver_counts[solver] = solver_counts.get(solver, 0) + 1
        stage = row["labels"]["authority_stage"]
        authority_counts[stage] = authority_counts.get(stage, 0) + 1
        trusted_count += int(row["lean_auto"]["solver"]["trusted_external_solver"])
        reconstructed_count += int(row["lean_auto"]["solver"]["proof_reconstructed"])
        unsat_core_rows += int(row["lean_auto"]["fact_inventory"]["unsat_core_count"] > 0)
    return {
        "schema": STATS_SCHEMA,
        "input": str(input_path),
        "output": str(out_path),
        "rows": len(rows),
        "solver_counts": dict(sorted(solver_counts.items())),
        "authority_stage_counts": dict(sorted(authority_counts.items())),
        "trusted_external_solver_rows": trusted_count,
        "proof_reconstructed_rows": reconstructed_count,
        "unsat_core_rows": unsat_core_rows,
        "authority_boundary": {
            "diagnostic_only": True,
            "external_solver_claim_not_authority": True,
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
