#!/usr/bin/env python3
"""Enrich tactic path-ranking rows with local operator-spectrum proxies.

This pass operates on `reports/training/tactic_path_ranking.jsonl`.

It does not build a global DAG matrix and it does not compute a certified
Drazin inverse.  Instead, each decision point is treated as a tiny local
transition proxy:

* positive candidates contribute to a success/core sector;
* failure/stall candidates contribute to transient or nilpotent/stall sectors;
* repeated failing tactic families increase cycle/stall pressure.

Authority boundary:
  - all fields emitted here are diagnostic priors;
  - Lean-checked labels remain the training authority;
  - no spectral/Hodge/Drazin diagnostic is a proof or certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
_SRC = ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from igf.common.json_io import iter_jsonl, write_jsonl

ROW_SCHEMA = "info_geometry.tactic_operator_spectrum.v1"
STATS_SCHEMA = "info_geometry.tactic_operator_spectrum.stats.v1"
DEFAULT_INPUT = Path("reports/training/tactic_path_ranking.jsonl")
DEFAULT_OUT = Path("reports/training/tactic_path_ranking.operator_enriched.jsonl")
DEFAULT_STATS = Path("reports/training/tactic_path_operator_spectrum.stats.json")


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


def safe_float(value: Any, default: float = 0.0) -> float:
    try:
        out = float(value)
    except (TypeError, ValueError):
        return default
    return out if math.isfinite(out) else default


def clamp01(value: float) -> float:
    if not math.isfinite(value):
        return 0.0
    return max(0.0, min(1.0, value))


def tactic_family(candidate: dict[str, Any]) -> str:
    tactic = str(candidate.get("tactic") or "").strip()
    return tactic.split()[0] if tactic else ""


def is_positive(candidate: dict[str, Any]) -> bool:
    return int(candidate.get("is_positive") or candidate.get("label") or 0) == 1


def stall_type(candidate: dict[str, Any]) -> str:
    return str(candidate.get("stall_type") or "none")


def is_stall(candidate: dict[str, Any]) -> bool:
    if stall_type(candidate) not in {"", "none", "failure"}:
        return True
    return str(candidate.get("edge_type") or "") == "stall"


def candidate_score(candidate: dict[str, Any]) -> float:
    return clamp01(
        safe_float(
            candidate.get("balanced_operator_score"),
            safe_float(candidate.get("operator_score"), 0.5),
        )
    )


def candidate_base_weight(candidate: dict[str, Any]) -> float:
    return max(
        0.0,
        safe_float(
            candidate.get("final_operator_sampling_weight"),
            safe_float(candidate.get("sampling_priority"), 1.0),
        ),
    )


def repeated_family_pressure(candidates: list[dict[str, Any]]) -> float:
    if not candidates:
        return 0.0
    failures = [
        tactic_family(candidate)
        for candidate in candidates
        if not is_positive(candidate) and tactic_family(candidate)
    ]
    counts = Counter(failures)
    repeated = sum(max(0, count - 1) for count in counts.values())
    return clamp01(repeated / max(len(candidates), 1))


def row_feature(row: dict[str, Any], key: str, default: float = 0.0) -> float:
    graph_features = row.get("graph_features")
    if isinstance(graph_features, dict):
        return safe_float(graph_features.get(key), default)
    return default


def compute_operator_spectrum(row: dict[str, Any]) -> dict[str, Any]:
    candidates = [c for c in row.get("candidates") or [] if isinstance(c, dict)]
    n = len(candidates)
    if n == 0:
        core_mass = nilpotent_stall_mass = transient_mass = 0.0
        success_absorption_mass = stall_absorption_mass = 0.0
        failure_mass = 0.0
    else:
        positive_scores = [candidate_score(c) for c in candidates if is_positive(c)]
        stall_scores = [1.0 - candidate_score(c) for c in candidates if is_stall(c)]
        failure_scores = [
            1.0 - candidate_score(c)
            for c in candidates
            if not is_positive(c) and not is_stall(c)
        ]
        repeat_pressure = repeated_family_pressure(candidates)
        success_signal = sum(positive_scores)
        stall_signal = sum(stall_scores) + repeat_pressure * n
        failure_signal = sum(failure_scores)
        total_signal = max(success_signal + stall_signal + failure_signal, 1e-9)
        core_mass = clamp01(success_signal / total_signal)
        nilpotent_stall_mass = clamp01(stall_signal / total_signal)
        transient_mass = clamp01(failure_signal / total_signal)
        success_absorption_mass = core_mass
        stall_absorption_mass = nilpotent_stall_mass
        failure_mass = transient_mass

    hodge_input = clamp01(row_feature(row, "hodge_harmonic_signal"))
    cycle_pressure = clamp01(repeated_family_pressure(candidates))
    boundary_pressure = clamp01(
        (sum(1 for c in candidates if not is_positive(c)) / max(len(candidates), 1))
        if candidates
        else 0.0
    )
    harmonic_residual = clamp01(0.5 * hodge_input + 0.3 * nilpotent_stall_mass + 0.2 * cycle_pressure)

    success_flow = success_absorption_mass
    failure_flow = clamp01(stall_absorption_mass + transient_mass)
    chiral_balance = clamp01(0.5 + 0.5 * (success_flow - failure_flow))
    mp_drazin_mismatch = clamp01(abs(boundary_pressure - core_mass))

    return {
        "schema": ROW_SCHEMA,
        "operator_scope": "local_decision_point",
        "diagnostic_only": True,
        "transition_proxy": {
            "candidate_count": n,
            "success_candidate_count": sum(1 for c in candidates if is_positive(c)),
            "failure_candidate_count": sum(1 for c in candidates if not is_positive(c)),
            "stall_candidate_count": sum(1 for c in candidates if is_stall(c)),
            "repeated_family_pressure": round(cycle_pressure, 6),
            "diagnostic_only": True,
        },
        "drazin_proxy": {
            "core_mass": round(core_mass, 6),
            "nilpotent_stall_mass": round(nilpotent_stall_mass, 6),
            "transient_mass": round(transient_mass, 6),
            "success_absorption_mass": round(success_absorption_mass, 6),
            "stall_absorption_mass": round(stall_absorption_mass, 6),
            "failure_mass": round(failure_mass, 6),
            "diagnostic_only": True,
        },
        "hodge_proxy": {
            "harmonic_residual": round(harmonic_residual, 6),
            "cycle_pressure": round(cycle_pressure, 6),
            "boundary_pressure": round(boundary_pressure, 6),
            "diagnostic_only": True,
        },
        "dirac_proxy": {
            "success_flow": round(success_flow, 6),
            "failure_flow": round(failure_flow, 6),
            "chiral_balance": round(chiral_balance, 6),
            "diagnostic_only": True,
        },
        "moore_penrose_drazin_proxy": {
            "mp_drazin_mismatch_proxy": round(mp_drazin_mismatch, 6),
            "diagnostic_only": True,
        },
        "authority": {
            "not_a_proof": True,
            "not_a_certificate": True,
            "diagnostic_prior_only": True,
            "lean_remains_proof_authority": True,
        },
    }


def enrich_candidate(
    candidate: dict[str, Any],
    spectrum: dict[str, Any],
    *,
    alpha: float = 0.10,
    beta: float = 0.05,
    gamma: float = 0.10,
) -> dict[str, Any]:
    out = dict(candidate)
    drazin = spectrum["drazin_proxy"]
    hodge = spectrum["hodge_proxy"]
    dirac = spectrum["dirac_proxy"]
    score = candidate_score(candidate)
    core_mass = safe_float(drazin.get("core_mass"))
    nil_mass = safe_float(drazin.get("nilpotent_stall_mass"))
    transient_mass = safe_float(drazin.get("transient_mass"))
    boundary_pressure = safe_float(hodge.get("boundary_pressure"))
    success_flow = safe_float(dirac.get("success_flow"))

    if is_positive(candidate):
        drazin_core_weight = clamp01(core_mass * (0.5 + 0.5 * score))
        nilpotent_penalty = clamp01(nil_mass * 0.25)
        transient_weight = clamp01(transient_mass * 0.25)
    elif is_stall(candidate):
        drazin_core_weight = clamp01(core_mass * 0.25 * score)
        nilpotent_penalty = clamp01(nil_mass * (0.75 + 0.25 * (1.0 - score)))
        transient_weight = clamp01(transient_mass * 0.5)
    else:
        drazin_core_weight = clamp01(core_mass * 0.5 * score)
        nilpotent_penalty = clamp01(nil_mass * 0.5 + boundary_pressure * 0.25)
        transient_weight = clamp01(transient_mass * (0.75 + 0.25 * (1.0 - score)))

    dirac_flow_weight = clamp01(success_flow if is_positive(candidate) else 1.0 - success_flow)
    base = candidate_base_weight(candidate)
    multiplier = (
        (1.0 + alpha * drazin_core_weight)
        * (1.0 + beta * transient_weight)
        * (1.0 - gamma * nilpotent_penalty)
    )
    final = max(0.0, base * multiplier)
    out["operator_enrichment"] = {
        "schema": "info_geometry.tactic_operator_spectrum_candidate.v1",
        "drazin_core_weight": round(drazin_core_weight, 6),
        "nilpotent_penalty": round(nilpotent_penalty, 6),
        "transient_weight": round(transient_weight, 6),
        "hodge_boundary_penalty": round(boundary_pressure, 6),
        "dirac_flow_weight": round(dirac_flow_weight, 6),
        "alpha": alpha,
        "beta": beta,
        "gamma": gamma,
        "operator_spectrum_multiplier": round(multiplier, 6),
        "final_operator_sampling_weight": round(final, 6),
        "diagnostic_only": True,
        "authority": {
            "not_a_proof": True,
            "not_a_certificate": True,
            "lean_remains_proof_authority": True,
        },
    }
    out["final_operator_sampling_weight"] = round(final, 6)
    return out


def decision_point_key(row: dict[str, Any]) -> str:
    context = row.get("context") if isinstance(row.get("context"), dict) else {}
    candidates = [c for c in row.get("candidates") or [] if isinstance(c, dict)]
    if context.get("goal_hash"):
        return str(context["goal_hash"])
    if context.get("goal_hash_before"):
        return str(context["goal_hash_before"])
    if context.get("goal_before"):
        return str(context["goal_before"])
    if context.get("goal_state"):
        return str(context["goal_state"])
    for candidate in candidates:
        if candidate.get("goal_hash_before"):
            return str(candidate["goal_hash_before"])
    if row.get("decision_id"):
        return str(row["decision_id"])
    return stable_hash(row)


def aggregate_decision_point_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    candidates: list[dict[str, Any]] = []
    hodge_values: list[float] = []
    positive_count = 0
    negative_count = 0
    stall_count = 0
    for row in rows:
        row_candidates = [c for c in row.get("candidates") or [] if isinstance(c, dict)]
        candidates.extend(row_candidates)
        graph_features = row.get("graph_features") if isinstance(row.get("graph_features"), dict) else {}
        if "hodge_harmonic_signal" in graph_features:
            hodge_values.append(clamp01(safe_float(graph_features.get("hodge_harmonic_signal"))))
        positive_count += sum(1 for candidate in row_candidates if is_positive(candidate))
        negative_count += sum(1 for candidate in row_candidates if not is_positive(candidate))
        stall_count += sum(1 for candidate in row_candidates if is_stall(candidate))
    first = rows[0] if rows else {}
    context = first.get("context") if isinstance(first.get("context"), dict) else {}
    provenance = first.get("provenance") if isinstance(first.get("provenance"), dict) else {}
    hodge_harmonic_signal = sum(hodge_values) / len(hodge_values) if hodge_values else 0.0
    return {
        "schema": first.get("schema", "info_geometry.tactic_path_ranking.v1"),
        "decision_id": decision_point_key(first) if first else "empty",
        "context": context,
        "graph_features": {
            "hodge_harmonic_signal": hodge_harmonic_signal,
            "candidate_count": len(candidates),
            "positive_count": positive_count,
            "negative_count": negative_count,
            "stall_count": stall_count,
        },
        "provenance": provenance,
        "candidates": candidates,
    }


def enrich_row(
    row: dict[str, Any],
    *,
    alpha: float = 0.10,
    beta: float = 0.05,
    gamma: float = 0.10,
    spectrum: dict[str, Any] | None = None,
    decision_point_row_count: int = 1,
) -> dict[str, Any]:
    out = dict(row)
    spectrum = dict(spectrum or compute_operator_spectrum(row))
    spectrum["decision_point_key"] = decision_point_key(row)
    spectrum["decision_point_row_count"] = decision_point_row_count
    candidates = [c for c in row.get("candidates") or [] if isinstance(c, dict)]
    enriched_candidates = [
        enrich_candidate(candidate, spectrum, alpha=alpha, beta=beta, gamma=gamma)
        for candidate in candidates
    ]
    enriched_candidates.sort(
        key=lambda c: (
            -safe_float(c.get("final_operator_sampling_weight")),
            str(c.get("edge_id") or ""),
            str(c.get("tactic") or ""),
        )
    )
    out["operator_spectrum"] = spectrum
    out["candidates"] = enriched_candidates
    out["operator_spectrum_enrichment_id"] = stable_hash(
        {
            "row_id": row.get("id"),
            "spectrum": spectrum,
            "candidate_ids": [c.get("edge_id") for c in enriched_candidates],
        }
    )
    return out


def summarize(rows: list[dict[str, Any]], *, input_path: Path, out_path: Path, alpha: float, beta: float, gamma: float) -> dict[str, Any]:
    core: list[float] = []
    nil: list[float] = []
    transient: list[float] = []
    final_weights: list[float] = []
    candidate_count = 0
    stall_rows = 0
    for row in rows:
        spectrum = row.get("operator_spectrum") if isinstance(row.get("operator_spectrum"), dict) else {}
        drazin = spectrum.get("drazin_proxy") if isinstance(spectrum.get("drazin_proxy"), dict) else {}
        core.append(safe_float(drazin.get("core_mass")))
        nil.append(safe_float(drazin.get("nilpotent_stall_mass")))
        transient.append(safe_float(drazin.get("transient_mass")))
        if safe_float(drazin.get("nilpotent_stall_mass")) > 0:
            stall_rows += 1
        for candidate in row.get("candidates") or []:
            if isinstance(candidate, dict):
                candidate_count += 1
                final_weights.append(safe_float(candidate.get("final_operator_sampling_weight")))
    return {
        "schema": STATS_SCHEMA,
        "input": str(input_path),
        "output": str(out_path),
        "rows": len(rows),
        "candidate_count": candidate_count,
        "rows_with_nilpotent_stall_mass": stall_rows,
        "alpha": alpha,
        "beta": beta,
        "gamma": gamma,
        "core_mass": numeric_summary(core),
        "nilpotent_stall_mass": numeric_summary(nil),
        "transient_mass": numeric_summary(transient),
        "final_operator_sampling_weight": numeric_summary(final_weights),
        "authority": {
            "diagnostic_only": True,
            "not_a_proof": True,
            "not_a_certificate": True,
            "lean_remains_proof_authority": True,
        },
    }


def numeric_summary(values: list[float]) -> dict[str, float | int | None]:
    if not values:
        return {"count": 0, "min": None, "max": None, "mean": None}
    return {
        "count": len(values),
        "min": round(min(values), 6),
        "max": round(max(values), 6),
        "mean": round(sum(values) / len(values), 6),
    }


def run(
    *,
    input_path: Path,
    out_path: Path,
    stats_path: Path,
    alpha: float = 0.10,
    beta: float = 0.05,
    gamma: float = 0.10,
) -> dict[str, Any]:
    input_rows = list(iter_jsonl(input_path))
    groups: dict[str, list[dict[str, Any]]] = {}
    for row in input_rows:
        groups.setdefault(decision_point_key(row), []).append(row)
    spectra = {
        key: compute_operator_spectrum(aggregate_decision_point_rows(group_rows))
        for key, group_rows in groups.items()
    }
    rows = [
        enrich_row(
            row,
            alpha=alpha,
            beta=beta,
            gamma=gamma,
            spectrum=spectra[decision_point_key(row)],
            decision_point_row_count=len(groups[decision_point_key(row)]),
        )
        for row in input_rows
    ]
    written = write_jsonl(out_path, rows)
    stats = summarize(rows, input_path=input_path, out_path=out_path, alpha=alpha, beta=beta, gamma=gamma)
    stats["decision_point_count"] = len(groups)
    stats["rows_written"] = written
    stats_path.parent.mkdir(parents=True, exist_ok=True)
    stats_path.write_text(json.dumps(stats, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return stats


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--stats-out", type=Path, default=DEFAULT_STATS)
    parser.add_argument("--alpha", type=float, default=0.10)
    parser.add_argument("--beta", type=float, default=0.05)
    parser.add_argument("--gamma", type=float, default=0.10)
    args = parser.parse_args()
    stats = run(
        input_path=args.input,
        out_path=args.out,
        stats_path=args.stats_out,
        alpha=args.alpha,
        beta=args.beta,
        gamma=args.gamma,
    )
    print(json.dumps(stats, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
