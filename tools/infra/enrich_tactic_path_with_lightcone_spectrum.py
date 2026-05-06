#!/usr/bin/env python3
"""Attach local lightcone spectral diagnostics to tactic path-ranking rows.

This is an optional enrichment pass over reports/training/tactic_path_ranking.jsonl.
It consumes a bounded local-lightcone spectral report produced by
`tools/infra/lightcone_spectral_filter.py` and adds conservative diagnostic
weights to each decision point/candidate.

Authority boundary:
  - the spectral report is a navigation prior, not proof evidence;
  - existing Lean-verified labels remain the training authority;
  - constants are intentionally small by default so diagnostics do not dominate
    verified success/failure telemetry.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from collections import Counter
from pathlib import Path
from typing import Any

SCHEMA = "info_geometry.tactic_lightcone_operator_enrichment.v1"
CONTEXT_SCHEMA = "info_geometry.tactic_lightcone_operator_context.v1"
DEFAULT_INPUT = Path("reports/training/tactic_path_ranking.jsonl")
DEFAULT_OUT = Path("reports/training/tactic_path_ranking.spectral_enriched.jsonl")
DEFAULT_STATS = Path("reports/training/tactic_path_ranking.spectral_enriched.stats.json")


def iter_jsonl(path: Path):
    if not path.exists():
        raise SystemExit(f"input JSONL does not exist: {path}")
    with path.open("r", encoding="utf-8") as f:
        for lineno, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise SystemExit(f"malformed JSON in {path} at line {lineno}: {exc}") from exc
            if isinstance(row, dict):
                yield row


def stable_hash(*parts: Any) -> str:
    h = hashlib.sha256()
    for part in parts:
        h.update(json.dumps(part, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
        h.update(b"\0")
    return h.hexdigest()[:24]


def clamp01(x: float) -> float:
    if not math.isfinite(x):
        return 0.0
    return max(0.0, min(1.0, x))


def safe_float(value: Any, default: float = 0.0) -> float:
    try:
        out = float(value)
    except (TypeError, ValueError):
        return default
    return out if math.isfinite(out) else default


def load_spectral_report(path: Path) -> dict[str, Any]:
    report = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(report, dict):
        raise SystemExit(f"spectral report must be a JSON object: {path}")
    if report.get("schema") != "info_geometry.local_lightcone_spectral_filter.v1":
        raise SystemExit(f"unexpected spectral report schema in {path}: {report.get('schema')!r}")
    return report


def normalize_node_scores(report: dict[str, Any]) -> dict[str, dict[str, float]]:
    rows = [node for node in report.get("nodes") or [] if isinstance(node, dict)]
    max_core = max((safe_float(r.get("drazin_core_weight")) for r in rows), default=0.0)
    max_harm = max((safe_float(r.get("hodge_harmonic_weight")) for r in rows), default=0.0)
    max_nil = max((safe_float(r.get("nilpotent_residue_weight")) for r in rows), default=0.0)
    out: dict[str, dict[str, float]] = {}
    for row in rows:
        name = row.get("name")
        if not isinstance(name, str) or not name:
            continue
        core = safe_float(row.get("drazin_core_weight"))
        harm = safe_float(row.get("hodge_harmonic_weight"))
        nil = safe_float(row.get("nilpotent_residue_weight"))
        out[name] = {
            "core": clamp01(core / max_core) if max_core > 0 else 0.0,
            "harmonic": clamp01(harm / max_harm) if max_harm > 0 else 0.0,
            "nilpotent": clamp01(nil / max_nil) if max_nil > 0 else 0.0,
            "raw_core": core,
            "raw_harmonic": harm,
            "raw_nilpotent": nil,
        }
    return out


def context_for(report: dict[str, Any], source_report: Path, node_scores: dict[str, dict[str, float]], apex: str | None) -> dict[str, Any]:
    drazin = report.get("drazin") if isinstance(report.get("drazin"), dict) else {}
    hodge = report.get("hodge") if isinstance(report.get("hodge"), dict) else {}
    apex_scores = node_scores.get(apex or "", {})
    return {
        "schema": CONTEXT_SCHEMA,
        "source_report": str(source_report),
        "drazin_nonzero_schur_dim": int(drazin.get("nonzero_schur_dim") or 0),
        "drazin_index": int(drazin.get("index") or 0),
        "hodge_harmonic_dim": int(hodge.get("harmonic_dim") or 0),
        "apex": apex,
        "apex_core_weight": apex_scores.get("core", 0.0),
        "apex_nilpotent_residue_weight": apex_scores.get("nilpotent", 0.0),
        "apex_hodge_harmonic_weight": apex_scores.get("harmonic", 0.0),
        "diagnostic_only": True,
        "authority": {
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
            "spectral_context_is_optional_prior": True,
        },
    }


def candidate_anchor_names(row: dict[str, Any], candidate: dict[str, Any], apex: str | None) -> list[str]:
    names: list[str] = []
    for value in (
        candidate.get("declaration"),
        candidate.get("theorem"),
        candidate.get("decl"),
        row.get("theorem"),
        row.get("apex"),
        apex,
    ):
        if isinstance(value, str) and value:
            names.append(value)
    context = row.get("lightcone_operator_context")
    if isinstance(context, dict):
        value = context.get("apex")
        if isinstance(value, str) and value:
            names.append(value)
    return names


def score_for_candidate(row: dict[str, Any], candidate: dict[str, Any], node_scores: dict[str, dict[str, float]], apex: str | None) -> dict[str, float]:
    for name in candidate_anchor_names(row, candidate, apex):
        if name in node_scores:
            return node_scores[name]
    return {"core": 0.0, "harmonic": 0.0, "nilpotent": 0.0, "raw_core": 0.0, "raw_harmonic": 0.0, "raw_nilpotent": 0.0}


def enrich_candidate(
    row: dict[str, Any],
    candidate: dict[str, Any],
    *,
    node_scores: dict[str, dict[str, float]],
    apex: str | None,
    alpha: float,
    beta: float,
    gamma: float,
) -> dict[str, Any]:
    out = dict(candidate)
    scores = score_for_candidate(row, candidate, node_scores, apex)
    base = safe_float(candidate.get("sampling_priority"), safe_float(candidate.get("final_operator_sampling_weight"), 1.0))
    multiplier = (1.0 + alpha * scores["core"]) * (1.0 + beta * scores["harmonic"]) * (1.0 - gamma * scores["nilpotent"])
    multiplier = max(0.0, multiplier)
    final = base * multiplier
    out["operator_enrichment"] = {
        "schema": SCHEMA,
        "drazin_core_weight": scores["core"],
        "nilpotent_penalty": scores["nilpotent"],
        "hodge_harmonic_weight": scores["harmonic"],
        "dirac_flow_weight": max(0.0, scores["core"] - scores["nilpotent"]),
        "raw_drazin_core_weight": scores["raw_core"],
        "raw_nilpotent_residue_weight": scores["raw_nilpotent"],
        "raw_hodge_harmonic_weight": scores["raw_harmonic"],
        "alpha": alpha,
        "beta": beta,
        "gamma": gamma,
        "lightcone_multiplier": multiplier,
        "final_operator_sampling_weight": final,
        "diagnostic_only": True,
    }
    out["final_operator_sampling_weight"] = final
    return out


def infer_apex(args_apex: str | None, report: dict[str, Any], rows: list[dict[str, Any]]) -> str | None:
    if args_apex:
        return args_apex
    for row in rows:
        for key in ("theorem", "apex", "declaration"):
            value = row.get(key)
            if isinstance(value, str) and value:
                return value
    nodes = report.get("nodes") or []
    if isinstance(nodes, list) and nodes:
        first = nodes[0]
        if isinstance(first, dict) and isinstance(first.get("name"), str):
            return first["name"]
    return None


def enrich_rows(
    rows: list[dict[str, Any]],
    report: dict[str, Any],
    *,
    source_report: Path,
    apex: str | None,
    alpha: float,
    beta: float,
    gamma: float,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    node_scores = normalize_node_scores(report)
    context = context_for(report, source_report, node_scores, apex)
    enriched: list[dict[str, Any]] = []
    candidate_count = 0
    touched_candidates = 0
    final_weights: list[float] = []
    trace_sources: Counter[str] = Counter()

    for row in rows:
        out = dict(row)
        out["lightcone_operator_context"] = context
        candidates = row.get("candidates") if isinstance(row.get("candidates"), list) else []
        enriched_candidates: list[dict[str, Any]] = []
        for candidate in candidates:
            if not isinstance(candidate, dict):
                continue
            candidate_count += 1
            enriched_candidate = enrich_candidate(
                row,
                candidate,
                node_scores=node_scores,
                apex=apex,
                alpha=alpha,
                beta=beta,
                gamma=gamma,
            )
            touched_candidates += 1
            final_weights.append(safe_float(enriched_candidate.get("final_operator_sampling_weight")))
            src = enriched_candidate.get("trace_source") or row.get("trace_source") or "unknown"
            trace_sources[str(src)] += 1
            enriched_candidates.append(enriched_candidate)
        if enriched_candidates:
            enriched_candidates.sort(key=lambda c: (-safe_float(c.get("final_operator_sampling_weight")), str(c.get("tactic") or c.get("edge_id") or "")))
            out["candidates"] = enriched_candidates
        out["spectral_enrichment_id"] = stable_hash(out.get("id"), context, len(enriched_candidates))
        enriched.append(out)

    stats = {
        "schema": "info_geometry.tactic_lightcone_operator_enrichment.stats.v1",
        "source_report": str(source_report),
        "rows": len(rows),
        "candidate_count": candidate_count,
        "enriched_candidate_count": touched_candidates,
        "apex": apex,
        "alpha": alpha,
        "beta": beta,
        "gamma": gamma,
        "trace_sources": dict(sorted(trace_sources.items())),
        "final_operator_sampling_weight": {
            "min": min(final_weights) if final_weights else 0.0,
            "max": max(final_weights) if final_weights else 0.0,
            "mean": (sum(final_weights) / len(final_weights)) if final_weights else 0.0,
        },
        "context": context,
        "warning": "Diagnostic enrichment only; Lean-verified labels remain authoritative.",
    }
    return enriched, stats


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        for row in rows:
            f.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT, help="tactic_path_ranking.jsonl input")
    parser.add_argument("--spectral-report", type=Path, required=True, help="JSON report from lightcone_spectral_filter.py")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--stats-out", type=Path, default=DEFAULT_STATS)
    parser.add_argument("--apex", help="Optional apex declaration name for matching spectral node scores")
    parser.add_argument("--alpha", type=float, default=0.10, help="small multiplier for normalized Drazin core weight")
    parser.add_argument("--beta", type=float, default=0.05, help="small multiplier for normalized Hodge harmonic weight")
    parser.add_argument("--gamma", type=float, default=0.10, help="small penalty for normalized nilpotent residue weight")
    args = parser.parse_args()

    rows = list(iter_jsonl(args.input) or [])
    report = load_spectral_report(args.spectral_report)
    apex = infer_apex(args.apex, report, rows)
    enriched, stats = enrich_rows(
        rows,
        report,
        source_report=args.spectral_report,
        apex=apex,
        alpha=args.alpha,
        beta=args.beta,
        gamma=args.gamma,
    )
    write_jsonl(args.out, enriched)
    args.stats_out.parent.mkdir(parents=True, exist_ok=True)
    args.stats_out.write_text(json.dumps(stats, indent=2, ensure_ascii=False, sort_keys=True), encoding="utf-8")
    print(f"wrote {len(enriched)} enriched tactic-ranking rows to {args.out}")
    print(f"wrote enrichment stats to {args.stats_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
