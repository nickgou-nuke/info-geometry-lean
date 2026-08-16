#!/usr/bin/env python3
"""Analyze tactic path ranking datasets before reranker training.

This script inspects the Spectral-Journey-style ranking rows emitted by
build_tactic_path_ranking_dataset.py.  It measures whether the dataset has useful
mixed decision points, which stall types dominate, and how the current diagnostic
operator_score baseline ranks successful candidates.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable

SCHEMA = "info_geometry.tactic_path_ranking.analysis.v1"
DEFAULT_INPUT = Path("reports/training/tactic_path_ranking.jsonl")
DEFAULT_OUT = Path("reports/training/tactic_path_ranking.analysis.json")


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def _is_positive(candidate: dict[str, Any]) -> bool:
    return int(candidate.get("is_positive") or 0) == 1


def _ranked_candidates(row: dict[str, Any]) -> list[dict[str, Any]]:
    candidates = [c for c in row.get("candidates") or [] if isinstance(c, dict)]
    return sorted(candidates, key=lambda c: (-float(c.get("operator_score") or 0.0), str(c.get("tactic") or "")))


def _topk_hit(row: dict[str, Any], k: int) -> bool:
    ranked = _ranked_candidates(row)[:k]
    return any(_is_positive(candidate) for candidate in ranked)


def _first_positive_rank(row: dict[str, Any]) -> int | None:
    for idx, candidate in enumerate(_ranked_candidates(row), start=1):
        if _is_positive(candidate):
            return idx
    return None


def analyze_rows(rows: list[dict[str, Any]], *, top_k: int) -> dict[str, Any]:
    split_counts: Counter[str] = Counter()
    source_counts: Counter[str] = Counter()
    authority_counts: Counter[str] = Counter()
    stall_counts: Counter[str] = Counter()
    edge_type_counts: Counter[str] = Counter()
    candidate_positive: Counter[str] = Counter()
    candidate_count_hist: Counter[str] = Counter()
    harmonic_buckets: Counter[str] = Counter()
    sampling_priorities: list[float] = []
    balanced_scores: list[float] = []
    mixed_rows = 0
    positive_rows = 0
    failure_only_rows = 0
    stall_rows = 0
    top1_hits = 0
    topk_hits = 0
    rank_sum = 0
    rank_count = 0
    source_top1: dict[str, Counter[str]] = defaultdict(Counter)
    authority_top1: dict[str, Counter[str]] = defaultdict(Counter)

    for row in rows:
        split_counts[str(row.get("split") or "unknown")] += 1
        provenance = row.get("provenance") if isinstance(row.get("provenance"), dict) else {}
        for source in provenance.get("trace_sources") or []:
            source_counts[str(source or "unknown")] += 1
        for authority in provenance.get("authority_stages") or []:
            authority_counts[str(authority or "unknown")] += 1

        candidates = [c for c in row.get("candidates") or [] if isinstance(c, dict)]
        positives = sum(1 for c in candidates if _is_positive(c))
        negatives = len(candidates) - positives
        stalls = sum(1 for c in candidates if str(c.get("stall_type") or "none") != "none")
        if positives > 0:
            positive_rows += 1
        if positives == 0 and negatives > 0:
            failure_only_rows += 1
        if positives > 0 and negatives > 0:
            mixed_rows += 1
        if stalls > 0:
            stall_rows += 1

        candidate_count_hist[str(len(candidates))] += 1
        harmonic = float((row.get("graph_features") or {}).get("hodge_harmonic_signal") or 0.0)
        harmonic_buckets[_bucket(harmonic)] += 1

        for candidate in candidates:
            candidate_positive[str(int(_is_positive(candidate)))] += 1
            stall_counts[str(candidate.get("stall_type") or "none")] += 1
            edge_type_counts[str(candidate.get("edge_type") or "unknown")] += 1
            sampling_priorities.append(float(candidate.get("sampling_priority") or 0.0))
            balanced_scores.append(float(candidate.get("balanced_operator_score") or 0.0))

        if _topk_hit(row, 1):
            top1_hits += 1
        if _topk_hit(row, top_k):
            topk_hits += 1
        rank = _first_positive_rank(row)
        if rank is not None:
            rank_sum += rank
            rank_count += 1

        row_sources = [str(s or "unknown") for s in provenance.get("trace_sources") or ["unknown"]]
        row_authorities = [str(a or "unknown") for a in provenance.get("authority_stages") or ["unknown"]]
        top1 = _topk_hit(row, 1)
        for source in row_sources:
            source_top1[source]["rows"] += 1
            source_top1[source]["top1_hits"] += int(top1)
        for authority in row_authorities:
            authority_top1[authority]["rows"] += 1
            authority_top1[authority]["top1_hits"] += int(top1)

    row_count = len(rows)
    return {
        "schema": SCHEMA,
        "rows": row_count,
        "mixed_rows": mixed_rows,
        "positive_rows": positive_rows,
        "failure_only_rows": failure_only_rows,
        "stall_rows": stall_rows,
        "splits": dict(sorted(split_counts.items())),
        "trace_sources": dict(sorted(source_counts.items())),
        "authority_stages": dict(sorted(authority_counts.items())),
        "candidate_is_positive": dict(sorted(candidate_positive.items())),
        "stall_types": dict(sorted(stall_counts.items())),
        "edge_types": dict(sorted(edge_type_counts.items())),
        "candidate_count_histogram": dict(sorted(candidate_count_hist.items(), key=lambda kv: int(kv[0]) if kv[0].isdigit() else 999999)),
        "hodge_harmonic_signal_buckets": dict(sorted(harmonic_buckets.items())),
        "sampling_priority": _summary_float(sampling_priorities),
        "balanced_operator_score": _summary_float(balanced_scores),
        "operator_score_baseline": {
            "top1_progress_rate": _rate(top1_hits, row_count),
            f"top{top_k}_progress_rate": _rate(topk_hits, row_count),
            "mean_first_positive_rank": (rank_sum / rank_count) if rank_count else None,
            "positive_ranked_rows": rank_count,
        },
        "by_source_top1": _rate_table(source_top1),
        "by_authority_top1": _rate_table(authority_top1),
        "recommendations": _recommendations(
            rows=row_count,
            mixed_rows=mixed_rows,
            stall_counts=stall_counts,
            top1_rate=_rate(top1_hits, row_count),
        ),
    }


def _bucket(value: float) -> str:
    if value < 0.1:
        return "[0.0,0.1)"
    if value < 0.25:
        return "[0.1,0.25)"
    if value < 0.5:
        return "[0.25,0.5)"
    if value < 0.75:
        return "[0.5,0.75)"
    return "[0.75,1.0]"


def _rate(num: int, den: int) -> float:
    return round(num / den, 6) if den else 0.0


def _summary_float(values: list[float]) -> dict[str, float | int | None]:
    if not values:
        return {"count": 0, "min": None, "max": None, "mean": None}
    return {
        "count": len(values),
        "min": round(min(values), 6),
        "max": round(max(values), 6),
        "mean": round(sum(values) / len(values), 6),
    }


def _rate_table(table: dict[str, Counter[str]]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for key, counts in sorted(table.items()):
        rows = int(counts.get("rows", 0))
        hits = int(counts.get("top1_hits", 0))
        out[key] = {"rows": rows, "top1_hits": hits, "top1_progress_rate": _rate(hits, rows)}
    return out


def _recommendations(*, rows: int, mixed_rows: int, stall_counts: Counter[str], top1_rate: float) -> list[str]:
    recs: list[str] = []
    if rows == 0:
        return ["No ranking rows found. Build reports/training/tactic_path_ranking.jsonl first."]
    if mixed_rows < max(10, rows // 10):
        recs.append("Increase same-goal success/failure pairing; reranker training benefits most from mixed decision points.")
    dominant_stalls = [(k, v) for k, v in stall_counts.most_common() if k != "none" and v > 0]
    if dominant_stalls:
        top_stall, _count = dominant_stalls[0]
        recs.append(f"Dominant stall family is {top_stall}; prioritize targeted failure-fossil mining for that class.")
    if top1_rate > 0.8:
        recs.append("Operator-score baseline is already strong; use held-out evaluation to avoid overfitting a reranker.")
    elif top1_rate < 0.4:
        recs.append("Operator-score baseline is weak; train a reranker and compare against this top-1 baseline.")
    else:
        recs.append("Operator-score baseline is moderate; a small reranker is a good next experiment.")
    return recs


def run_analysis(input_path: Path, output_path: Path, *, top_k: int) -> dict[str, Any]:
    rows = [row for row in iter_jsonl(input_path) if row.get("schema") == "info_geometry.tactic_path_ranking.v1"]
    report = analyze_rows(rows, top_k=top_k)
    report["input"] = str(input_path)
    report["output"] = str(output_path)
    report["top_k"] = top_k
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--top-k", type=int, default=3)
    args = parser.parse_args()
    report = run_analysis(args.input, args.out, top_k=max(1, args.top_k))
    print(json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
