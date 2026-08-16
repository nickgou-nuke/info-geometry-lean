#!/usr/bin/env python3
"""Analyze bottlenecks in tactic path ranking telemetry.

Reads info_geometry.tactic_path_ranking.v1 JSONL plus optional summary JSON and
emits a compact report for stall/failure concentration analysis.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

SCHEMA = "info_geometry.tactic_path_ranking.analysis.v1"
DEFAULT_DATASET = Path("reports/training/tactic_path_ranking.jsonl")
DEFAULT_STATS = Path("reports/training/tactic_path_ranking.stats.json")
DEFAULT_OUT = Path("reports/training/tactic_path_ranking.analysis.json")


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def cone_bucket(depth: int) -> str:
    if depth <= 0:
        return "0"
    if depth <= 2:
        return "1-2"
    if depth <= 5:
        return "3-5"
    if depth <= 10:
        return "6-10"
    return "11+"


def ratio(n: int, d: int) -> float:
    return round((float(n) / float(d)) if d else 0.0, 4)


def run_analysis(dataset_path: Path, stats_path: Path | None, out_path: Path, top_k: int = 10) -> dict[str, Any]:
    rows = [r for r in iter_jsonl(dataset_path) if r.get("schema") == "info_geometry.tactic_path_ranking.v1"]

    totals = Counter()
    stall_types = Counter()
    by_theorem = defaultdict(lambda: Counter())
    by_split = defaultdict(lambda: Counter())
    by_cone_bucket = defaultdict(lambda: Counter())

    for row in rows:
        theorem = str((row.get("context") or {}).get("theorem") or "")
        split = str(row.get("split") or "unknown")
        gf = row.get("graph_features") or {}
        bucket = cone_bucket(int(gf.get("cone_depth") or 0))

        candidates = row.get("candidates") or []
        totals["decision_points"] += 1

        local = Counter()
        for c in candidates:
            st = str(c.get("stall_type") or "none")
            lbl = int(c.get("label") or 0)
            if st != "none":
                local["stall"] += 1
                stall_types[st] += 1
            if lbl == 1:
                local["positive"] += 1
            elif lbl == 0:
                local["negative"] += 1
            elif lbl == -1:
                local["stall_label"] += 1
        local["candidates"] = len(candidates)

        for k, v in local.items():
            totals[k] += v
            by_theorem[theorem][k] += v
            by_split[split][k] += v
            by_cone_bucket[bucket][k] += v

    def pack(counter: Counter) -> dict[str, Any]:
        cands = int(counter.get("candidates", 0))
        return {
            "candidates": cands,
            "positive": int(counter.get("positive", 0)),
            "negative": int(counter.get("negative", 0)),
            "stall": int(counter.get("stall", 0)),
            "stall_label": int(counter.get("stall_label", 0)),
            "stall_ratio": ratio(int(counter.get("stall", 0)), cands),
            "positive_ratio": ratio(int(counter.get("positive", 0)), cands),
            "negative_ratio": ratio(int(counter.get("negative", 0)), cands),
        }

    theorem_rank = []
    for theorem, c in by_theorem.items():
        p = pack(c)
        p["theorem"] = theorem
        theorem_rank.append(p)
    theorem_rank.sort(key=lambda x: (-x["stall_ratio"], -x["stall"], x["theorem"]))

    split_summary = {k: pack(v) for k, v in sorted(by_split.items())}
    cone_summary = {k: pack(v) for k, v in sorted(by_cone_bucket.items())}

    source_stats = None
    if stats_path and stats_path.exists():
        try:
            source_stats = json.loads(stats_path.read_text(encoding="utf-8"))
        except Exception:
            source_stats = None

    out = {
        "schema": SCHEMA,
        "inputs": {
            "dataset": str(dataset_path),
            "stats": str(stats_path) if stats_path else None,
        },
        "totals": {
            "decision_points": int(totals.get("decision_points", 0)),
            **pack(totals),
        },
        "stall_types": dict(sorted(stall_types.items(), key=lambda kv: (-kv[1], kv[0]))),
        "top_theorems_by_stall_ratio": theorem_rank[: max(1, top_k)],
        "by_split": split_summary,
        "by_cone_depth_bucket": cone_summary,
        "source_stats": source_stats,
        "authority_boundary": {
            "analysis_only": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    parser.add_argument("--stats", type=Path, default=DEFAULT_STATS)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--top-k", type=int, default=10)
    args = parser.parse_args()

    result = run_analysis(args.dataset, args.stats, args.out, top_k=max(1, args.top_k))
    print(json.dumps(result["totals"], indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
