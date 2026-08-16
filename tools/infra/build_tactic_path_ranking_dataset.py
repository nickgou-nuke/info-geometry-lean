#!/usr/bin/env python3
"""Build operator-informed tactic path ranking rows from tactic telemetry.

This is the first Spectral-Journey-style dataset seam for Hive: instead of
training only "next tactic" SFT rows, it groups success/failure candidates at a
shared decision point and emits a candidate ranking packet.

The operator features are diagnostic priors, not proof authority.  Labels come
from previously verified/success/failure telemetry; Lean remains the authority
for any newly generated proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable

try:
    from tools.infra.aesop_tactic_prior import classify_tactic
except Exception:  # pragma: no cover - CLI fallback outside repo import path.
    def classify_tactic(tactic: str) -> dict[str, Any]:
        return {"family": str(tactic or "").split()[0] if str(tactic or "").split() else "", "phase": "unknown"}

from igf.common.json_io import iter_jsonl, write_jsonl
from igf.common.hashing import stable_hash


SCHEMA = "info_geometry.tactic_path_ranking.v1"
SUMMARY_SCHEMA = "info_geometry.tactic_path_ranking.summary.v1"
DEFAULT_SFT = Path("reports/training/tactic_sft.jsonl")
DEFAULT_FAILURES = Path("reports/training/tactic_failures.jsonl")
DEFAULT_OUT = Path("reports/training/tactic_path_ranking.jsonl")
DEFAULT_STATS = Path("reports/training/tactic_path_ranking.stats.json")
STALL_KINDS = {"stall", "loop", "cycle", "no_progress", "repeated", "timeout"}


def split_for(key: str, *, train_ratio: float, val_ratio: float, seed: int) -> str:
    digest = hashlib.sha256(f"{seed}|{key}".encode("utf-8")).hexdigest()
    x = int(digest[:15], 16) / float(16**15 - 1)
    if x < train_ratio:
        return "train"
    if x < train_ratio + val_ratio:
        return "val"
    return "test"


def normalize_goal(text: Any) -> str:
    if text is None:
        return ""
    return re.sub(r"\s+", " ", str(text)).strip()


def decision_key(row: dict[str, Any]) -> tuple[str, str]:
    theorem = str(row.get("theorem") or "")
    goal_hash = str(row.get("goal_hash") or stable_hash(normalize_goal(row.get("goal_before"))))
    return theorem, goal_hash


def tactic_family(tactic: str) -> str:
    words = str(tactic or "").strip().split()
    return words[0] if words else ""


def edge_type_for(tactic: str, *, success: bool, goal_after: str = "", failure_kind: str = "") -> str:
    family = tactic_family(tactic)
    if success and normalize_goal(goal_after).lower() in {"no goals", "no goals."}:
        return "terminal"
    if family in {"constructor", "cases", "induction", "rcases", "constructor;"}:
        return "branching"
    if family in {"simp", "simpa", "rw", "rwa", "norm_num", "ring", "linarith", "omega", "aesop"}:
        return "simplification"
    if any(kind in failure_kind.lower() for kind in STALL_KINDS):
        return "stall"
    if family in {"apply", "exact", "refine", "use", "exists"}:
        return "directed"
    return "other"


def failure_label(failure_kind: str, diagnostic: str) -> int:
    return 0


def stall_type_for(failure_kind: str = "", diagnostic: str = "") -> str:
    text = f"{failure_kind}\n{diagnostic}".lower()
    if "timeout" in text:
        return "timeout"
    if "type mismatch" in text or "type_mismatch" in text or "failed to synthesize" in text:
        return "type_mismatch"
    if "syntax" in text or "unexpected token" in text or "parser" in text:
        return "syntax_error"
    if "unsolved" in text:
        return "unsolved_goals"
    if any(kind in text for kind in STALL_KINDS):
        return "harmonic_stall"
    return "failure" if text.strip() else "none"


def operator_score(*, label: int, edge_type: str, tactic: str, diagnostic: str = "") -> float:
    base = 0.5
    if label == 1:
        base = 0.86
    elif label == -1:
        base = 0.08
    else:
        base = 0.22
    if edge_type == "terminal":
        base += 0.1
    elif edge_type == "simplification":
        base += 0.04
    elif edge_type == "stall":
        base -= 0.08
    if "timeout" in diagnostic.lower():
        base -= 0.04
    return max(0.0, min(1.0, round(base, 4)))


def count_local_hypotheses(goal: str) -> int:
    text = str(goal or "")
    if "⊢" not in text:
        return 0
    prefix = text.split("⊢", 1)[0]
    return sum(1 for chunk in re.split(r"\s{2,}|\n|;", prefix) if ":" in chunk)


def quantifier_depth(goal: str) -> int:
    text = str(goal or "")
    return len(re.findall(r"\bforall\b|∀|\bexists\b|∃", text))


def token_count(text: str) -> int:
    return len(re.findall(r"[A-Za-z0-9_'.]+|[∀∃⊢→↔=<>≤≥]+", str(text or "")))


def hodge_harmonic_signal(candidates: list[dict[str, Any]]) -> float:
    if not candidates:
        return 0.0
    stalled = sum(
        1
        for item in candidates
        if item.get("stall_type") not in {None, "", "none"} or item.get("edge_type") == "stall"
    )
    repeated_families = 0
    families = Counter(tactic_family(str(item.get("tactic") or "")) for item in candidates)
    for _family, count in families.items():
        if count > 1:
            repeated_families += count - 1
    signal = (stalled + 0.5 * repeated_families) / max(len(candidates), 1)
    return round(max(0.0, min(1.0, signal)), 4)


def chiral_flow_direction(candidates: list[dict[str, Any]]) -> int:
    positives = sum(1 for item in candidates if item.get("is_positive") == 1)
    stalls = sum(1 for item in candidates if item.get("stall_type") not in {None, "", "none"})
    if positives > stalls:
        return 1
    if stalls > positives:
        return -1
    return 0


def _empty_frequency_stats() -> dict[str, dict[str, int]]:
    return {
        "trial": Counter(),
        "failure": Counter(),
        "stall": Counter(),
        "success": Counter(),
    }


def build_frequency_stats(
    sft_rows: list[dict[str, Any]],
    failure_rows: list[dict[str, Any]],
) -> dict[str, dict[str, int]]:
    stats = _empty_frequency_stats()
    for row in sft_rows:
        family = tactic_family(str(row.get("tactic") or ""))
        if not family:
            continue
        stats["trial"][family] += 1
        stats["success"][family] += 1
    for row in failure_rows:
        family = tactic_family(str(row.get("failed_tactic") or ""))
        if not family:
            continue
        stats["trial"][family] += 1
        stats["failure"][family] += 1
        stall_type = stall_type_for(str(row.get("failure_kind") or ""), str(row.get("diagnostic") or ""))
        if stall_type not in {"none", "failure"}:
            stats["stall"][family] += 1
    return stats


def add_entropic_weights(candidate: dict[str, Any], frequency_stats: dict[str, dict[str, int]]) -> dict[str, Any]:
    family = tactic_family(str(candidate.get("tactic") or ""))
    trial_count = int(frequency_stats["trial"].get(family, 0))
    failure_count = int(frequency_stats["failure"].get(family, 0))
    stall_count = int(frequency_stats["stall"].get(family, 0))
    success_count = int(frequency_stats["success"].get(family, 0))
    denom = max(trial_count, 1)
    failure_rate = failure_count / denom
    stall_rate = stall_count / denom
    inverse_trial_frequency = 1.0 / math.sqrt(denom)
    entropy_flattening_weight = inverse_trial_frequency * (1.0 + 0.5 * stall_rate)
    entropic_bias = math.log1p(trial_count) * (failure_rate + 0.5 * stall_rate)
    operator_score_value = float(candidate.get("operator_score") or 0.0)
    balanced_operator_score = max(0.0, min(1.0, operator_score_value - 0.08 * entropic_bias))
    if int(candidate.get("is_positive") or 0) == 1:
        sampling_priority = entropy_flattening_weight * (1.0 + 0.25 * (1.0 - failure_rate))
    else:
        sampling_priority = entropy_flattening_weight * (1.0 + failure_rate + 0.5 * stall_rate)
    enriched = dict(candidate)
    enriched["entropic_weights"] = {
        "tactic_family": family,
        "trial_count": trial_count,
        "success_count": success_count,
        "failure_count": failure_count,
        "stall_count": stall_count,
        "failure_rate": round(failure_rate, 6),
        "stall_rate": round(stall_rate, 6),
        "inverse_trial_frequency": round(inverse_trial_frequency, 6),
        "entropy_flattening_weight": round(entropy_flattening_weight, 6),
        "entropic_bias": round(entropic_bias, 6),
        "balanced_operator_score": round(balanced_operator_score, 6),
        "sampling_priority": round(sampling_priority, 6),
        "diagnostic_prior_only": True,
    }
    enriched["sampling_priority"] = round(sampling_priority, 6)
    enriched["balanced_operator_score"] = round(balanced_operator_score, 6)
    return enriched


def success_candidate(row: dict[str, Any]) -> dict[str, Any]:
    tactic = str(row.get("tactic") or "")
    goal_after = str(row.get("goal_after") or "")
    goal_hash_before = str(row.get("goal_hash") or stable_hash(normalize_goal(row.get("goal_before"))))
    goal_hash_after = stable_hash(normalize_goal(goal_after))
    edge_type = edge_type_for(tactic, success=True, goal_after=goal_after)
    edge_id = stable_hash(
        {
            "trace_source": row.get("source"),
            "goal_hash_before": goal_hash_before,
            "goal_hash_after": goal_hash_after,
            "tactic": tactic,
            "raw_ref": row.get("raw_ref") or {},
        }
    )
    return {
        "edge_id": edge_id,
        "goal_hash_before": goal_hash_before,
        "goal_hash_after": goal_hash_after,
        "tactic": tactic,
        "edge_type": edge_type,
        "operator_score": operator_score(label=1, edge_type=edge_type, tactic=tactic),
        "is_positive": 1,
        "label": 1,
        "stall_type": "none",
        "trace_source": row.get("source"),
        "authority_stage": row.get("authority_stage") or "lean_checked",
        "source": row.get("source"),
        "goal_after": goal_after,
        "aesop_tactic_prior": row.get("aesop_tactic_prior") or classify_tactic(tactic),
        "raw_ref": row.get("raw_ref") or {},
    }


def failure_candidate(row: dict[str, Any]) -> dict[str, Any]:
    tactic = str(row.get("failed_tactic") or "")
    failure_kind = str(row.get("failure_kind") or "failure")
    diagnostic = str(row.get("diagnostic") or "")
    goal_hash_before = str(row.get("goal_hash") or stable_hash(normalize_goal(row.get("goal_before"))))
    goal_hash_after = ""
    label = failure_label(failure_kind, diagnostic)
    edge_type = edge_type_for(tactic, success=False, failure_kind=failure_kind)
    stall_type = stall_type_for(failure_kind, diagnostic)
    edge_id = stable_hash(
        {
            "trace_source": row.get("source"),
            "goal_hash_before": goal_hash_before,
            "goal_hash_after": goal_hash_after,
            "tactic": tactic,
            "failure_kind": failure_kind,
            "raw_ref": row.get("raw_ref") or {},
        }
    )
    return {
        "edge_id": edge_id,
        "goal_hash_before": goal_hash_before,
        "goal_hash_after": goal_hash_after,
        "tactic": tactic,
        "edge_type": edge_type,
        "operator_score": operator_score(label=label, edge_type=edge_type, tactic=tactic, diagnostic=diagnostic),
        "is_positive": 0,
        "label": 0,
        "stall_type": stall_type,
        "trace_source": row.get("source"),
        "authority_stage": row.get("authority_stage") or "lean_checked",
        "source": row.get("source"),
        "diagnostic": diagnostic,
        "failure_kind": failure_kind,
        "aesop_tactic_prior": row.get("aesop_tactic_prior") or classify_tactic(tactic),
        "raw_ref": row.get("raw_ref") or {},
    }


def build_rows(
    sft_rows: list[dict[str, Any]],
    failure_rows: list[dict[str, Any]],
    *,
    min_candidates: int,
    seed: int,
    train_ratio: float,
    val_ratio: float,
) -> list[dict[str, Any]]:
    success_by_key: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    failure_by_key: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    exemplar_by_key: dict[tuple[str, str], dict[str, Any]] = {}

    for row in sft_rows:
        key = decision_key(row)
        success_by_key[key].append(row)
        exemplar_by_key.setdefault(key, row)
    for row in failure_rows:
        key = decision_key(row)
        failure_by_key[key].append(row)
        exemplar_by_key.setdefault(key, row)

    frequency_stats = build_frequency_stats(sft_rows, failure_rows)
    out: list[dict[str, Any]] = []
    for key in sorted(set(success_by_key) | set(failure_by_key)):
        exemplar = exemplar_by_key[key]
        candidates = [success_candidate(row) for row in success_by_key.get(key, [])]
        candidates.extend(failure_candidate(row) for row in failure_by_key.get(key, []))
        candidates = [add_entropic_weights(candidate, frequency_stats) for candidate in candidates]
        if len(candidates) < min_candidates:
            continue
        candidates.sort(key=lambda item: (-int(item["is_positive"] == 1), -float(item["balanced_operator_score"]), str(item["tactic"])))
        goal = normalize_goal(exemplar.get("goal_before"))
        deps = []
        context = exemplar.get("context")
        if isinstance(context, dict):
            deps = [str(dep) for dep in context.get("dependencies") or []]
        positives = sum(1 for item in candidates if item["is_positive"] == 1)
        negatives = sum(1 for item in candidates if item["is_positive"] == 0)
        stalls = sum(1 for item in candidates if item.get("stall_type") not in {None, "", "none"})
        trace_sources = sorted({str(item.get("trace_source") or "") for item in candidates if item.get("trace_source")})
        authority_stages = sorted({str(item.get("authority_stage") or "") for item in candidates if item.get("authority_stage")})
        split = str(exemplar.get("split") or "") or split_for(
            f"{key[0]}|{key[1]}",
            train_ratio=train_ratio,
            val_ratio=val_ratio,
            seed=seed,
        )
        row = {
            "schema": SCHEMA,
            "id": "",
            "split": split,
            "context": {
                "theorem": exemplar.get("theorem") or key[0],
                "lean_file": exemplar.get("lean_file") or "",
                "theorem_statement": exemplar.get("theorem_statement") or "",
                "goal_state": goal,
                "local_hypotheses": _local_hypotheses(goal),
                "imports_fingerprint": stable_hash(deps),
                "dependencies": deps,
            },
            "graph_features": {
                "node_id": key[1],
                "goal_hash": key[1],
                "cone_depth": len(deps),
                "scc_level": None,
                "l0_hypothesis_count": count_local_hypotheses(goal),
                "goal_token_count": token_count(goal),
                "quantifier_depth": quantifier_depth(goal),
                "candidate_count": len(candidates),
                "positive_count": positives,
                "negative_count": negatives,
                "stall_count": stalls,
                "hodge_harmonic_signal": hodge_harmonic_signal(candidates),
                "chiral_flow_direction": chiral_flow_direction(candidates),
                "operator_features_are_diagnostic": True,
                "entropic_weights_are_diagnostic": True,
            },
            "provenance": {
                "trace_sources": trace_sources,
                "authority_stages": authority_stages,
                "ranking_dataset_stage": "telemetry_derived",
            },
            "candidates": candidates,
            "failure_fossils": [
                {
                    "tactic": item.get("tactic"),
                    "failure_kind": item.get("failure_kind"),
                    "diagnostic": item.get("diagnostic"),
                    "source": item.get("source"),
                }
                for item in candidates
                if item.get("is_positive") == 0
            ],
            "authority": {
                "ranking_prior_only": True,
                "not_a_proof": True,
                "lean_remains_proof_authority": True,
            },
        }
        row["id"] = stable_hash({"schema": SCHEMA, "theorem": key[0], "goal_hash": key[1], "candidates": [c["tactic"] for c in candidates]})
        out.append(row)
    return out


def _local_hypotheses(goal: str) -> list[str]:
    text = str(goal or "")
    if "⊢" not in text:
        return []
    prefix = text.split("⊢", 1)[0]
    return [chunk.strip() for chunk in re.split(r"\n|;", prefix) if ":" in chunk]


def run_builder(
    *,
    sft_path: Path,
    failures_path: Path,
    out_path: Path,
    stats_path: Path,
    min_candidates: int,
    seed: int = 1729,
    train_ratio: float = 0.85,
    val_ratio: float = 0.075,
) -> dict[str, Any]:
    sft_rows = [row for row in iter_jsonl(sft_path) if row.get("schema") == "info_geometry.tactic_sft.v1"]
    failure_rows = [row for row in iter_jsonl(failures_path) if row.get("schema") == "info_geometry.tactic_failure.v1"]
    rows = build_rows(
        sft_rows,
        failure_rows,
        min_candidates=min_candidates,
        seed=seed,
        train_ratio=train_ratio,
        val_ratio=val_ratio,
    )
    count = write_jsonl(out_path, rows)
    candidate_labels = Counter()
    candidate_positive = Counter()
    stall_types = Counter()
    splits = Counter()
    sampling_priorities: list[float] = []
    balanced_scores: list[float] = []
    for row in rows:
        splits[str(row.get("split") or "unknown")] += 1
        for candidate in row["candidates"]:
            candidate_labels[str(candidate["label"])] += 1
            candidate_positive[str(candidate["is_positive"])] += 1
            stall_types[str(candidate.get("stall_type") or "none")] += 1
            sampling_priorities.append(float(candidate.get("sampling_priority") or 0.0))
            balanced_scores.append(float(candidate.get("balanced_operator_score") or 0.0))
    stats = {
        "schema": SUMMARY_SCHEMA,
        "inputs": {
            "sft": str(sft_path),
            "failures": str(failures_path),
        },
        "output": str(out_path),
        "rows": count,
        "input_success_rows": len(sft_rows),
        "input_failure_rows": len(failure_rows),
        "candidate_labels": dict(sorted(candidate_labels.items())),
        "candidate_is_positive": dict(sorted(candidate_positive.items())),
        "stall_types": dict(sorted(stall_types.items())),
        "splits": dict(sorted(splits.items())),
        "sampling_priority": _summary_float(sampling_priorities),
        "balanced_operator_score": _summary_float(balanced_scores),
        "min_candidates": min_candidates,
        "seed": seed,
        "train_ratio": train_ratio,
        "val_ratio": val_ratio,
    }
    stats_path.parent.mkdir(parents=True, exist_ok=True)
    stats_path.write_text(json.dumps(stats, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return stats


def _summary_float(values: list[float]) -> dict[str, float | int | None]:
    if not values:
        return {"count": 0, "min": None, "max": None, "mean": None}
    return {
        "count": len(values),
        "min": round(min(values), 6),
        "max": round(max(values), 6),
        "mean": round(sum(values) / len(values), 6),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sft", type=Path, default=DEFAULT_SFT)
    parser.add_argument("--failures", type=Path, default=DEFAULT_FAILURES)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--stats-out", type=Path, default=DEFAULT_STATS)
    parser.add_argument("--min-candidates", type=int, default=2)
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--train-ratio", type=float, default=0.85)
    parser.add_argument("--val-ratio", type=float, default=0.075)
    args = parser.parse_args()
    stats = run_builder(
        sft_path=args.sft,
        failures_path=args.failures,
        out_path=args.out,
        stats_path=args.stats_out,
        min_candidates=max(1, args.min_candidates),
        seed=args.seed,
        train_ratio=args.train_ratio,
        val_ratio=args.val_ratio,
    )
    print(json.dumps(stats, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
