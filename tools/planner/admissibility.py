"""Strict admissibility precheck scaffold logic."""

from __future__ import annotations

from typing import Any, cast

from .common import (
    JsonObj,
    RankedEntry,
    THEOREM_LIKE_KINDS,
    clamp01,
    jaccard_overlap,
    keys_from_counts,
)


def _admissibility_overlap(
    candidate_decl: str,
    replacement_decl: str,
    bridge_decl_signals: dict[str, JsonObj],
) -> float | None:
    cand_profile = bridge_decl_signals.get(candidate_decl)
    repl_profile = bridge_decl_signals.get(replacement_decl)
    if not isinstance(cand_profile, dict) or not isinstance(repl_profile, dict):
        return None

    cand_clusters = keys_from_counts(cand_profile.get("clusterKeys"))
    repl_clusters = keys_from_counts(repl_profile.get("clusterKeys"))
    cand_heads = keys_from_counts(cand_profile.get("semanticHeadCounts"))
    repl_heads = keys_from_counts(repl_profile.get("semanticHeadCounts"))
    cand_fps = keys_from_counts(cand_profile.get("fingerprintCounts"))
    repl_fps = keys_from_counts(repl_profile.get("fingerprintCounts"))

    if not (cand_clusters or cand_heads or cand_fps):
        return None
    if not (repl_clusters or repl_heads or repl_fps):
        return None

    cluster_overlap = jaccard_overlap(cand_clusters, repl_clusters)
    head_overlap = jaccard_overlap(cand_heads, repl_heads)
    fp_overlap = jaccard_overlap(cand_fps, repl_fps)
    return clamp01(0.5 * cluster_overlap + 0.3 * head_overlap + 0.2 * fp_overlap)


def rank_admissibility_prechecks(
    declaration_plans: list[JsonObj],
    decls: dict[str, JsonObj],
    bridge_decl_signals: dict[str, JsonObj],
    top_k: int,
) -> list[JsonObj]:
    ranked: list[RankedEntry] = []

    for plan in declaration_plans:
        candidate = plan.get("candidate")
        if not isinstance(candidate, str) or not candidate:
            continue

        corridor_any = plan.get("probable_replacement_corridor")
        corridor = cast(list[Any], corridor_any) if isinstance(corridor_any, list) else []
        first_repl_any = corridor[0] if corridor and isinstance(corridor[0], dict) else {}
        first_repl = cast(JsonObj, first_repl_any)
        replacement_decl_any = first_repl.get("replacementDecl")
        replacement_decl = replacement_decl_any if isinstance(replacement_decl_any, str) else None

        checks: list[JsonObj] = []
        hard_failures: list[str] = []
        soft_warnings: list[str] = []

        candidate_meta = decls.get(candidate)
        replacement_meta = decls.get(replacement_decl) if isinstance(replacement_decl, str) else None

        candidate_exists = isinstance(candidate_meta, dict)
        checks.append(
            {
                "check": "candidate.exists",
                "severity": "hard",
                "passed": candidate_exists,
                "evidence": f"candidate={candidate}",
            }
        )
        if not candidate_exists:
            hard_failures.append("candidate declaration metadata missing")

        replacement_exists = isinstance(replacement_meta, dict)
        checks.append(
            {
                "check": "replacement.exists",
                "severity": "hard",
                "passed": replacement_exists,
                "evidence": f"replacement={replacement_decl}",
            }
        )
        if not replacement_exists:
            hard_failures.append("replacement declaration metadata missing")

        candidate_kind = str(candidate_meta.get("kind")) if isinstance(candidate_meta, dict) else "unknown"
        replacement_kind = str(replacement_meta.get("kind")) if isinstance(replacement_meta, dict) else "unknown"
        kind_ok = candidate_kind in THEOREM_LIKE_KINDS and replacement_kind in THEOREM_LIKE_KINDS
        checks.append(
            {
                "check": "kind.theorem-like-compatible",
                "severity": "hard",
                "passed": kind_ok,
                "evidence": f"candidateKind={candidate_kind}, replacementKind={replacement_kind}",
            }
        )
        if not kind_ok:
            hard_failures.append("replacement is not theorem-like")

        candidate_region_any = plan.get("candidateRegion")
        candidate_region = candidate_region_any if isinstance(candidate_region_any, str) else "unknown"
        replacement_region_any = first_repl.get("region")
        replacement_region = replacement_region_any if isinstance(replacement_region_any, str) else "unknown"
        region_ok = candidate_region == "unknown" or replacement_region == "unknown" or candidate_region == replacement_region
        checks.append(
            {
                "check": "region.compatible",
                "severity": "soft",
                "passed": region_ok,
                "evidence": f"candidateRegion={candidate_region}, replacementRegion={replacement_region}",
            }
        )
        if not region_ok:
            soft_warnings.append("candidate and replacement are in different regions")

        overlap = None
        if isinstance(replacement_decl, str):
            overlap = _admissibility_overlap(candidate, replacement_decl, bridge_decl_signals)

        overlap_ok = overlap is not None and overlap >= 0.05
        checks.append(
            {
                "check": "bridge.shape-overlap",
                "severity": "soft",
                "passed": overlap_ok,
                "evidence": f"shapeOverlap={overlap:.4f}" if isinstance(overlap, float) else "shapeOverlap unavailable",
            }
        )
        if overlap is None:
            soft_warnings.append("bridge declaration shape overlap is unavailable")
        elif overlap < 0.05:
            soft_warnings.append("bridge declaration shape overlap is weak")

        plan_score = clamp01(float(plan.get("score", 0.0)))
        plan_conf = clamp01(float(plan.get("confidence", 0.0)))

        if hard_failures:
            status = "blocked"
            score = clamp01(0.20 * plan_score)
            confidence = clamp01(0.35 * plan_conf)
        elif soft_warnings:
            status = "needs-review"
            score = clamp01(0.55 * plan_score + 0.15 * (overlap if isinstance(overlap, float) else 0.0))
            confidence = clamp01(0.70 * plan_conf)
        else:
            status = "provisionally-admissible"
            overlap_for_score = overlap if isinstance(overlap, float) else 0.5
            score = clamp01(0.70 * plan_score + 0.20 * overlap_for_score + 0.10)
            confidence = clamp01(0.85 * plan_conf + 0.10)

        payload: JsonObj = {
            "candidate": candidate,
            "candidateFile": plan.get("candidateFile"),
            "replacementDecl": replacement_decl,
            "replacementRegion": replacement_region,
            "declarationPlanRank": plan.get("rank"),
            "precheckStatus": status,
            "shapeOverlap": round(overlap, 4) if isinstance(overlap, float) else None,
            "hardFailures": hard_failures,
            "softWarnings": soft_warnings,
            "admissibilityChecks": checks,
            "score": round(score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": [
                {
                    "signal": "precheck.plan-prior",
                    "contribution": round(0.70 * plan_score, 4),
                    "reliability": max(0.4, plan_conf),
                    "evidence": f"declaration-plan score={plan_score:.4f}",
                },
                {
                    "signal": "precheck.shape-overlap",
                    "contribution": round(0.20 * (overlap if isinstance(overlap, float) else 0.0), 4),
                    "reliability": 0.78,
                    "evidence": f"shape overlap={overlap:.4f}" if isinstance(overlap, float) else "shape overlap unavailable",
                },
                {
                    "signal": "precheck.status",
                    "contribution": 0.1 if status == "provisionally-admissible" else 0.0,
                    "reliability": 0.74,
                    "evidence": status,
                },
            ],
        }
        ranked.append(
            RankedEntry(
                key=f"{candidate}->{replacement_decl or 'none'}",
                score=score,
                confidence=confidence,
                payload=payload,
            )
        )

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out
