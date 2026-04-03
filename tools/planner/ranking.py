"""Ranking logic for vacuity, owner, replacement, corridor, and declaration plans."""

from __future__ import annotations

from collections import Counter, defaultdict
from typing import Any, cast

if __package__ in (None, "", "planner"):
    from pathing import repo_root
else:
    from tools.pathing import repo_root

from .common import (
    JsonObj,
    REPLACEMENT_CLUSTER_PARTICIPATION_LIMIT,
    RankedEntry,
    Signal,
    VACUITY_TAGS,
    VIOLATION_LEVEL_WEIGHT,
    clamp01,
    file_domain,
    first_count_key,
    jaccard_overlap,
    keys_from_counts,
    make_cluster_key,
    parse_uri_or_path,
    safe_mean,
    summarize_signals,
    top_count_keys,
)


def _cluster_rank_weight(cluster_rank: int) -> float:
    if cluster_rank <= 0:
        return 1.0
    return 1.0 / float(cluster_rank)


def rank_vacuity_candidates(
    theorem_entries: list[JsonObj],
    module_region: dict[str, str],
    file_region: dict[str, str],
    hole_counts: dict[str, int],
    bridge_file_signals: dict[str, JsonObj],
    bridge_decl_signals: dict[str, JsonObj],
    top_k: int,
) -> list[JsonObj]:
    ranked: list[RankedEntry] = []

    for row in theorem_entries:
        if row.get("kind") != "theorem":
            continue
        tags = set(row.get("tags") or [])
        raw_violations = row.get("violations")
        violations = raw_violations if isinstance(raw_violations, list) else []
        if not (tags & VACUITY_TAGS or violations):
            continue

        name = str(row.get("name") or "")
        if not name:
            continue

        file_path = row.get("file") if isinstance(row.get("file"), str) else None
        module = row.get("module") if isinstance(row.get("module"), str) else None
        if module:
            region = module_region.get(module, file_region.get(file_path or "", "unknown"))
        else:
            region = file_region.get(file_path or "", "unknown")

        signals: list[Signal] = []

        if "wrapper-candidate" in tags:
            signals.append(Signal("tag.wrapper-candidate", 0.34, 0.82, "wrapper-candidate"))
        if "dead-candidate" in tags:
            signals.append(Signal("tag.dead-candidate", 0.28, 0.84, "dead-candidate"))
        if "rfl-like" in tags:
            signals.append(Signal("tag.rfl-like", 0.18, 0.74, "rfl-like"))
        if "proof-infrastructure" in tags:
            signals.append(Signal("tag.proof-infrastructure", 0.10, 0.72, "proof-infrastructure"))

        levels: list[str] = []
        for violation_any in violations:
            if isinstance(violation_any, dict):
                violation = cast(JsonObj, violation_any)
                level = violation.get("level")
                if isinstance(level, str):
                    levels.append(level)
        if "error" in levels:
            signals.append(Signal("violation.error", 0.20, VIOLATION_LEVEL_WEIGHT["error"], "error-level violation present"))
        elif "warning" in levels:
            signals.append(
                Signal("violation.warning", 0.12, VIOLATION_LEVEL_WEIGHT["warning"], "warning-level violation present")
            )

        if int(row.get("reverse_type", 0)) == 0:
            signals.append(Signal("graph.zero-reverse-type", 0.06, 0.70, "reverse_type = 0"))
        if int(row.get("reverse_value", 0)) == 0:
            signals.append(Signal("graph.zero-reverse-value", 0.05, 0.68, "reverse_value = 0"))
        if bool(row.get("is_sink", False)):
            signals.append(Signal("graph.sink", 0.03, 0.62, "is_sink = true"))

        if isinstance(file_path, str):
            hole_count = hole_counts.get(file_path, 0)
            if hole_count > 0:
                hole_boost = min(0.18, 0.04 * hole_count)
                signals.append(
                    Signal(
                        "proof-holes.by-file",
                        hole_boost,
                        0.88,
                        f"explicit proof holes in file: {hole_count}",
                    )
                )

        semantic_profile: JsonObj | None = None
        profile_scope = "none"
        profile_mapping = "none"
        profile_mapping_reliability = 0.0

        decl_signal = bridge_decl_signals.get(name)
        if isinstance(decl_signal, dict):
            semantic_profile = dict(decl_signal)
            profile_scope = "declaration"
            match_counts_any = decl_signal.get("matchProvenanceCounts")
            if isinstance(match_counts_any, dict) and match_counts_any:
                match_counts = {str(k): int(v) for k, v in match_counts_any.items() if isinstance(v, (int, float))}
                if match_counts:
                    top_match = max(match_counts.items(), key=lambda item: item[1])[0]
                    profile_mapping = top_match
                else:
                    profile_mapping = "declaration"
            else:
                profile_mapping = "declaration"
            profile_mapping_reliability = clamp01(float(decl_signal.get("avgMappingReliability", 0.0)))
            if profile_mapping_reliability <= 0.0:
                profile_mapping_reliability = 0.70
        elif isinstance(file_path, str):
            file_signal = bridge_file_signals.get(file_path)
            if isinstance(file_signal, dict):
                semantic_profile = dict(file_signal)
                profile_scope = "file"
                profile_mapping = "file-fallback"
                profile_mapping_reliability = 0.62

        if semantic_profile is not None:
            sem_count = int(semantic_profile.get("semanticCount", 0))
            fp_count = int(semantic_profile.get("fingerprintCount", 0))
            bridge_conf = clamp01(float(semantic_profile.get("avgConfidence", 0.0)))
            scoped_conf = clamp01(bridge_conf * profile_mapping_reliability)
            sem_scale = 0.13 if profile_scope == "declaration" else 0.09
            fp_scale = 0.08 if profile_scope == "declaration" else 0.05
            if sem_count > 0:
                sem_boost = sem_scale * min(1.0, sem_count / 3.0)
                signals.append(
                    Signal(
                        f"bridge.{profile_scope}.semantic-shape",
                        sem_boost,
                        scoped_conf,
                        f"{profile_mapping}: semantic observations={sem_count}",
                    )
                )
            if fp_count > 0:
                fp_boost = fp_scale * min(1.0, fp_count / 3.0)
                signals.append(
                    Signal(
                        f"bridge.{profile_scope}.fingerprint-shape",
                        fp_boost,
                        scoped_conf,
                        f"{profile_mapping}: fingerprint observations={fp_count}",
                    )
                )

        cluster_counts = semantic_profile.get("clusterKeys") if semantic_profile else None
        cluster_key = None
        if isinstance(cluster_counts, list) and cluster_counts:
            first = cluster_counts[0]
            if isinstance(first, (list, tuple)) and first and isinstance(first[0], str):
                cluster_key = first[0]
        if not cluster_key:
            cluster_key = make_cluster_key(
                fingerprint_v1=None,
                semantic_head=name,
                expr_kind="unknown",
                arity_shape_value="arity:?",
                binder_shape_value="binder:?",
            )

        score, confidence, provenance = summarize_signals(signals)
        semantic_profile_summary: JsonObj | None = None
        if semantic_profile is not None:
            semantic_profile_summary = {
                "scope": profile_scope,
                "mapping": profile_mapping,
                "mappingReliability": round(profile_mapping_reliability, 4),
                "semanticCount": int(semantic_profile.get("semanticCount", 0)),
                "fingerprintCount": int(semantic_profile.get("fingerprintCount", 0)),
                "avgConfidence": round(float(semantic_profile.get("avgConfidence", 0.0)), 4),
                "avgMappingReliability": round(float(semantic_profile.get("avgMappingReliability", 0.0)), 4),
                "semanticHeadCounts": semantic_profile.get("semanticHeadCounts", []),
                "fingerprintCounts": semantic_profile.get("fingerprintCounts", []),
                "exprKindCounts": semantic_profile.get("exprKindCounts", []),
                "arityShapeCounts": semantic_profile.get("arityShapeCounts", []),
                "binderShapeCounts": semantic_profile.get("binderShapeCounts", []),
                "clusterKeys": semantic_profile.get("clusterKeys", []),
                "matchProvenanceCounts": semantic_profile.get("matchProvenanceCounts", {}),
            }
        payload: JsonObj = {
            "name": name,
            "file": file_path,
            "module": module,
            "region": region,
            "tags": sorted(tags),
            "violations": violations,
            "semanticClusterKey": cluster_key,
            "semanticProfile": semantic_profile_summary,
            "score": round(score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=name, score=score, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def rank_owner_candidates(
    vacuity_candidates: list[JsonObj],
    owner_entries: list[JsonObj],
    file_region: dict[str, str],
    top_k: int,
) -> list[JsonObj]:
    agg_score: dict[str, float] = defaultdict(float)
    agg_signals: dict[str, list[Signal]] = defaultdict(list)
    support: dict[str, set[str]] = defaultdict(set)

    owner_by_file: dict[str, JsonObj] = {str(e.get("file")): e for e in owner_entries if e.get("file")}

    for cand in vacuity_candidates:
        cand_name = str(cand.get("name"))
        cand_file = cand.get("file")
        cand_region = cand.get("region") or file_region.get(str(cand_file), "unknown")
        cand_domain = file_domain(str(cand_file) if isinstance(cand_file, str) else None)
        cand_score = float(cand.get("score", 0.0))

        for owner_file, owner in owner_by_file.items():
            owner_region = file_region.get(owner_file, "unknown")
            owner_domain = file_domain(owner_file)

            local_signals: list[Signal] = []
            if cand_file == owner_file:
                local_signals.append(Signal("owner.exact-file", 0.75 * cand_score, 0.95, f"{cand_name} is in owner file"))
            if cand_region != "unknown" and cand_region == owner_region:
                local_signals.append(Signal("owner.same-region", 0.35 * cand_score, 0.76, f"shared region: {cand_region}"))
            if cand_domain and owner_domain and cand_domain == owner_domain:
                local_signals.append(Signal("owner.same-domain", 0.20 * cand_score, 0.72, f"shared domain: {cand_domain}"))

            if not local_signals:
                continue

            base = sum(max(0.0, s.contribution) for s in local_signals)
            agg_score[owner_file] += base
            agg_signals[owner_file].extend(local_signals)
            support[owner_file].add(cand_name)

    ranked: list[RankedEntry] = []
    for owner_file in agg_score:
        signals = agg_signals[owner_file]
        final_score, confidence, provenance = summarize_signals(signals)
        owner = owner_by_file[owner_file]
        owner_region = file_region.get(owner_file, "unknown")
        payload: JsonObj = {
            "ownerFile": owner_file,
            "region": owner_region,
            "sourceDepth": owner.get("source_depth"),
            "targetDepth": owner.get("target_depth"),
            "notes": owner.get("notes", ""),
            "supportingVacuityCandidates": sorted(support[owner_file]),
            "score": round(final_score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=owner_file, score=final_score, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def rank_declaration_plans(
    vacuity_candidates: list[JsonObj],
    owner_candidates: list[JsonObj],
    replacement_candidates: list[JsonObj],
    bridge_decl_signals: dict[str, JsonObj],
    top_k: int,
) -> list[JsonObj]:
    owner_by_file: dict[str, JsonObj] = {
        str(row.get("ownerFile")): row
        for row in owner_candidates
        if isinstance(row.get("ownerFile"), str)
    }
    replacements = list(replacement_candidates)
    ranked: list[RankedEntry] = []

    for cand in vacuity_candidates:
        cand_name = cand.get("name")
        if not isinstance(cand_name, str) or not cand_name:
            continue

        cand_file = cand.get("file") if isinstance(cand.get("file"), str) else None
        cand_region = cand.get("region") if isinstance(cand.get("region"), str) else "unknown"
        cand_score = clamp01(float(cand.get("score", 0.0)))
        cand_conf = clamp01(float(cand.get("confidence", 0.0)))
        cand_profile_any = cand.get("semanticProfile")
        cand_profile = cast(JsonObj, cand_profile_any) if isinstance(cand_profile_any, dict) else {}

        plan_signals: list[Signal] = [
            Signal(
                "candidate.vacuity-prior",
                0.32 * cand_score,
                max(0.45, cand_conf),
                f"candidate score={cand_score:.4f}",
            )
        ]

        owner_best: JsonObj | None = None
        owner_best_score = 0.0
        owner_best_conf = 0.0
        owner_best_prov: list[JsonObj] = []
        for owner in owner_by_file.values():
            owner_file = owner.get("ownerFile")
            if not isinstance(owner_file, str):
                continue
            owner_region = owner.get("region") if isinstance(owner.get("region"), str) else "unknown"
            owner_support_any = owner.get("supportingVacuityCandidates")
            owner_support = set(owner_support_any) if isinstance(owner_support_any, list) else set()

            owner_signals: list[Signal] = []
            if cand_file and cand_file == owner_file:
                owner_signals.append(
                    Signal(
                        "owner.same-file",
                        0.28 * cand_score,
                        0.95,
                        f"candidate file matches owner file: {owner_file}",
                    )
                )
            if cand_region != "unknown" and cand_region == owner_region:
                owner_signals.append(
                    Signal(
                        "owner.same-region",
                        0.14 * cand_score,
                        0.78,
                        f"candidate region matches owner region: {cand_region}",
                    )
                )
            if cand_name in owner_support:
                owner_signals.append(
                    Signal(
                        "owner.support-link",
                        0.22 * cand_score,
                        0.86,
                        f"owner already supported by candidate {cand_name}",
                    )
                )

            if not owner_signals:
                continue
            local_score, local_conf, local_prov = summarize_signals(owner_signals)
            if local_score > owner_best_score or (
                abs(local_score - owner_best_score) < 1e-9 and local_conf > owner_best_conf
            ):
                owner_best = owner
                owner_best_score = local_score
                owner_best_conf = local_conf
                owner_best_prov = local_prov

        if owner_best is not None:
            owner_file = cast(str, owner_best.get("ownerFile"))
            plan_signals.append(
                Signal(
                    "owner.best-corridor",
                    0.24 * owner_best_score,
                    owner_best_conf,
                    f"selected owner={owner_file}",
                )
            )

        cand_clusters = keys_from_counts(cand_profile.get("clusterKeys"))
        cand_heads = keys_from_counts(cand_profile.get("semanticHeadCounts"))
        cand_fps = keys_from_counts(cand_profile.get("fingerprintCounts"))

        corridor_rows: list[JsonObj] = []
        for repl in replacements:
            repl_decl = repl.get("replacementDecl")
            if not isinstance(repl_decl, str) or not repl_decl:
                continue
            repl_support_any = repl.get("supportingVacuityCandidates")
            repl_support = set(repl_support_any) if isinstance(repl_support_any, list) else set()
            repl_region = repl.get("region") if isinstance(repl.get("region"), str) else "unknown"
            owner_corridor_any = repl.get("ownerCorridor")
            owner_corridor = set(owner_corridor_any) if isinstance(owner_corridor_any, list) else set()

            repl_signals: list[Signal] = []
            if cand_name in repl_support:
                repl_signals.append(
                    Signal(
                        "replacement.support-link",
                        0.30 * cand_score,
                        0.90,
                        f"replacement already supported by candidate {cand_name}",
                    )
                )
            if cand_region != "unknown" and cand_region == repl_region:
                repl_signals.append(
                    Signal(
                        "replacement.same-region",
                        0.10 * cand_score,
                        0.74,
                        f"replacement region matches candidate region: {cand_region}",
                    )
                )
            if owner_best is not None:
                owner_file = cast(str, owner_best.get("ownerFile"))
                if owner_file in owner_corridor:
                    repl_signals.append(
                        Signal(
                            "replacement.owner-corridor",
                            0.16 * cand_score,
                            0.84,
                            f"replacement corridor includes selected owner {owner_file}",
                        )
                    )

            repl_decl_profile = bridge_decl_signals.get(repl_decl)
            if isinstance(repl_decl_profile, dict):
                repl_clusters = keys_from_counts(repl_decl_profile.get("clusterKeys"))
                repl_heads = keys_from_counts(repl_decl_profile.get("semanticHeadCounts"))
                repl_fps = keys_from_counts(repl_decl_profile.get("fingerprintCounts"))
                cluster_overlap = jaccard_overlap(cand_clusters, repl_clusters)
                head_overlap = jaccard_overlap(cand_heads, repl_heads)
                fp_overlap = jaccard_overlap(cand_fps, repl_fps)
                overlap = 0.5 * cluster_overlap + 0.3 * head_overlap + 0.2 * fp_overlap
                if overlap > 0.0:
                    repl_signals.append(
                        Signal(
                            "replacement.decl-shape-overlap",
                            0.18 * cand_score * overlap,
                            0.80,
                            (
                                "bridge declaration overlap "
                                f"(cluster={cluster_overlap:.3f}, head={head_overlap:.3f}, fp={fp_overlap:.3f})"
                            ),
                        )
                    )

            repl_prior_score = clamp01(float(repl.get("score", 0.0)))
            repl_prior_conf = clamp01(float(repl.get("confidence", 0.0)))
            if repl_prior_score > 0.0:
                repl_signals.append(
                    Signal(
                        "replacement.rank-prior",
                        0.14 * repl_prior_score,
                        max(0.40, repl_prior_conf),
                        f"replacement ranking prior={repl_prior_score:.4f}",
                    )
                )

            if not repl_signals:
                continue
            repl_score, repl_conf, repl_prov = summarize_signals(repl_signals)
            if repl_score <= 0.0:
                continue
            corridor_rows.append(
                {
                    "replacementDecl": repl_decl,
                    "region": repl_region,
                    "score": round(repl_score, 4),
                    "confidence": round(repl_conf, 4),
                    "confidenceProvenance": repl_prov,
                }
            )

        corridor_rows.sort(
            key=lambda row: (
                -float(row.get("score", 0.0)),
                -float(row.get("confidence", 0.0)),
                str(row.get("replacementDecl", "")),
            )
        )
        probable_corridor = corridor_rows[:3]

        if probable_corridor:
            best_repl = probable_corridor[0]
            plan_signals.append(
                Signal(
                    "replacement.best-corridor",
                    0.24 * clamp01(float(best_repl.get("score", 0.0))),
                    clamp01(float(best_repl.get("confidence", 0.0))),
                    f"selected replacement={best_repl.get('replacementDecl')}",
                )
            )
            if len(probable_corridor) > 1:
                plan_signals.append(
                    Signal(
                        "replacement.alternatives",
                        min(0.06, 0.02 * (len(probable_corridor) - 1)),
                        0.62,
                        f"alternative corridor count={len(probable_corridor)}",
                    )
                )

        score, confidence, provenance = summarize_signals(plan_signals)

        owner_payload: JsonObj | None = None
        if owner_best is not None:
            owner_payload = {
                "ownerFile": owner_best.get("ownerFile"),
                "region": owner_best.get("region"),
                "score": round(owner_best_score, 4),
                "confidence": round(owner_best_conf, 4),
                "confidenceProvenance": owner_best_prov,
            }

        payload: JsonObj = {
            "candidate": cand_name,
            "candidateFile": cand_file,
            "candidateRegion": cand_region,
            "candidateScore": round(cand_score, 4),
            "candidateConfidence": round(cand_conf, 4),
            "probable_owner": owner_payload,
            "probable_replacement_corridor": probable_corridor,
            "score": round(score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=cand_name, score=score, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def rank_fingerprint_corridors(
    vacuity_candidates: list[JsonObj],
    replacement_candidates: list[JsonObj],
    bridge_decl_signals: dict[str, JsonObj],
    top_k: int,
) -> list[JsonObj]:
    buckets: dict[str, JsonObj] = {}

    def ensure_bucket(cluster_key: str) -> JsonObj:
        bucket = buckets.get(cluster_key)
        if isinstance(bucket, dict):
            return bucket
        bucket = {
            "clusterKey": cluster_key,
            "vacuityCandidates": [],
            "replacementCandidates": [],
            "scoreSamples": [],
            "confidenceSamples": [],
            "replacementParticipationWeight": 0.0,
            "regionCounts": Counter(),
        }
        buckets[cluster_key] = bucket
        return bucket

    for cand in vacuity_candidates:
        cluster_any = cand.get("semanticClusterKey")
        if not isinstance(cluster_any, str) or not cluster_any:
            continue
        bucket = ensure_bucket(cluster_any)
        name = cand.get("name")
        if not isinstance(name, str) or not name:
            continue
        score = clamp01(float(cand.get("score", 0.0)))
        confidence = clamp01(float(cand.get("confidence", 0.0)))
        region_any = cand.get("region")
        region = region_any if isinstance(region_any, str) else "unknown"
        cast(list[JsonObj], bucket["vacuityCandidates"]).append(
            {
                "name": name,
                "score": round(score, 4),
                "confidence": round(confidence, 4),
                "region": region,
            }
        )
        cast(list[float], bucket["scoreSamples"]).append(score)
        cast(list[float], bucket["confidenceSamples"]).append(confidence)
        cast(Counter[str], bucket["regionCounts"])[region] += 1

    for repl in replacement_candidates:
        repl_decl = repl.get("replacementDecl")
        if not isinstance(repl_decl, str) or not repl_decl:
            continue
        profile = bridge_decl_signals.get(repl_decl)
        if not isinstance(profile, dict):
            continue
        cluster_keys = top_count_keys(
            profile.get("clusterKeys"),
            limit=REPLACEMENT_CLUSTER_PARTICIPATION_LIMIT,
        )
        if not cluster_keys:
            continue
        score = clamp01(float(repl.get("score", 0.0)))
        confidence = clamp01(float(repl.get("confidence", 0.0)))
        region_any = repl.get("region")
        region = region_any if isinstance(region_any, str) else "unknown"

        for cluster_rank, cluster_key in enumerate(cluster_keys, start=1):
            cluster_weight = _cluster_rank_weight(cluster_rank)
            bucket = ensure_bucket(cluster_key)
            cast(list[JsonObj], bucket["replacementCandidates"]).append(
                {
                    "replacementDecl": repl_decl,
                    "score": round(score, 4),
                    "confidence": round(confidence, 4),
                    "region": region,
                    "clusterRank": cluster_rank,
                    "clusterWeight": round(cluster_weight, 4),
                    "effectiveScore": round(score * cluster_weight, 4),
                    "effectiveConfidence": round(confidence * cluster_weight, 4),
                }
            )
            cast(list[float], bucket["scoreSamples"]).append(score * cluster_weight)
            cast(list[float], bucket["confidenceSamples"]).append(confidence * cluster_weight)
            bucket["replacementParticipationWeight"] = float(bucket.get("replacementParticipationWeight", 0.0)) + cluster_weight
            cast(Counter[str], bucket["regionCounts"])[region] += 1

    ranked: list[RankedEntry] = []
    for cluster_key, bucket in buckets.items():
        vac_rows = cast(list[JsonObj], bucket["vacuityCandidates"])
        repl_rows = cast(list[JsonObj], bucket["replacementCandidates"])
        vac_rows.sort(key=lambda row: (-float(row.get("score", 0.0)), str(row.get("name", ""))))
        repl_rows.sort(
            key=lambda row: (
                -float(row.get("effectiveScore", row.get("score", 0.0))),
                -float(row.get("effectiveConfidence", row.get("confidence", 0.0))),
                str(row.get("replacementDecl", "")),
            )
        )

        vac_count = len(vac_rows)
        repl_count = len(repl_rows)
        if vac_count == 0 and repl_count == 0:
            continue

        coverage = min(1.0, vac_count / 3.0)
        replacement_weight = float(bucket.get("replacementParticipationWeight", 0.0))
        corridor_depth = min(1.0, replacement_weight / 3.0)
        signal_strength = safe_mean(cast(list[float], bucket["scoreSamples"]), default=0.0)
        score = clamp01(0.42 * coverage + 0.28 * corridor_depth + 0.30 * signal_strength)
        confidence = clamp01(safe_mean(cast(list[float], bucket["confidenceSamples"]), default=0.0))

        payload: JsonObj = {
            "clusterKey": cluster_key,
            "vacuityCount": vac_count,
            "replacementCount": repl_count,
            "replacementParticipationWeight": round(replacement_weight, 4),
            "vacuityCandidates": vac_rows[:5],
            "replacementCandidates": repl_rows[:5],
            "regions": dict(cast(Counter[str], bucket["regionCounts"])),
            "score": round(score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": [
                {
                    "signal": "corridor.vacuity-coverage",
                    "contribution": round(0.42 * coverage, 4),
                    "reliability": 0.82,
                    "evidence": f"vacuity candidates={vac_count}",
                },
                {
                    "signal": "corridor.replacement-depth",
                    "contribution": round(0.28 * corridor_depth, 4),
                    "reliability": 0.80,
                    "evidence": (
                        f"replacement candidates={repl_count}, "
                        f"weighted participation={replacement_weight:.4f}"
                    ),
                },
                {
                    "signal": "corridor.signal-strength",
                    "contribution": round(0.30 * signal_strength, 4),
                    "reliability": 0.78,
                    "evidence": f"mean candidate score={signal_strength:.4f}",
                },
            ],
        }
        ranked.append(RankedEntry(key=cluster_key, score=score, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def rank_replacement_candidates(
    vacuity_candidates: list[JsonObj],
    forward_edges: dict[str, list[tuple[str, str]]],
    decls: dict[str, JsonObj],
    theorem_by_name: dict[str, JsonObj],
    file_region: dict[str, str],
    owner_candidates: list[JsonObj],
    top_k: int,
) -> list[JsonObj]:
    owner_by_region: dict[str, list[str]] = defaultdict(list)
    for owner in owner_candidates:
        owner_file = owner.get("ownerFile")
        if not isinstance(owner_file, str):
            continue
        reg = file_region.get(owner_file, "unknown")
        owner_by_region[reg].append(owner_file)

    agg_score: dict[str, float] = defaultdict(float)
    agg_signals: dict[str, list[Signal]] = defaultdict(list)
    support: dict[str, set[str]] = defaultdict(set)

    for cand in vacuity_candidates:
        src_name = str(cand.get("name") or "")
        src_file = cand.get("file")
        src_region = cand.get("region") or file_region.get(str(src_file), "unknown")
        src_score = float(cand.get("score", 0.0))
        if not src_name:
            continue

        for dst, edge_kind in forward_edges.get(src_name, []):
            decl = decls.get(dst)
            if not decl:
                continue

            dst_kind = str(decl.get("kind", ""))
            if dst_kind not in {"theorem", "def", "lemma", "abbrev"}:
                continue

            dst_file = parse_uri_or_path(decl.get("file"), repo_root())
            dst_region = file_region.get(dst_file or "", "unknown")

            signals: list[Signal] = []
            if edge_kind == "value":
                signals.append(Signal("edge.value", 0.55 * src_score, 0.84, f"value-edge from {src_name}"))
            else:
                signals.append(Signal("edge.type", 0.35 * src_score, 0.74, f"type-edge from {src_name}"))

            dst_meta = theorem_by_name.get(dst)
            if dst_meta:
                dst_tags = set(dst_meta.get("tags") or [])
                if "dead-candidate" in dst_tags:
                    signals.append(
                        Signal("dst.dead-penalty", -0.12 * src_score, 0.86, "destination tagged dead-candidate")
                    )
                elif "wrapper-candidate" in dst_tags:
                    signals.append(
                        Signal("dst.wrapper-penalty", -0.08 * src_score, 0.80, "destination tagged wrapper-candidate")
                    )
                elif "statement-bearing" in dst_tags:
                    signals.append(
                        Signal("dst.statement-bearing", 0.14 * src_score, 0.78, "destination tagged statement-bearing")
                    )

            if src_region != "unknown" and src_region == dst_region:
                signals.append(Signal("region.match", 0.06 * src_score, 0.70, f"shared region: {src_region}"))

            if owner_by_region.get(dst_region):
                signals.append(
                    Signal("owner.corridor-present", 0.05 * src_score, 0.68, f"owner corridor in region {dst_region}")
                )

            if not signals:
                continue

            local_score = sum(s.contribution for s in signals)
            if local_score <= 0:
                continue

            agg_score[dst] += local_score
            agg_signals[dst].extend(signals)
            support[dst].add(src_name)

    ranked: list[RankedEntry] = []
    for dst in agg_score:
        decl = decls[dst]
        dst_file = parse_uri_or_path(decl.get("file"), repo_root())
        dst_region = file_region.get(dst_file or "", "unknown")
        score_clamped, confidence, provenance = summarize_signals(agg_signals[dst])
        payload: JsonObj = {
            "replacementDecl": dst,
            "kind": decl.get("kind"),
            "file": dst_file,
            "module": decl.get("module"),
            "region": dst_region,
            "ownerCorridor": owner_by_region.get(dst_region, [])[:3],
            "supportingVacuityCandidates": sorted(support[dst]),
            "score": round(score_clamped, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=dst, score=score_clamped, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out
