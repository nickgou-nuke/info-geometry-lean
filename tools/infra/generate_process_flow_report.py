#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, cast

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root

DEFAULT_INPUT_DIR = "artifacts/dag/process-flow"
DEFAULT_COCYCLES_OUT = "artifacts/dag/process-flow/flow-cocycles.jsonl"
DEFAULT_COMPARISONS_OUT = "artifacts/dag/process-flow/comparison-candidates.jsonl"
DEFAULT_REPORT_OUT = "reports/dag/process-flow-defect-report.md"
DEFAULT_JSON_OUT = "reports/dag/process-flow-defect-report.json"
COCYCLE_SCHEMA_VERSION = 1
COMPARISON_SCHEMA_VERSION = 1
EXPECTED_INPUT_SCHEMA_VERSION = 4

JsonDict = dict[str, Any]

DEFECT_SEVERITY: dict[str, int] = {
    "illicitBoundaryCrossing": 5,
    "regressiveFlow": 5,
    "boundaryBypass": 4,
    "remoteAttachment": 3,
    "failedLocalFactorization": 3,
    "mixedPolarity": 2,
    "unclearPolarity": 2,
    "typeOnlySupport": 1,
    "unresolvedComparison": 1,
}

ROLE_CREDIT: dict[str, int] = {
    "head": 5,
    "transportArg": 6,
    "requiredArg": 3,
    "witness": 2,
    "closureSupport": 1,
    "ornament": 0,
    "remoteSupport": 0,
    "unknown": 0,
}

BOUNDARY_CREDIT: dict[str, int] = {
    "bridge": 2,
    "localInterface": 1,
    "internal": 0,
    "capstone": 0,
    "mixed": 0,
    "unclear": 0,
}

COMPARISON_STATUS_RANK: dict[str, int] = {
    "parallel_unresolved": 0,
    "parallel_coherent": 1,
    "merely_similar": 2,
}



def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate derived cocycle, comparison, and defect reports from the constitutive process-flow JSONL artifacts."
        )
    )
    parser.add_argument("--input-dir", default=DEFAULT_INPUT_DIR, help="Directory containing process-flow JSONL artifacts.")
    parser.add_argument("--cocycles-out", default=DEFAULT_COCYCLES_OUT, help="JSONL file to write derived edge cocycles.")
    parser.add_argument("--comparisons-out", default=DEFAULT_COMPARISONS_OUT, help="JSONL file to write derived comparison candidates.")
    parser.add_argument("--report-out", default=DEFAULT_REPORT_OUT, help="Markdown report path.")
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT, help="JSON summary path.")
    parser.add_argument("--top", type=int, default=12, help="Top-N rows per ranked section.")
    parser.add_argument(
        "--max-shared-sources-per-path",
        type=int,
        default=16,
        help="Cap shared comparison source expansion per path (0 disables cap).",
    )
    parser.add_argument(
        "--max-candidate-paths-per-path",
        type=int,
        default=128,
        help="Cap candidate comparison paths considered per path (0 disables cap).",
    )
    parser.add_argument(
        "--max-comparison-pairs",
        type=int,
        default=20000,
        help="Global cap on comparison pairs evaluated (0 disables cap).",
    )
    parser.add_argument(
        "--max-witness-searches",
        type=int,
        default=2000,
        help="Global cap on closure witness searches for pair comparisons (0 disables cap).",
    )
    parser.add_argument(
        "--max-comparison-seconds",
        type=float,
        default=45.0,
        help="Wall-clock budget for comparison generation in seconds (0 disables cap).",
    )
    return parser.parse_args()



def load_jsonl(path: Path) -> list[JsonDict]:
    rows: list[JsonDict] = []
    if not path.exists():
        return rows
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line:
            continue
        obj = json.loads(line)
        if isinstance(obj, dict):
            rows.append(cast(JsonDict, obj))
    return rows



def validate_schema(rows: list[JsonDict], label: str, expected: int) -> None:
    if not rows:
        return
    versions = {row.get("schemaVersion") for row in rows}
    if versions != {expected}:
        raise SystemExit(
            f"unexpected {label} schemaVersion set {sorted(str(version) for version in versions)!r}; expected only {expected}"
        )



def write_jsonl(path: Path, rows: list[JsonDict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [json.dumps(row, ensure_ascii=True, sort_keys=True) for row in rows]
    path.write_text(("\n".join(lines) + "\n") if lines else "", encoding="utf-8")



def write_json(path: Path, payload: JsonDict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")



def edge_use_has_value(edge_use: str) -> bool:
    return edge_use in {"valueOnly", "both"}



def edge_use_has_type(edge_use: str) -> bool:
    return edge_use in {"typeOnly", "both"}



def compute_transport_credit(edge: JsonDict) -> int:
    edge_use = str(edge.get("edgeUse", ""))
    base = 4 if edge_use_has_value(edge_use) else 1 if edge_use_has_type(edge_use) else 0
    role = str(edge.get("inferredRole", "unknown"))
    boundary = str(edge.get("inferredBoundary", "unclear"))
    return base + ROLE_CREDIT.get(role, 0) + BOUNDARY_CREDIT.get(boundary, 0)



def compute_defect_debt(defect_tags: list[str]) -> int:
    return sum(DEFECT_SEVERITY.get(tag, 1) for tag in defect_tags)



def classify_grade(edge: dict[str, Any]) -> str:
    polarity = str(edge.get("inferredPolarity", ""))
    if polarity == "sameLayer":
        return "same_layer"
    if polarity == "descending":
        return "adjacent_descent"
    if polarity == "remote":
        return "remote_descent"
    if polarity == "regressive":
        return "regressive"
    return "unclear"



def feature_key(bundle: Any) -> str:
    return json.dumps(bundle if isinstance(bundle, dict) else {}, ensure_ascii=True, sort_keys=True)



def event_feature_out_bundles(ev: JsonDict) -> list[JsonDict]:
    raw = ev.get("featureOut", [])
    if isinstance(raw, dict):
        return [cast(JsonDict, raw)]
    if isinstance(raw, list):
        bundles: list[JsonDict] = []
        for bundle in cast(list[Any], raw):
            if isinstance(bundle, dict):
                bundles.append(cast(JsonDict, bundle))
        return bundles
    return []


def build_event_target_index(events: list[JsonDict]) -> dict[tuple[str, str], list[JsonDict]]:
    buckets: dict[tuple[str, str], list[JsonDict]] = defaultdict(list)
    seen: dict[tuple[str, str], set[str]] = defaultdict(set)
    for ev in events:
        typed_ev = dict(ev)
        node = str(ev.get("node", ""))
        boundary = str(ev.get("boundaryClass", ""))
        typed_ev["_closureSet"] = {str(x) for x in ev.get("closureDeps", [])}
        for bundle in event_feature_out_bundles(ev):
            key = (boundary, feature_key(bundle))
            if node and node in seen[key]:
                continue
            if node:
                seen[key].add(node)
            buckets[key].append(typed_ev)
    return buckets


def is_duplicate_path_defect_row(row: JsonDict) -> bool:
    if str(row.get("locus", "")) != "path":
        return False
    defect = row.get("defect", {})
    if not isinstance(defect, dict):
        return False
    typed_defect = cast(JsonDict, defect)
    kind = str(typed_defect.get("kind", ""))
    return kind != "unresolvedComparison"


def max_witness_score(row: JsonDict) -> int:
    details = row.get("witnessDetails", [])
    if not isinstance(details, list):
        return 0
    scores: list[int] = []
    for item in cast(list[Any], details):
        if isinstance(item, dict):
            typed_item = cast(JsonDict, item)
            scores.append(int(typed_item.get("score", 0)))
    return max(scores, default=0)


def validate_exporter_contract(
    paths: list[JsonDict],
    defects: list[JsonDict],
) -> None:
    for path in paths:
        raw_defects = path.get("defects", [])
        if not isinstance(raw_defects, list):
            raise SystemExit(f"path {path.get('src')} -> {path.get('dst')} has non-list defects")
        for defect in cast(list[Any], raw_defects):
            if not isinstance(defect, dict):
                raise SystemExit(f"path {path.get('src')} -> {path.get('dst')} has non-dict defect row")
            typed = cast(JsonDict, defect)
            kind = str(typed.get("kind", ""))
            if kind != "unresolvedComparison":
                raise SystemExit(
                    f"path {path.get('src')} -> {path.get('dst')} exported unexpected path-local defect kind {kind!r}"
                )

    for row in defects:
        locus = str(row.get("locus", ""))
        defect = row.get("defect", {})
        if not isinstance(defect, dict):
            continue
        typed = cast(JsonDict, defect)
        kind = str(typed.get("kind", ""))
        if locus == "path" and kind != "unresolvedComparison":
            raise SystemExit(
                f"defects.jsonl contains unexpected path-locus defect kind {kind!r}"
            )


def sequence_similarity(a: list[str], b: list[str]) -> float:
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    matches = sum(1 for x, y in zip(a, b) if x == y)
    return (2.0 * matches) / (len(a) + len(b))



def jaccard_distance(a: set[str], b: set[str]) -> float:
    if not a and not b:
        return 0.0
    union = a | b
    if not union:
        return 0.0
    return 1.0 - (len(a & b) / len(union))



def build_cocycles(
    flow_edges: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], dict[tuple[str, str], dict[str, Any]]]:
    rows: list[dict[str, Any]] = []
    by_pair: dict[tuple[str, str], dict[str, Any]] = {}
    for idx, edge in enumerate(flow_edges):
        defect_tags = [str(tag) for tag in edge.get("defectTags", [])]
        transport_credit = compute_transport_credit(edge)
        defect_debt = compute_defect_debt(defect_tags)
        row: JsonDict = {
            "schemaVersion": COCYCLE_SCHEMA_VERSION,
            "flowEdgeSchemaVersion": edge.get("schemaVersion"),
            "edgeIndex": idx,
            "src": str(edge.get("src", "")),
            "dst": str(edge.get("dst", "")),
            "edgeUse": str(edge.get("edgeUse", "")),
            "edgeKind": str(edge.get("edgeKind", "")),
            "inferredRole": str(edge.get("inferredRole", "")),
            "inferredBoundary": str(edge.get("inferredBoundary", "")),
            "inferredPolarity": str(edge.get("inferredPolarity", "")),
            "transportCredit": transport_credit,
            "defectDebt": defect_debt,
            "netWeight": transport_credit - defect_debt,
            "grade": classify_grade(edge),
            "anomalous": defect_debt > 0,
            "defectTags": defect_tags,
        }
        rows.append(row)
        by_pair[(row["src"], row["dst"])] = row
    return rows, by_pair





def build_path_summaries(
    paths: list[JsonDict],
    cocycles_by_pair: dict[tuple[str, str], JsonDict],
    events: list[JsonDict],
) -> list[JsonDict]:
    out: list[JsonDict] = []
    event_by_node = {str(ev.get("node", "")): ev for ev in events}
    for path_id, path in enumerate(paths):
        raw_steps = path.get("steps", [])
        steps: list[JsonDict] = []
        if isinstance(raw_steps, list):
            for step in cast(list[Any], raw_steps):
                if isinstance(step, dict):
                    steps.append(cast(JsonDict, step))
        transport_credit = 0
        edge_accumulated_debt = 0
        net_weight = 0
        grades: list[str] = []
        role_signature: list[str] = []
        boundary_signature: list[str] = []
        support_core: set[str] = set()
        head_core: set[str] = set()
        for idx, step in enumerate(steps):
            key = (str(step.get("src", "")), str(step.get("dst", "")))
            cocycle = cocycles_by_pair.get(key)
            if cocycle is not None:
                transport_credit += int(cocycle["transportCredit"])
                edge_accumulated_debt += int(cocycle["defectDebt"])
                net_weight += int(cocycle["netWeight"])
                grades.append(str(cocycle["grade"]))
            role = str(step.get("inferredRole", ""))
            boundary = str(step.get("inferredBoundary", ""))
            role_signature.append(role)
            boundary_signature.append(boundary)
            dst = str(step.get("dst", ""))
            if idx < len(steps) - 1 and role not in {"ornament", "remoteSupport"} and dst:
                support_core.add(dst)
            if role in {"head", "transportArg", "requiredArg"} and dst:
                head_core.add(dst)

        last_step = steps[-1] if steps else None
        dst = str(path.get("dst", ""))
        dst_event = event_by_node.get(dst, {})
        dst_feature_bundles = event_feature_out_bundles(dst_event)
        target_feature = dst_feature_bundles[0] if dst_feature_bundles else (last_step.get("featureOut", {}) if last_step else {})
        target_boundary = str(dst_event.get("boundaryClass", "")) or (
            str(last_step.get("inferredBoundary", "unclear")) if last_step else "unclear"
        )

        path_defect_cost = int(path.get("totalDefectCost", 0))
        path_residual_debt = max(path_defect_cost - edge_accumulated_debt, 0)

        out.append(
            {
                "pathId": path_id,
                "src": str(path.get("src", "")),
                "dst": dst,
                "stepCount": len(steps),
                "transportCredit": transport_credit,
                "edgeAccumulatedDebt": edge_accumulated_debt,
                "pathDefectCost": path_defect_cost,
                "pathResidualDebt": path_residual_debt,
                "exportedPathResidualDebt": path_residual_debt,
                "pairwiseConfirmedResidualDebt": 0,
                "netWeight": net_weight,
                "sharedComparisonCandidates": list(path.get("sharedComparisonCandidates", [])),
                "grades": grades,
                "roleSignature": role_signature,
                "boundarySignature": boundary_signature,
                "targetFeature": target_feature,
                "targetFeatureKey": feature_key(target_feature),
                "targetBoundary": target_boundary,
                "supportCore": sorted(support_core),
                "headCore": sorted(head_core),
                "_supportCoreSet": set(support_core),
                "_headCoreSet": set(head_core),
                "_roleSignatureTuple": tuple(role_signature),
                "_boundarySignatureTuple": tuple(boundary_signature),
                "effectivePathResidualDebt": path_residual_debt,  # deprecated compatibility alias; equals exportedPathResidualDebt
                "unresolvedPairCount": 0,
                "coherentPairCount": 0,
                "merelySimilarPairCount": 0,
            }
        )
    return out




def witness_match_detail(
    ev: JsonDict,
    path_a: JsonDict,
    path_b: JsonDict,
) -> JsonDict | None:
    node = str(ev.get("node", ""))
    target_feature_key = str(path_a.get("targetFeatureKey", ""))
    target_boundary = str(path_a.get("targetBoundary", ""))

    if str(ev.get("boundaryClass", "")) != target_boundary:
        return None

    feature_out = event_feature_out_bundles(ev)
    if not any(feature_key(bundle) == target_feature_key for bundle in feature_out):
        return None

    closure = cast(set[str], ev.get("_closureSet", set()))
    support_union = cast(set[str], path_a.get("_supportCoreSet", set())) | cast(set[str], path_b.get("_supportCoreSet", set()))
    head_union = cast(set[str], path_a.get("_headCoreSet", set())) | cast(set[str], path_b.get("_headCoreSet", set()))
    source_union = {str(path_a.get("src", "")), str(path_b.get("src", ""))} - {""}

    score = 0
    reasons: list[str] = []

    if support_union:
        if support_union.issubset(closure):
            score += 4
            reasons.append("support_core_cover")
        elif support_union & closure:
            score += 2
            reasons.append("support_core_overlap")
        else:
            return None

    if head_union and (head_union & closure):
        score += 2
        reasons.append("head_core_overlap")

    if source_union and (source_union & closure):
        score += 1
        reasons.append("source_overlap")

    if not reasons:
        return None

    return {
        "node": node,
        "score": score,
        "reasons": reasons,
    }


def find_comparison_witnesses(
    path_a: JsonDict,
    path_b: JsonDict,
    events_by_target: dict[tuple[str, str], list[JsonDict]],
) -> list[JsonDict]:
    matches_by_node: dict[str, JsonDict] = {}
    excluded = {
        str(path_a.get("src", "")),
        str(path_b.get("src", "")),
        str(path_a.get("dst", "")),
        str(path_b.get("dst", "")),
    }

    target_feature_key = str(path_a.get("targetFeatureKey", ""))
    target_boundary = str(path_a.get("targetBoundary", ""))
    target_events = events_by_target.get((target_boundary, target_feature_key), [])

    for ev in target_events:
        node = str(ev.get("node", ""))
        if node in excluded:
            continue
        if str(ev.get("boundaryClass", "")) != target_boundary:
            continue
        if not any(feature_key(bundle) == target_feature_key for bundle in event_feature_out_bundles(ev)):
            continue
        detail = witness_match_detail(ev, path_a, path_b)
        if detail is not None:
            detail = dict(detail)
            detail["source"] = "closure_match"
            detail["featureTargetMatch"] = True
            detail["boundaryMatch"] = True
            existing = matches_by_node.get(node)
            if existing is None or int(detail["score"]) > int(existing["score"]):
                matches_by_node[node] = detail

    matches = sorted(matches_by_node.values(), key=lambda row: (-int(row["score"]), str(row["node"])))
    return matches




def build_comparison_candidates(
    path_summaries: list[JsonDict],
    events: list[JsonDict],
    *,
    max_shared_sources_per_path: int,
    max_candidate_paths_per_path: int,
    max_comparison_pairs: int,
    max_witness_searches: int,
    max_comparison_seconds: float,
) -> tuple[list[JsonDict], list[JsonDict]]:
    events_by_target = build_event_target_index(events)
    paths_by_src: dict[str, list[JsonDict]] = defaultdict(list)
    paths_by_dst: dict[str, list[JsonDict]] = defaultdict(list)
    shared_candidates_by_path_id: dict[int, set[str]] = {}
    for path in path_summaries:
        paths_by_src[str(path["src"])].append(path)
        paths_by_dst[str(path["dst"])].append(path)
        shared_candidates_by_path_id[int(path["pathId"])] = {
            str(name)
            for name in cast(list[Any], path.get("sharedComparisonCandidates", []))
            if str(name)
        }

    rows: list[JsonDict] = []
    seen_pairs: set[tuple[int, int]] = set()
    capped_out = False
    witness_search_count = 0
    started_at = time.perf_counter()
    for path_a in path_summaries:
        if max_comparison_seconds > 0 and (time.perf_counter() - started_at) >= max_comparison_seconds:
            capped_out = True
            break
        path_a_id = int(path_a["pathId"])
        candidate_paths_by_id: dict[int, JsonDict] = {}
        candidate_srcs = shared_candidates_by_path_id[path_a_id]
        sorted_srcs = sorted(candidate_srcs)
        if max_shared_sources_per_path > 0:
            sorted_srcs = sorted_srcs[:max_shared_sources_per_path]
        for src in sorted_srcs:
            for path_b in paths_by_src.get(src, []):
                candidate_paths_by_id[int(path_b["pathId"])] = path_b
        same_dst_paths = paths_by_dst.get(str(path_a["dst"]), [])
        if len(same_dst_paths) <= 64:
            for path_b in same_dst_paths:
                candidate_paths_by_id[int(path_b["pathId"])] = path_b

        candidate_items = sorted(candidate_paths_by_id.items())
        if max_candidate_paths_per_path > 0:
            candidate_items = candidate_items[:max_candidate_paths_per_path]
        for path_b_id, path_b in candidate_items:
            if max_comparison_seconds > 0 and (time.perf_counter() - started_at) >= max_comparison_seconds:
                capped_out = True
                break
            path_b_id = int(path_b["pathId"])
            if path_b_id <= path_a_id:
                continue
            pair_key = (path_a_id, path_b_id)
            if pair_key in seen_pairs:
                continue
            seen_pairs.add(pair_key)
            same_dst = str(path_a["dst"]) == str(path_b["dst"])
            same_feature_target = str(path_a["targetFeatureKey"]) == str(path_b["targetFeatureKey"])
            same_boundary = str(path_a["targetBoundary"]) == str(path_b["targetBoundary"])
            if not (same_dst or (same_feature_target and same_boundary)):
                continue
            reciprocal_candidate = str(path_a["src"]) in shared_candidates_by_path_id[path_b_id]
            if not same_dst and not reciprocal_candidate:
                continue
            role_match = sequence_similarity(list(path_a["_roleSignatureTuple"]), list(path_b["_roleSignatureTuple"]))
            boundary_match = sequence_similarity(list(path_a["_boundarySignatureTuple"]), list(path_b["_boundarySignatureTuple"]))
            grade_match = sequence_similarity(list(path_a["grades"]), list(path_b["grades"]))
            support_divergence = jaccard_distance(
                cast(set[str], path_a["_supportCoreSet"]),
                cast(set[str], path_b["_supportCoreSet"]),
            )
            distinct_profile = (
                path_a["supportCore"] != path_b["supportCore"]
                or path_a["roleSignature"] != path_b["roleSignature"]
                or path_a["src"] != path_b["src"]
            )
            if not distinct_profile:
                evidence_class = "overlap_only"
            elif same_feature_target and same_boundary and role_match >= 0.85 and support_divergence > 0.0:
                evidence_class = "coherence_candidate"
            elif same_feature_target and same_boundary and role_match >= 0.5:
                evidence_class = "parallel_transport"
            else:
                evidence_class = "overlap_only"
            should_search_witnesses = same_dst or evidence_class == "coherence_candidate"
            if should_search_witnesses:
                if max_witness_searches > 0 and witness_search_count >= max_witness_searches:
                    should_search_witnesses = False
                elif max_comparison_seconds > 0 and (time.perf_counter() - started_at) >= max_comparison_seconds:
                    should_search_witnesses = False
            if should_search_witnesses:
                witness_matches = find_comparison_witnesses(path_a, path_b, events_by_target)
                witness_search_count += 1
            else:
                witness_matches = []
            witness_nodes = [row["node"] for row in witness_matches]
            if evidence_class == "overlap_only":
                comparison_status = "merely_similar"
            elif not should_search_witnesses:
                comparison_status = "merely_similar"
            elif witness_nodes:
                comparison_status = "parallel_coherent"
            else:
                comparison_status = "parallel_unresolved"
            rows.append(
                {
                    "schemaVersion": COMPARISON_SCHEMA_VERSION,
                    "pathAId": int(path_a["pathId"]),
                    "pathBId": int(path_b["pathId"]),
                    "srcA": str(path_a["src"]),
                    "srcB": str(path_b["src"]),
                    "dst": str(path_a["dst"] if same_dst else "<feature-match>"),
                    "sharedTarget": same_dst,
                    "sameFeatureTarget": same_feature_target,
                    "sameBoundary": same_boundary,
                    "roleSignatureMatch": round(role_match, 3),
                    "boundarySignatureMatch": round(boundary_match, 3),
                    "gradeSignatureMatch": round(grade_match, 3),
                    "supportDivergence": round(support_divergence, 3),
                    "sharedSupportCore": sorted(set(path_a["supportCore"]) & set(path_b["supportCore"])),
                    "evidenceClass": evidence_class,
                    "comparisonStatus": comparison_status,
                    "witnessNodes": witness_nodes,
                    "witnessDetails": witness_matches[:5],
                }
            )
            if max_comparison_pairs > 0 and len(rows) >= max_comparison_pairs:
                capped_out = True
                break
        if capped_out:
            break
    rows.sort(
        key=lambda row: (
            COMPARISON_STATUS_RANK.get(str(row["comparisonStatus"]), 99),
            -row["roleSignatureMatch"],
            -row["boundarySignatureMatch"],
            row["pathAId"],
            row["pathBId"],
        )
    )

    updated: list[JsonDict] = []
    unresolved_counter: Counter[int] = Counter()
    coherent_counter: Counter[int] = Counter()
    similar_counter: Counter[int] = Counter()
    for row in rows:
        a = int(row["pathAId"])
        b = int(row["pathBId"])
        status = str(row["comparisonStatus"])
        if status == "parallel_unresolved":
            unresolved_counter[a] += 1
            unresolved_counter[b] += 1
        elif status == "parallel_coherent":
            coherent_counter[a] += 1
            coherent_counter[b] += 1
        else:
            similar_counter[a] += 1
            similar_counter[b] += 1

    for path in path_summaries:
        pid = int(path["pathId"])
        updated_path = dict(path)
        updated_path["unresolvedPairCount"] = int(unresolved_counter[pid])
        updated_path["coherentPairCount"] = int(coherent_counter[pid])
        updated_path["merelySimilarPairCount"] = int(similar_counter[pid])
        pairwise_confirmed_residual_debt = unresolved_counter[pid] * DEFECT_SEVERITY["unresolvedComparison"]
        updated_path["pairwiseConfirmedResidualDebt"] = pairwise_confirmed_residual_debt
        updated_path["effectivePathResidualDebt"] = (
            int(path["exportedPathResidualDebt"]) + pairwise_confirmed_residual_debt
        )
        updated.append(updated_path)
    return rows, updated




def validate_derived_state(
    path_summaries: list[JsonDict],
    comparison_candidates: list[JsonDict],
) -> None:
    for path in path_summaries:
        raw = int(path.get("pathResidualDebt", 0))
        exported = int(path.get("exportedPathResidualDebt", 0))
        pairwise = int(path.get("pairwiseConfirmedResidualDebt", 0))
        effective = int(path.get("effectivePathResidualDebt", 0))
        unresolved_pairs = int(path.get("unresolvedPairCount", 0))

        expected_pairwise = unresolved_pairs * DEFECT_SEVERITY["unresolvedComparison"]

        if exported != raw:
            raise SystemExit(
                f"path {path.get('pathId')} exportedPathResidualDebt={exported} "
                f"but pathResidualDebt={raw}"
            )
        if pairwise != expected_pairwise:
            raise SystemExit(
                f"path {path.get('pathId')} pairwiseConfirmedResidualDebt={pairwise} "
                f"but unresolvedPairCount={unresolved_pairs} implies {expected_pairwise}"
            )
        if effective != exported + pairwise:
            raise SystemExit(
                f"path {path.get('pathId')} effectivePathResidualDebt={effective} "
                f"but exportedPathResidualDebt={exported} and pairwiseConfirmedResidualDebt={pairwise}"
            )

    for row in comparison_candidates:
        status = str(row.get("comparisonStatus", ""))
        witness_nodes = row.get("witnessNodes", [])
        if not isinstance(witness_nodes, list):
            witness_nodes = []
        witness_count = len(cast(list[Any], witness_nodes))

        if status == "parallel_coherent" and witness_count == 0:
            raise SystemExit(
                f"comparison ({row.get('pathAId')}, {row.get('pathBId')}) is parallel_coherent without witnesses"
            )
        if status == "parallel_unresolved" and witness_count != 0:
            raise SystemExit(
                f"comparison ({row.get('pathAId')}, {row.get('pathBId')}) is parallel_unresolved but has witnesses"
            )


def build_node_stress(
    events: list[JsonDict],
    cocycles: list[JsonDict],
    path_summaries: list[JsonDict],
    defects: list[JsonDict],
) -> list[JsonDict]:
    event_by_node = {str(ev.get("node", "")): ev for ev in events}
    outgoing_edge_credit: Counter[str] = Counter()
    outgoing_edge_debt: Counter[str] = Counter()
    incoming_edge_debt: Counter[str] = Counter()
    outgoing_exported_path_residual: Counter[str] = Counter()
    incoming_exported_path_residual: Counter[str] = Counter()
    outgoing_pairwise_path_residual: Counter[str] = Counter()
    incoming_pairwise_path_residual: Counter[str] = Counter()
    source_defect_count: Counter[str] = Counter()
    affected_by_defect_count: Counter[str] = Counter()

    for row in cocycles:
        src = str(row["src"])
        dst = str(row["dst"])
        outgoing_edge_credit[src] += int(row["transportCredit"])
        outgoing_edge_debt[src] += int(row["defectDebt"])
        incoming_edge_debt[dst] += int(row["defectDebt"])

    for row in path_summaries:
        src = str(row["src"])
        dst = str(row["dst"])
        outgoing_exported_path_residual[src] += int(row["exportedPathResidualDebt"])
        incoming_exported_path_residual[dst] += int(row["exportedPathResidualDebt"])
        outgoing_pairwise_path_residual[src] += int(row["pairwiseConfirmedResidualDebt"])
        incoming_pairwise_path_residual[dst] += int(row["pairwiseConfirmedResidualDebt"])

    for row in defects:
        if is_duplicate_path_defect_row(row):
            continue
        src = str(row.get("src", ""))
        dst = str(row.get("dst", ""))
        if src:
            source_defect_count[src] += 1
        if dst:
            affected_by_defect_count[dst] += 1

    rows: list[JsonDict] = []
    for node, ev in event_by_node.items():
        local_stress = outgoing_edge_debt[node] + incoming_edge_debt[node]
        exported_path_stress = outgoing_exported_path_residual[node] + incoming_exported_path_residual[node]
        pairwise_path_stress = outgoing_pairwise_path_residual[node] + incoming_pairwise_path_residual[node]
        total_stress = local_stress + exported_path_stress + pairwise_path_stress
        rows.append(
            {
                "node": node,
                "module": str(ev.get("module", "")),
                "boundaryClass": str(ev.get("boundaryClass", "")),
                "role": str(ev.get("role", "")),
                "novelty": int(ev.get("novelty", 0)),
                "outgoingEdgeCredit": int(outgoing_edge_credit[node]),
                "outgoingEdgeDebt": int(outgoing_edge_debt[node]),
                "incomingEdgeDebt": int(incoming_edge_debt[node]),
                "localStress": int(local_stress),
                "outgoingExportedPathResidual": int(outgoing_exported_path_residual[node]),
                "incomingExportedPathResidual": int(incoming_exported_path_residual[node]),
                "exportedPathStress": int(exported_path_stress),
                "outgoingPairwisePathResidual": int(outgoing_pairwise_path_residual[node]),
                "incomingPairwisePathResidual": int(incoming_pairwise_path_residual[node]),
                "pairwisePathStress": int(pairwise_path_stress),
                "pathStress": int(exported_path_stress + pairwise_path_stress),
                "sourceDefectCount": int(source_defect_count[node]),
                "affectedByDefectCount": int(affected_by_defect_count[node]),
                "totalStress": int(total_stress),
            }
        )
    rows.sort(key=lambda row: (-row["totalStress"], -row["sourceDefectCount"], row["node"]))
    return rows




def build_module_stress(node_stress: list[JsonDict]) -> list[JsonDict]:
    buckets: dict[str, dict[str, int]] = defaultdict(
        lambda: {
            "nodeCount": 0,
            "totalStress": 0,
            "localStress": 0,
            "exportedPathStress": 0,
            "pairwisePathStress": 0,
            "sourceDefectCount": 0,
            "affectedByDefectCount": 0,
            "outgoingEdgeCredit": 0,
        }
    )
    for row in node_stress:
        mod = str(row["module"])
        bucket = buckets[mod]
        bucket["nodeCount"] += 1
        bucket["totalStress"] += int(row["totalStress"])
        bucket["localStress"] += int(row["localStress"])
        bucket["exportedPathStress"] += int(row["exportedPathStress"])
        bucket["pairwisePathStress"] += int(row["pairwisePathStress"])
        bucket["sourceDefectCount"] += int(row["sourceDefectCount"])
        bucket["affectedByDefectCount"] += int(row["affectedByDefectCount"])
        bucket["outgoingEdgeCredit"] += int(row["outgoingEdgeCredit"])
    rows: list[JsonDict] = [{"module": module, **values} for module, values in buckets.items()]
    rows.sort(key=lambda row: (-row["totalStress"], row["module"]))
    return rows


def markdown_table(headers: list[str], rows: list[list[Any]]) -> str:
    if not rows:
        return "_None._"
    out = ["| " + " | ".join(headers) + " |", "| " + " | ".join(["---"] * len(headers)) + " |"]
    for row in rows:
        out.append("| " + " | ".join(str(x) for x in row) + " |")
    return "\n".join(out)


def strip_internal_fields(row: JsonDict) -> JsonDict:
    return {key: value for key, value in row.items() if not str(key).startswith("_")}


def build_markdown(
    input_dir: Path,
    cocycles_out: Path,
    comparisons_out: Path,
    summary: JsonDict,
    defects_by_kind: list[JsonDict],
    top_nodes: list[JsonDict],
    top_modules: list[JsonDict],
    top_edges: list[JsonDict],
    best_bridges: list[JsonDict],
    top_paths: list[JsonDict],
    top_comparisons: list[JsonDict],
) -> str:
    lines: list[str] = []
    lines.append("# Process Flow Defect Report")
    lines.append("")
    lines.append(f"Input dir: `{input_dir}`")
    lines.append(f"Derived cocycles: `{cocycles_out}`")
    lines.append(f"Derived comparisons: `{comparisons_out}`")
    lines.append("")
    lines.append(
        "Derived analysis over constitutive process-flow artifacts; no analyzer output is fed back into Lean classification."
    )
    lines.append(
        "Path rows are bounded ancestry candidates exported from Lean, not an exhaustive enumeration of all derivational paths in the dependency DAG."
    )
    lines.append(
        "Path debt is reported in two forms: exported residual debt from Lean's bounded path candidates, and pairwise-confirmed residual debt from unresolved comparison pairs recognized by this analyzer."
    )
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Flow edges: `{summary['flowEdgeCount']}`")
    lines.append(f"- Process events: `{summary['processEventCount']}`")
    lines.append(f"- Path candidates: `{summary['pathCandidateCount']}`")
    lines.append(f"- Comparison candidates: `{summary['comparisonCandidateCount']}`")
    lines.append(f"- Unresolved comparison pairs: `{summary['unresolvedComparisonPairCount']}`")
    lines.append(f"- Defect rows: `{summary['defectRowCount']}`")
    lines.append(f"- Cocycle rows: `{summary['flowCocycleCount']}`")
    lines.append(f"- Exported path residual debt total: `{summary['exportedPathResidualDebtTotal']}`")
    lines.append(f"- Pairwise-confirmed residual debt total: `{summary['pairwiseConfirmedResidualDebtTotal']}`")
    lines.append(f"- Effective path residual debt total: `{summary['effectivePathResidualDebtTotal']}`")
    lines.append(f"- Paths with exported residual debt: `{summary['pathsWithExportedResidualDebt']}`")
    lines.append(f"- Paths with pairwise-confirmed residual debt: `{summary['pathsWithPairwiseConfirmedResidualDebt']}`")
    lines.append(f"- Paths with effective residual debt: `{summary['pathsWithEffectiveResidualDebt']}`")
    lines.append("")
    lines.append("## Defects By Kind")
    lines.append("")
    lines.append(
        markdown_table(
            ["Defect", "Count", "Severity Weight"],
            [[row["kind"], row["count"], row["severity"]] for row in defects_by_kind],
        )
    )
    lines.append("")
    lines.append("## Most Stressed Declarations")
    lines.append("")
    lines.append(
        markdown_table(
            ["Node", "Stress", "Local", "ExportedPath", "PairwisePath", "SourceDefects", "Boundary", "Role"],
            [
                [
                    row["node"],
                    row["totalStress"],
                    row["localStress"],
                    row["exportedPathStress"],
                    row["pairwisePathStress"],
                    row["sourceDefectCount"],
                    row["boundaryClass"],
                    row["role"],
                ]
                for row in top_nodes
            ],
        )
    )
    lines.append("")
    lines.append("## Most Stressed Modules")
    lines.append("")
    lines.append(
        markdown_table(
            ["Module", "Nodes", "Stress", "Local", "ExportedPath", "PairwisePath", "SourceDefects", "Credit"],
            [
                [
                    row["module"],
                    row["nodeCount"],
                    row["totalStress"],
                    row["localStress"],
                    row["exportedPathStress"],
                    row["pairwisePathStress"],
                    row["sourceDefectCount"],
                    row["outgoingEdgeCredit"],
                ]
                for row in top_modules
            ],
        )
    )
    lines.append("")
    lines.append("## Most Anomalous Edges")
    lines.append("")
    lines.append(
        markdown_table(
            ["Edge", "Grade", "Debt", "Net", "Role", "Boundary", "Tags"],
            [
                [
                    f"{row['src']} -> {row['dst']}",
                    row["grade"],
                    row["defectDebt"],
                    row["netWeight"],
                    row["inferredRole"],
                    row["inferredBoundary"],
                    ", ".join(row["defectTags"]),
                ]
                for row in top_edges
            ],
        )
    )
    lines.append("")
    lines.append("## Best Low-Defect Bridges")
    lines.append("")
    lines.append(
        markdown_table(
            ["Edge", "Grade", "Credit", "Net", "Role", "Boundary", "Use"],
            [
                [
                    f"{row['src']} -> {row['dst']}",
                    row["grade"],
                    row["transportCredit"],
                    row["netWeight"],
                    row["inferredRole"],
                    row["inferredBoundary"],
                    row["edgeUse"],
                ]
                for row in best_bridges
            ],
        )
    )
    lines.append("")
    lines.append("## Unresolved Comparison Candidates")
    lines.append("")
    lines.append(
        markdown_table(
            ["PathA", "PathB", "Evidence", "RoleMatch", "SupportDiv", "Witnesses", "BestScore"],
            [
                [
                    row["pathAId"],
                    row["pathBId"],
                    row["evidenceClass"],
                    row["roleSignatureMatch"],
                    row["supportDivergence"],
                    len(row["witnessNodes"]),
                    max_witness_score(row),
                ]
                for row in top_comparisons
            ],
        )
    )
    lines.append("")
    lines.append("## Most Stressed Path Candidates")
    lines.append("")
    lines.append(
        markdown_table(
            ["Path", "Steps", "ExportedResidual", "PairwiseResidual", "UnresolvedPairs", "PathDefectCost", "EdgeAccumDebt", "Net"],
            [
                [
                    f"{row['src']} -> {row['dst']}",
                    row["stepCount"],
                    row["exportedPathResidualDebt"],
                    row["pairwiseConfirmedResidualDebt"],
                    row["unresolvedPairCount"],
                    row["pathDefectCost"],
                    row["edgeAccumulatedDebt"],
                    row["netWeight"],
                ]
                for row in top_paths
            ],
        )
    )
    lines.append("")
    return "\n".join(lines)


def build_summary(
    root: Path,
    input_dir: Path,
    flow_edges: list[JsonDict],
    events: list[JsonDict],
    paths: list[JsonDict],
    defects: list[JsonDict],
    cocycles: list[JsonDict],
    comparison_candidates: list[JsonDict],
    path_summaries: list[JsonDict],
) -> JsonDict:
    try:
        input_dir_str = str(input_dir.relative_to(root))
    except ValueError:
        input_dir_str = str(input_dir)

    exported_path_residual_total = sum(int(row["exportedPathResidualDebt"]) for row in path_summaries)
    pairwise_path_residual_total = sum(int(row["pairwiseConfirmedResidualDebt"]) for row in path_summaries)
    effective_path_residual_total = sum(int(row["effectivePathResidualDebt"]) for row in path_summaries)
    paths_with_exported_residual = sum(1 for row in path_summaries if int(row["exportedPathResidualDebt"]) > 0)
    paths_with_pairwise_residual = sum(1 for row in path_summaries if int(row["pairwiseConfirmedResidualDebt"]) > 0)
    paths_with_effective_residual = sum(1 for row in path_summaries if int(row["effectivePathResidualDebt"]) > 0)
    unresolved_pair_count = sum(
        1 for row in comparison_candidates if row["comparisonStatus"] == "parallel_unresolved"
    )

    return {
        "inputDir": input_dir_str,
        "flowEdgeCount": len(flow_edges),
        "processEventCount": len(events),
        "pathCandidateCount": len(paths),
        "comparisonCandidateCount": len(comparison_candidates),
        "unresolvedComparisonPairCount": unresolved_pair_count,
        "defectRowCount": sum(1 for row in defects if not is_duplicate_path_defect_row(row)),
        "flowCocycleCount": len(cocycles),
        "expectedInputSchemaVersion": EXPECTED_INPUT_SCHEMA_VERSION,
        "exportedPathResidualDebtTotal": exported_path_residual_total,
        "pairwiseConfirmedResidualDebtTotal": pairwise_path_residual_total,
        "effectivePathResidualDebtTotal": effective_path_residual_total,
        "pathsWithExportedResidualDebt": paths_with_exported_residual,
        "pathsWithPairwiseConfirmedResidualDebt": paths_with_pairwise_residual,
        "pathsWithEffectiveResidualDebt": paths_with_effective_residual,
    }



def main() -> int:
    args = parse_args()
    root = repo_root()
    input_dir = normalize_user_path(args.input_dir, root / DEFAULT_INPUT_DIR)
    cocycles_out = normalize_user_path(args.cocycles_out, root / DEFAULT_COCYCLES_OUT)
    comparisons_out = normalize_user_path(args.comparisons_out, root / DEFAULT_COMPARISONS_OUT)
    report_out = normalize_user_path(args.report_out, root / DEFAULT_REPORT_OUT)
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)

    flow_edges = load_jsonl(input_dir / "flow-edges.jsonl")
    events = load_jsonl(input_dir / "process-events.jsonl")
    paths = load_jsonl(input_dir / "lawful-path-candidates.jsonl")
    defects = load_jsonl(input_dir / "defects.jsonl")
    print(
        f"[generate_process_flow_report] loaded edges={len(flow_edges)} events={len(events)} "
        f"paths={len(paths)} defects={len(defects)}",
        flush=True,
    )

    if not flow_edges and not events:
        raise SystemExit(f"no process-flow artifacts found under {input_dir}")

    validate_schema(flow_edges, "flow-edges", EXPECTED_INPUT_SCHEMA_VERSION)
    validate_schema(events, "process-events", EXPECTED_INPUT_SCHEMA_VERSION)
    validate_schema(paths, "lawful-path-candidates", EXPECTED_INPUT_SCHEMA_VERSION)
    validate_schema(defects, "defects", EXPECTED_INPUT_SCHEMA_VERSION)
    validate_exporter_contract(paths, defects)

    cocycles, cocycles_by_pair = build_cocycles(flow_edges)
    write_jsonl(cocycles_out, cocycles)
    print(f"[generate_process_flow_report] cocycles={len(cocycles)}", flush=True)
    path_summaries = build_path_summaries(paths, cocycles_by_pair, events)
    print(f"[generate_process_flow_report] path_summaries={len(path_summaries)}", flush=True)
    comparison_candidates, path_summaries = build_comparison_candidates(
        path_summaries,
        events,
        max_shared_sources_per_path=max(0, int(args.max_shared_sources_per_path)),
        max_candidate_paths_per_path=max(0, int(args.max_candidate_paths_per_path)),
        max_comparison_pairs=max(0, int(args.max_comparison_pairs)),
        max_witness_searches=max(0, int(args.max_witness_searches)),
        max_comparison_seconds=max(0.0, float(args.max_comparison_seconds)),
    )
    print(f"[generate_process_flow_report] comparisons={len(comparison_candidates)}", flush=True)
    validate_derived_state(path_summaries, comparison_candidates)
    write_jsonl(comparisons_out, comparison_candidates)
    node_stress = build_node_stress(events, cocycles, path_summaries, defects)
    module_stress = build_module_stress(node_stress)
    print(
        f"[generate_process_flow_report] node_stress={len(node_stress)} module_stress={len(module_stress)}",
        flush=True,
    )

    defects_by_kind_counter: Counter[str] = Counter()
    for row in defects:
        if is_duplicate_path_defect_row(row):
            continue
        defect = row.get("defect", {})
        if not isinstance(defect, dict):
            defect = {}
        typed_defect = cast(JsonDict, defect)
        kind = str(typed_defect.get("kind", "unknown"))
        defects_by_kind_counter[kind] += 1
    defects_by_kind: list[JsonDict] = [
        {"kind": kind, "count": count, "severity": DEFECT_SEVERITY.get(kind, 1)}
        for kind, count in sorted(defects_by_kind_counter.items(), key=lambda item: (-item[1], item[0]))
    ]

    anomalous_edges = sorted(
        [row for row in cocycles if bool(row["anomalous"])],
        key=lambda row: (-row["defectDebt"], row["netWeight"], row["src"], row["dst"]),
    )[: args.top]
    best_bridges = sorted(
        [
            row
            for row in cocycles
            if not bool(row["anomalous"]) and row["inferredBoundary"] in {"bridge", "localInterface"}
        ],
        key=lambda row: (-row["netWeight"], -row["transportCredit"], row["src"], row["dst"]),
    )[: args.top]
    unresolved_comparisons = sorted(
        [row for row in comparison_candidates if row["comparisonStatus"] == "parallel_unresolved"],
        key=lambda row: (
            -row["roleSignatureMatch"],
            row["supportDivergence"],
            row["pathAId"],
            row["pathBId"],
        ),
    )[: args.top]
    stressed_paths = sorted(
        path_summaries,
        key=lambda row: (
            -row["effectivePathResidualDebt"],
            -row["pairwiseConfirmedResidualDebt"],
            -row["unresolvedPairCount"],
            -row["pathDefectCost"],
            row["netWeight"],
            row["src"],
            row["dst"],
        ),
    )[: args.top]
    top_nodes = node_stress[: args.top]
    top_modules = module_stress[: args.top]
    public_stressed_paths = [strip_internal_fields(row) for row in stressed_paths]

    summary = build_summary(
        root,
        input_dir,
        flow_edges,
        events,
        paths,
        defects,
        cocycles,
        comparison_candidates,
        path_summaries,
    )
    payload: JsonDict = {
        "summary": summary,
        "defectsByKind": defects_by_kind,
        "topStressedDeclarations": top_nodes,
        "topStressedModules": top_modules,
        "topAnomalousEdges": anomalous_edges,
        "bestLowDefectBridges": best_bridges,
        "topPathCandidates": public_stressed_paths,
        "topComparisonCandidates": unresolved_comparisons,
    }
    write_json(json_out, payload)
    report_out.parent.mkdir(parents=True, exist_ok=True)
    report_out.write_text(
        build_markdown(
            input_dir,
            cocycles_out,
            comparisons_out,
            summary,
            defects_by_kind,
            top_nodes,
            top_modules,
            anomalous_edges,
            best_bridges,
            stressed_paths,
            unresolved_comparisons,
        ),
        encoding="utf-8",
    )

    print(
        f"[generate_process_flow_report] edges={len(flow_edges)} events={len(events)} "
        f"paths={len(paths)} comparisons={len(comparison_candidates)} defects={len(defects)} cocycles={len(cocycles)} "
        f"wrote {cocycles_out} {comparisons_out} {report_out} {json_out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
