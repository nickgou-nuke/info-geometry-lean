"""Bridge observation normalization and signal extraction."""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, cast

from tools.pathing import normalize_user_path

from .common import (
    DECL_MATCH_RELIABILITY,
    DIAG_PROVENANCE_WEIGHT,
    HEAD_SOURCE_WEIGHT,
    JsonObj,
    clamp01,
    diag_weight,
    load_json,
    make_cluster_key,
    normalize_expr_record,
    parse_uri_or_path,
    relpath_or_self,
    safe_mean,
    source_weight,
    top_counts,
)
from .matching import extract_decl_field, resolve_decl_match, seed_decl_match_context


def collect_bridge_json_paths(raw_inputs: list[str], root: Path) -> list[Path]:
    candidates: list[Path] = []
    seen: set[Path] = set()

    def add_file(p: Path) -> None:
        q = p.resolve()
        if q in seen:
            return
        seen.add(q)
        candidates.append(q)

    def collect_from_path(p: Path) -> None:
        if p.is_file() and p.suffix == ".json":
            add_file(p)
            return
        if p.is_dir():
            for child in sorted(p.rglob("*.json")):
                add_file(child)

    if raw_inputs:
        for item in raw_inputs:
            if any(ch in item for ch in "*?[]"):
                for match in sorted(root.glob(item)):
                    collect_from_path(match)
                continue
            resolved = normalize_user_path(item, root / item)
            collect_from_path(resolved)
        return candidates

    auto_dirs = [
        root / ".artifacts" / "ci" / "compiler_bridge_smoke",
        root / "reports" / "vacuity",
    ]
    auto_files = [
        root / "reports" / "bridge_payload_demo.json",
        root / "reports" / "vacuity" / "bridge_payload_demo.json",
    ]
    for d in auto_dirs:
        collect_from_path(d)
    for f in auto_files:
        collect_from_path(f)
    return candidates


def extract_bridge_payload_objects(data: Any) -> list[JsonObj]:
    found: list[JsonObj] = []

    def visit(node: Any) -> None:
        if isinstance(node, dict):
            node_dict = cast(JsonObj, node)
            if isinstance(node_dict.get("goals"), list) and isinstance(node_dict.get("diagnostics", []), list):
                found.append(node_dict)
            for key in ("result", "payload", "data", "entries", "responses"):
                if key in node_dict:
                    visit(node_dict[key])
        elif isinstance(node, list):
            for item in cast(list[Any], node):
                visit(item)

    visit(data)
    return found


def observe_bridge_payload(
    payload: JsonObj,
    payload_path: Path,
    root: Path,
    match_ctx: dict[str, Any] | None = None,
) -> list[JsonObj]:
    response_meta = payload.get("responseMeta", {})
    session = response_meta.get("sessionId", {}).get("value")
    source_file = parse_uri_or_path(session, root)
    if match_ctx is not None:
        decl_name, decl_match_provenance, decl_match_reliability = resolve_decl_match(
            payload,
            source_file=source_file,
            root=root,
            match_ctx=match_ctx,
        )
    else:
        decl_name, prov = extract_decl_field(payload)
        decl_match_provenance = prov
        decl_match_reliability = DECL_MATCH_RELIABILITY.get(prov, DECL_MATCH_RELIABILITY["unmatched"])

    diag_provs: list[str] = []
    for diag_any in payload.get("diagnostics", []):
        if isinstance(diag_any, dict):
            diag = cast(JsonObj, diag_any)
            prov = diag.get("classificationProvenance")
            if isinstance(prov, str):
                diag_provs.append(prov)

    base_diag_weight = diag_weight(diag_provs)

    def make_observation(
        *,
        surface: str,
        head: Any,
        head_source: Any,
        head_fingerprint: Any,
        expr_record: Any,
    ) -> JsonObj:
        norm = normalize_expr_record(
            expr_record,
            fallback_head=head,
            fallback_source=head_source,
            fallback_fingerprint=head_fingerprint,
        )
        s_weight = source_weight(cast(str | None, norm.get("headSource")))
        obs_conf = clamp01(0.7 * s_weight + 0.3 * base_diag_weight)
        return {
            "payloadFile": relpath_or_self(payload_path, root),
            "sourceFile": source_file,
            "declName": decl_name,
            "declMatchProvenance": decl_match_provenance,
            "declMatchReliability": round(decl_match_reliability, 4),
            "surface": surface,
            "head": norm.get("semanticHead"),
            "headSource": norm.get("headSource"),
            "fingerprint": norm.get("fingerprintV1"),
            "semanticHead": norm.get("semanticHead"),
            "fingerprintV1": norm.get("fingerprintV1"),
            "exprKind": norm.get("exprKind"),
            "appArity": norm.get("appArity"),
            "binderDepth": norm.get("binderDepth"),
            "arityShape": norm.get("arityShape"),
            "binderShape": norm.get("binderShape"),
            "argHeadFingerprints": norm.get("argHeadFingerprints", []),
            "observationConfidence": round(obs_conf, 4),
            "diagnosticProvenance": list(diag_provs),
        }

    out: list[JsonObj] = []
    for goal_any in payload.get("goals", []):
        if not isinstance(goal_any, dict):
            continue
        goal = cast(JsonObj, goal_any)
        out.append(
            make_observation(
                surface="target",
                head=goal.get("targetHead"),
                head_source=goal.get("targetHeadSource", "unavailable"),
                head_fingerprint=goal.get("targetHeadFingerprint"),
                expr_record=goal.get("targetExprFingerprint"),
            )
        )
        for local_any in goal.get("locals", []):
            if not isinstance(local_any, dict):
                continue
            local = cast(JsonObj, local_any)
            out.append(
                make_observation(
                    surface="local",
                    head=local.get("typeHead"),
                    head_source=local.get("typeHeadSource", "unavailable"),
                    head_fingerprint=local.get("typeHeadFingerprint"),
                    expr_record=local.get("typeExprFingerprint"),
                )
            )

    has_validate_decl_shape = any(
        key in payload
        for key in (
            "theoremType",
            "theoremTypeHead",
            "theoremTypeHeadSource",
            "theoremTypeHeadFingerprint",
            "theoremTypeExprFingerprint",
        )
    )
    if has_validate_decl_shape:
        out.append(
            make_observation(
                surface="theoremType",
                head=payload.get("theoremTypeHead"),
                head_source=payload.get("theoremTypeHeadSource", "unavailable"),
                head_fingerprint=payload.get("theoremTypeHeadFingerprint"),
                expr_record=payload.get("theoremTypeExprFingerprint"),
            )
        )

    if match_ctx is not None:
        seed_decl_match_context(match_ctx, out)

    return out


def normalize_bridge_observations(
    observations: list[JsonObj],
) -> tuple[JsonObj, dict[str, JsonObj], dict[str, JsonObj]]:
    semantic_groups: dict[tuple[str, str], JsonObj] = {}
    fingerprint_groups: dict[tuple[str, str], JsonObj] = {}
    shape_groups: dict[tuple[str, str, str, str, str], JsonObj] = {}
    file_signals: dict[str, JsonObj] = defaultdict(
        lambda: {
            "semanticCount": 0,
            "fingerprintCount": 0,
            "confSamples": [],
            "fingerprintCounts": Counter(),
            "semanticHeadCounts": Counter(),
            "exprKindCounts": Counter(),
            "arityShapeCounts": Counter(),
            "binderShapeCounts": Counter(),
            "clusterKeyCounts": Counter(),
        }
    )
    decl_signals: dict[str, JsonObj] = defaultdict(
        lambda: {
            "semanticCount": 0,
            "fingerprintCount": 0,
            "confSamples": [],
            "mappingReliabilitySamples": [],
            "fingerprintCounts": Counter(),
            "semanticHeadCounts": Counter(),
            "exprKindCounts": Counter(),
            "arityShapeCounts": Counter(),
            "binderShapeCounts": Counter(),
            "clusterKeyCounts": Counter(),
            "matchProvenanceCounts": Counter(),
            "sourceFiles": set(),
            "surfaceCounts": Counter(),
        }
    )

    for obs in observations:
        surface = str(obs.get("surface") or "unknown")
        head = obs.get("semanticHead") or obs.get("head")
        source = str(obs.get("headSource") or "unavailable")
        fingerprint = obs.get("fingerprintV1") or obs.get("fingerprint")
        expr_kind_any = obs.get("exprKind")
        expr_kind = expr_kind_any if isinstance(expr_kind_any, str) and expr_kind_any else "unknown"
        arity_shape_any = obs.get("arityShape")
        arity_shape_value = arity_shape_any if isinstance(arity_shape_any, str) and arity_shape_any else "arity:?"
        binder_shape_any = obs.get("binderShape")
        binder_shape_value = (
            binder_shape_any if isinstance(binder_shape_any, str) and binder_shape_any else "binder:?"
        )
        source_file = obs.get("sourceFile")
        decl_name = obs.get("declName")
        diag_provs = [str(p) for p in obs.get("diagnosticProvenance", [])]
        cluster_key = make_cluster_key(
            fingerprint_v1=fingerprint if isinstance(fingerprint, str) else None,
            semantic_head=head if isinstance(head, str) else None,
            expr_kind=expr_kind,
            arity_shape_value=arity_shape_value,
            binder_shape_value=binder_shape_value,
        )

        conf_any = obs.get("observationConfidence")
        if isinstance(conf_any, (int, float)):
            obs_conf = clamp01(float(conf_any))
        else:
            s_weight = source_weight(source)
            d_weight = diag_weight(diag_provs)
            obs_conf = clamp01(0.7 * s_weight + 0.3 * d_weight)

        if source_file:
            fstats = file_signals[source_file]
            fstats["confSamples"].append(obs_conf)
            if source == "exprSemantic" and head:
                fstats["semanticCount"] += 1
            if source == "exprSemantic" and fingerprint:
                fstats["fingerprintCount"] += 1
            if source == "exprSemantic" and isinstance(head, str) and head:
                cast(Counter[str], fstats["semanticHeadCounts"])[head] += 1
            if source == "exprSemantic" and isinstance(fingerprint, str) and fingerprint:
                cast(Counter[str], fstats["fingerprintCounts"])[fingerprint] += 1
            if source == "exprSemantic" and expr_kind:
                cast(Counter[str], fstats["exprKindCounts"])[expr_kind] += 1
            if source == "exprSemantic" and arity_shape_value:
                cast(Counter[str], fstats["arityShapeCounts"])[arity_shape_value] += 1
            if source == "exprSemantic" and binder_shape_value:
                cast(Counter[str], fstats["binderShapeCounts"])[binder_shape_value] += 1
            if source == "exprSemantic":
                cast(Counter[str], fstats["clusterKeyCounts"])[cluster_key] += 1

        if isinstance(decl_name, str) and decl_name:
            dstats = decl_signals[decl_name]
            decl_match_prov_any = obs.get("declMatchProvenance")
            decl_match_prov = decl_match_prov_any if isinstance(decl_match_prov_any, str) else "unmatched"
            decl_rel_any = obs.get("declMatchReliability")
            if isinstance(decl_rel_any, (int, float)):
                decl_rel = clamp01(float(decl_rel_any))
            else:
                decl_rel = DECL_MATCH_RELIABILITY.get(decl_match_prov, DECL_MATCH_RELIABILITY["unmatched"])
            effective_conf = clamp01(obs_conf * max(0.2, decl_rel))

            dstats["confSamples"].append(effective_conf)
            dstats["mappingReliabilitySamples"].append(decl_rel)
            cast(Counter[str], dstats["matchProvenanceCounts"])[decl_match_prov] += 1
            cast(Counter[str], dstats["surfaceCounts"])[surface] += 1
            if source_file:
                cast(set[str], dstats["sourceFiles"]).add(source_file)
            if source == "exprSemantic" and head:
                dstats["semanticCount"] += 1
            if source == "exprSemantic" and fingerprint:
                dstats["fingerprintCount"] += 1
            if source == "exprSemantic" and isinstance(head, str) and head:
                cast(Counter[str], dstats["semanticHeadCounts"])[head] += 1
            if source == "exprSemantic" and isinstance(fingerprint, str) and fingerprint:
                cast(Counter[str], dstats["fingerprintCounts"])[fingerprint] += 1
            if source == "exprSemantic" and expr_kind:
                cast(Counter[str], dstats["exprKindCounts"])[expr_kind] += 1
            if source == "exprSemantic" and arity_shape_value:
                cast(Counter[str], dstats["arityShapeCounts"])[arity_shape_value] += 1
            if source == "exprSemantic" and binder_shape_value:
                cast(Counter[str], dstats["binderShapeCounts"])[binder_shape_value] += 1
            if source == "exprSemantic":
                cast(Counter[str], dstats["clusterKeyCounts"])[cluster_key] += 1

        if source == "exprSemantic" and isinstance(head, str) and head:
            gkey = (surface, head)
            group = semantic_groups.setdefault(
                gkey,
                {
                    "surface": surface,
                    "head": head,
                    "count": 0,
                    "files": set(),
                    "fingerprints": Counter(),
                    "diagProvenance": Counter(),
                    "confSamples": [],
                },
            )
            group["count"] += 1
            if source_file:
                group["files"].add(source_file)
            if isinstance(fingerprint, str) and fingerprint:
                group["fingerprints"][fingerprint] += 1
            for prov in diag_provs:
                group["diagProvenance"][prov] += 1
            group["confSamples"].append(obs_conf)

        if source == "exprSemantic" and isinstance(fingerprint, str) and fingerprint:
            fkey = (surface, fingerprint)
            group2 = fingerprint_groups.setdefault(
                fkey,
                {
                    "surface": surface,
                    "fingerprint": fingerprint,
                    "count": 0,
                    "heads": Counter(),
                    "files": set(),
                    "diagProvenance": Counter(),
                    "confSamples": [],
                },
            )
            group2["count"] += 1
            if isinstance(head, str) and head:
                group2["heads"][head] += 1
            if source_file:
                group2["files"].add(source_file)
            for prov in diag_provs:
                group2["diagProvenance"][prov] += 1
            group2["confSamples"].append(obs_conf)

        if source == "exprSemantic":
            shape_key = (
                str(fingerprint or "none"),
                str(head or "none"),
                expr_kind,
                arity_shape_value,
                binder_shape_value,
            )
            shape_group = shape_groups.setdefault(
                shape_key,
                {
                    "fingerprintV1": shape_key[0],
                    "semanticHead": shape_key[1],
                    "exprKind": shape_key[2],
                    "arityShape": shape_key[3],
                    "binderShape": shape_key[4],
                    "clusterKey": cluster_key,
                    "count": 0,
                    "files": set(),
                    "decls": set(),
                    "diagProvenance": Counter(),
                    "confSamples": [],
                    "surfaceCounts": Counter(),
                },
            )
            shape_group["count"] += 1
            if isinstance(source_file, str) and source_file:
                shape_group["files"].add(source_file)
            if isinstance(decl_name, str) and decl_name:
                shape_group["decls"].add(decl_name)
            for prov in diag_provs:
                shape_group["diagProvenance"][prov] += 1
            shape_group["confSamples"].append(obs_conf)
            shape_group["surfaceCounts"][surface] += 1

    semantic_out: list[JsonObj] = []
    for group in semantic_groups.values():
        diag_hist = dict(group["diagProvenance"])
        avg_diag = safe_mean(
            [DIAG_PROVENANCE_WEIGHT.get(k, DIAG_PROVENANCE_WEIGHT["fallback"]) for k in group["diagProvenance"]],
            default=DIAG_PROVENANCE_WEIGHT["fallback"],
        )
        semantic_out.append(
            {
                "surface": group["surface"],
                "head": group["head"],
                "count": group["count"],
                "files": sorted(group["files"]),
                "fingerprints": group["fingerprints"].most_common(),
                "groupConfidence": round(safe_mean(group["confSamples"], default=0.0), 4),
                "confidenceProvenance": [
                    {
                        "signal": "headSource",
                        "weight": HEAD_SOURCE_WEIGHT["exprSemantic"],
                        "evidence": "exprSemantic",
                    },
                    {
                        "signal": "diagnosticProvenance",
                        "weight": round(avg_diag, 4),
                        "evidence": json.dumps(diag_hist, sort_keys=True),
                    },
                ],
            }
        )

    fingerprint_out: list[JsonObj] = []
    for group in fingerprint_groups.values():
        diag_hist = dict(group["diagProvenance"])
        avg_diag = safe_mean(
            [DIAG_PROVENANCE_WEIGHT.get(k, DIAG_PROVENANCE_WEIGHT["fallback"]) for k in group["diagProvenance"]],
            default=DIAG_PROVENANCE_WEIGHT["fallback"],
        )
        fingerprint_out.append(
            {
                "surface": group["surface"],
                "fingerprint": group["fingerprint"],
                "count": group["count"],
                "heads": group["heads"].most_common(),
                "files": sorted(group["files"]),
                "groupConfidence": round(safe_mean(group["confSamples"], default=0.0), 4),
                "confidenceProvenance": [
                    {
                        "signal": "headSource",
                        "weight": HEAD_SOURCE_WEIGHT["exprSemantic"],
                        "evidence": "exprSemantic",
                    },
                    {
                        "signal": "diagnosticProvenance",
                        "weight": round(avg_diag, 4),
                        "evidence": json.dumps(diag_hist, sort_keys=True),
                    },
                ],
            }
        )

    shape_out: list[JsonObj] = []
    for group in shape_groups.values():
        diag_hist = dict(group["diagProvenance"])
        avg_diag = safe_mean(
            [DIAG_PROVENANCE_WEIGHT.get(k, DIAG_PROVENANCE_WEIGHT["fallback"]) for k in group["diagProvenance"]],
            default=DIAG_PROVENANCE_WEIGHT["fallback"],
        )
        shape_out.append(
            {
                "clusterKey": group["clusterKey"],
                "fingerprintV1": group["fingerprintV1"],
                "semanticHead": group["semanticHead"],
                "exprKind": group["exprKind"],
                "arityShape": group["arityShape"],
                "binderShape": group["binderShape"],
                "count": group["count"],
                "files": sorted(group["files"]),
                "declarations": sorted(group["decls"]),
                "surfaceCounts": dict(group["surfaceCounts"]),
                "groupConfidence": round(safe_mean(group["confSamples"], default=0.0), 4),
                "confidenceProvenance": [
                    {
                        "signal": "headSource",
                        "weight": HEAD_SOURCE_WEIGHT["exprSemantic"],
                        "evidence": "exprSemantic",
                    },
                    {
                        "signal": "diagnosticProvenance",
                        "weight": round(avg_diag, 4),
                        "evidence": json.dumps(diag_hist, sort_keys=True),
                    },
                ],
            }
        )

    semantic_out.sort(key=lambda x: (-x["count"], -x["groupConfidence"], x["surface"], x["head"]))
    fingerprint_out.sort(key=lambda x: (-x["count"], -x["groupConfidence"], x["surface"], x["fingerprint"]))
    shape_out.sort(
        key=lambda x: (
            -x["count"],
            -x["groupConfidence"],
            str(x.get("exprKind") or ""),
            str(x.get("semanticHead") or ""),
            str(x.get("fingerprintV1") or ""),
        )
    )

    file_signal_out: dict[str, JsonObj] = {}
    for fpath, stats in file_signals.items():
        file_signal_out[fpath] = {
            "semanticCount": stats["semanticCount"],
            "fingerprintCount": stats["fingerprintCount"],
            "avgConfidence": round(safe_mean(stats["confSamples"], default=0.0), 4),
            "fingerprintCounts": top_counts(cast(Counter[str], stats["fingerprintCounts"])),
            "semanticHeadCounts": top_counts(cast(Counter[str], stats["semanticHeadCounts"])),
            "exprKindCounts": top_counts(cast(Counter[str], stats["exprKindCounts"])),
            "arityShapeCounts": top_counts(cast(Counter[str], stats["arityShapeCounts"])),
            "binderShapeCounts": top_counts(cast(Counter[str], stats["binderShapeCounts"])),
            "clusterKeys": top_counts(cast(Counter[str], stats["clusterKeyCounts"])),
        }

    decl_signal_out: dict[str, JsonObj] = {}
    for decl, stats in decl_signals.items():
        decl_signal_out[decl] = {
            "semanticCount": stats["semanticCount"],
            "fingerprintCount": stats["fingerprintCount"],
            "avgConfidence": round(safe_mean(stats["confSamples"], default=0.0), 4),
            "avgMappingReliability": round(safe_mean(stats["mappingReliabilitySamples"], default=0.0), 4),
            "fingerprintCounts": top_counts(cast(Counter[str], stats["fingerprintCounts"])),
            "semanticHeadCounts": top_counts(cast(Counter[str], stats["semanticHeadCounts"])),
            "exprKindCounts": top_counts(cast(Counter[str], stats["exprKindCounts"])),
            "arityShapeCounts": top_counts(cast(Counter[str], stats["arityShapeCounts"])),
            "binderShapeCounts": top_counts(cast(Counter[str], stats["binderShapeCounts"])),
            "clusterKeys": top_counts(cast(Counter[str], stats["clusterKeyCounts"])),
            "matchProvenanceCounts": dict(cast(Counter[str], stats["matchProvenanceCounts"])),
            "sourceFiles": sorted(cast(set[str], stats["sourceFiles"])),
            "surfaceCounts": dict(cast(Counter[str], stats["surfaceCounts"])),
        }

    summary: JsonObj = {
        "payloadObservationCount": len(observations),
        "semanticHeadGroupCount": len(semantic_out),
        "fingerprintGroupCount": len(fingerprint_out),
        "shapeClusterGroupCount": len(shape_out),
        "declarationSignalCount": len(decl_signal_out),
        "declarationMatchProvenance": dict(
            Counter(str(obs.get("declMatchProvenance") or "unmatched") for obs in observations)
        ),
        "semanticHeadGroups": semantic_out,
        "fingerprintGroups": fingerprint_out,
        "shapeClusters": shape_out,
    }
    return summary, file_signal_out, decl_signal_out
