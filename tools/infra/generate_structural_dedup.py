#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import (
        default_decl_structure_file,
        default_source_sink_bipartite_file,
        normalize_user_path,
        repo_root,
    )
else:
    from tools.pathing import (
        default_decl_structure_file,
        default_source_sink_bipartite_file,
        normalize_user_path,
        repo_root,
    )


DEFAULT_STRUCTURE = str(default_decl_structure_file().relative_to(repo_root()))
DEFAULT_BIPARTITE = str(default_source_sink_bipartite_file().relative_to(repo_root()))
DEFAULT_JSON_OUT = "reports/dag/structural-dedup.json"
DEFAULT_MD_OUT = "reports/dag/structural-dedup.md"

SCORE_SAME_BUNDLE = 4.0
SCORE_SAME_CORRIDOR = 3.0
SCORE_COMPONENT_JACCARD = 2.0
SCORE_SINK_FAMILY_JACCARD = 2.0
SCORE_MOTIF_JACCARD = 1.0


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Generate a native-structure-backed quotient-candidate report over sink surfaces, "
            "hydrated carrier shadows, and repeated assumption packets."
        )
    )
    ap.add_argument("--structure", default=DEFAULT_STRUCTURE)
    ap.add_argument("--bipartite", default=DEFAULT_BIPARTITE)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--shadow-threshold", type=float, default=5.0)
    ap.add_argument("--top", type=int, default=25)
    return ap.parse_args()


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def ordered_unique(items: list[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        if not item or item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def jaccard(left: list[str] | set[str], right: list[str] | set[str]) -> float:
    left_set = {str(x) for x in left if str(x)}
    right_set = {str(x) for x in right if str(x)}
    if not left_set or not right_set:
        return 0.0
    return len(left_set & right_set) / len(left_set | right_set)


def parse_structure(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in payload.get("components", []):
        if not isinstance(row, dict):
            continue
        component_id = str(row.get("componentId", ""))
        if component_id:
            out[component_id] = row
    return out


def component_repr(component_id: str, components_by_id: dict[str, dict[str, Any]]) -> str:
    row = components_by_id.get(component_id, {})
    return str(row.get("representative", component_id))


def sort_component_ids(component_ids: set[str], components_by_id: dict[str, dict[str, Any]]) -> list[str]:
    return sorted(component_ids, key=lambda cid: (component_repr(cid, components_by_id), cid))


def normalize_hydrated_rows(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in payload.get("hydrated_nodes", []):
        if not isinstance(row, dict):
            continue
        hydrated_id = str(row.get("hydrated_id", ""))
        if hydrated_id:
            out[hydrated_id] = row
    return out


def normalize_atomic_rows(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in payload.get("atomic_nodes", []):
        if not isinstance(row, dict):
            continue
        atomic_id = str(row.get("atomic_id", ""))
        if atomic_id:
            out[atomic_id] = row
    return out


def normalize_sink_rows(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in payload.get("sink_nodes", []):
        if not isinstance(row, dict):
            continue
        name = str(row.get("name", ""))
        if name:
            out[name] = row
    return out


def parse_incidence(payload: dict[str, Any]) -> dict[str, set[str]]:
    usage: dict[str, set[str]] = defaultdict(set)
    for row in payload.get("incidence_edges", []):
        if not isinstance(row, dict):
            continue
        if str(row.get("role", "")) != "supports":
            continue
        if str(row.get("projection_kind", "")) != "node_support":
            continue
        atomic_id = str(row.get("atomic_id", ""))
        hydrated_id = str(row.get("hydrated_id", ""))
        if atomic_id and hydrated_id:
            usage[atomic_id].add(hydrated_id)
    return usage


def normalize_motif_signatures(value: Any) -> list[str]:
    out: list[str] = []
    if isinstance(value, list):
        for item in value:
            if isinstance(item, str):
                if item:
                    out.append(item)
            elif isinstance(item, dict):
                signature = str(item.get("signature", ""))
                if signature:
                    out.append(signature)
    return ordered_unique(out)


def short_name(name: str) -> str:
    return name.rsplit('.', 1)[-1]


def role_rank(role: str) -> int:
    return {
        "constructive_source": 0,
        "transport_only": 1,
        "consumer_sink": 2,
    }.get(role, -1)


def choose_canonical_sink(sink_names: list[str], sink_by_name: dict[str, dict[str, Any]]) -> str:
    def rank(name: str) -> tuple[Any, ...]:
        row = sink_by_name.get(name, {})
        return (
            int(row.get("severity", 99) or 99),
            len(short_name(name)),
            -int(row.get("flow_in_degree", 0) or 0),
            name,
        )

    return min(sink_names, key=rank)


def dedup_family_id(atomic_id: str, sink_names: list[str]) -> str:
    digest = hashlib.sha1((atomic_id + '|' + '|'.join(sorted(sink_names))).encode('utf-8')).hexdigest()[:12]
    return f"family:{digest}"


def shared_decl_stem(sink_names: list[str]) -> str:
    if len(sink_names) < 2:
        return ""
    stem = os.path.commonprefix(sink_names)
    if "." in stem:
        stem = stem[: stem.rfind(".") + 1] if stem.endswith(".") else stem
    if len(stem) < 40:
        return ""
    return stem


def classify_dedup_family(
    canonical_sink: str,
    sink_names: list[str],
    member_rows: list[dict[str, Any]],
) -> dict[str, str]:
    member_modules = ordered_unique([str(row.get("module", "")) for row in member_rows if str(row.get("module", ""))])
    same_module = len(member_modules) == 1
    stem = shared_decl_stem(sink_names)
    short_names = [short_name(name) for name in sink_names]
    alias_like_suffixes = any(
        token in short
        for short in short_names
        for token in ("_iff_", "_of_", "_eq_", "_le_", "_ge_")
    )
    if same_module and stem and alias_like_suffixes:
        return {
            "relation_subtype": "compatibility_alias_candidate",
            "recommended_action": "review_as_alias_family",
            "shared_name_stem": stem,
        }
    return {
        "relation_subtype": "true_dedup_candidate",
        "recommended_action": "review_for_contraction",
        "shared_name_stem": "",
    }


def build_dedup_families(
    atomic_by_id: dict[str, dict[str, Any]],
    sink_by_name: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for atomic_id, atomic in atomic_by_id.items():
        sink_names = ordered_unique([str(x) for x in atomic.get("sink_names", []) if str(x)])
        if len(sink_names) < 2:
            continue
        canonical_sink = choose_canonical_sink(sink_names, sink_by_name)
        canonical_row = sink_by_name.get(canonical_sink, {})
        family_score = round(
            8.0 * max(0, len(sink_names) - 1)
            + 1.0 * int(atomic.get("path_multiplicity", 0) or 0)
            + 0.05 * float(atomic.get("compression_potential", 0.0) or 0.0),
            4,
        )
        member_rows = [sink_by_name.get(name, {}) for name in sink_names]
        family_classification = classify_dedup_family(canonical_sink, sink_names, member_rows)
        rows.append({
            "family_id": dedup_family_id(atomic_id, sink_names),
            "relation_type": "true_dedup_candidate",
            "relation_subtype": family_classification["relation_subtype"],
            "recommended_action": family_classification["recommended_action"],
            "shared_name_stem": family_classification["shared_name_stem"],
            "candidate_canonical_endpoint": canonical_sink,
            "candidate_canonical_module": str(canonical_row.get("module", canonical_sink.rsplit('.', 1)[0] if '.' in canonical_sink else canonical_sink)),
            "member_sinks": sink_names,
            "member_modules": ordered_unique([str(row.get("module", "")) for row in member_rows if str(row.get("module", ""))]),
            "member_count": len(sink_names),
            "shared_minimal_source_bundle": atomic_id,
            "shared_source_bundle": [str(x) for x in atomic.get("source_bundle", []) if str(x)],
            "shared_sink_family": ordered_unique([str(x) for x in atomic.get("sink_modules", []) if str(x)]),
            "shared_top_corridor_representatives": [str(x) for x in atomic.get("native_component_representatives", []) if str(x)],
            "shared_native_component_ids": [str(x) for x in atomic.get("native_component_ids", []) if str(x)],
            "shared_native_root_witnesses": [str(x) for x in atomic.get("native_root_witnesses", []) if str(x)],
            "motif_signature": str(atomic.get("motif_signature", "")),
            "path_multiplicity": int(atomic.get("path_multiplicity", 0) or 0),
            "compression_potential": float(atomic.get("compression_potential", 0.0) or 0.0),
            "family_score": family_score,
            "member_sink_metadata": [
                {
                    "name": name,
                    "category": str(sink_by_name.get(name, {}).get("category", "unknown")),
                    "burn_down_rank": int(sink_by_name.get(name, {}).get("burn_down_rank", 0) or 0),
                    "flow_in_degree": int(sink_by_name.get(name, {}).get("flow_in_degree", 0) or 0),
                    "severity": int(sink_by_name.get(name, {}).get("severity", 0) or 0),
                }
                for name in sink_names
            ],
        })

    rows.sort(
        key=lambda row: (
            -float(row["family_score"]),
            -int(row["member_count"]),
            row["candidate_canonical_endpoint"],
        )
    )
    return rows


def shadow_pair_features(
    left: dict[str, Any],
    right: dict[str, Any],
    components_by_id: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    left_components = {str(x) for x in left.get("native_component_ids", []) if str(x)}
    right_components = {str(x) for x in right.get("native_component_ids", []) if str(x)}
    left_corridors = [str(x) for x in left.get("top_native_corridor_representatives", []) if str(x)]
    right_corridors = [str(x) for x in right.get("top_native_corridor_representatives", []) if str(x)]
    left_sink_family = [str(x) for x in left.get("canonical_downstream_sink_family", []) if str(x)]
    right_sink_family = [str(x) for x in right.get("canonical_downstream_sink_family", []) if str(x)]
    left_motifs = normalize_motif_signatures(left.get("path_motif_signatures", []))
    right_motifs = normalize_motif_signatures(right.get("path_motif_signatures", []))

    same_bundle = (
        bool(left.get("minimal_source_bundle"))
        and str(left.get("minimal_source_bundle")) == str(right.get("minimal_source_bundle"))
    )
    same_corridor = bool(left_corridors) and left_corridors == right_corridors
    component_j = jaccard(left_components, right_components)
    sink_family_j = jaccard(left_sink_family, right_sink_family)
    motif_j = jaccard(left_motifs, right_motifs)

    score = round(
        (SCORE_SAME_BUNDLE if same_bundle else 0.0)
        + (SCORE_SAME_CORRIDOR if same_corridor else 0.0)
        + SCORE_COMPONENT_JACCARD * component_j
        + SCORE_SINK_FAMILY_JACCARD * sink_family_j
        + SCORE_MOTIF_JACCARD * motif_j,
        4,
    )

    shared_components = sort_component_ids(left_components & right_components, components_by_id)
    shared_corridors = [item for item in left_corridors if item in set(right_corridors)]
    shared_motifs = [item for item in left_motifs if item in set(right_motifs)]
    return {
        "left_hydrated_id": str(left.get("hydrated_id", "")),
        "left_module": str(left.get("module", left.get("hydrated_id", ""))),
        "left_role_class": str(left.get("sink_role", "unknown")),
        "right_hydrated_id": str(right.get("hydrated_id", "")),
        "right_module": str(right.get("module", right.get("hydrated_id", ""))),
        "right_role_class": str(right.get("sink_role", "unknown")),
        "score": score,
        "same_minimal_source_bundle": same_bundle,
        "minimal_source_bundle": str(left.get("minimal_source_bundle", "")) if same_bundle else "",
        "same_top_native_corridor": same_corridor,
        "component_jaccard": round(component_j, 4),
        "sink_family_jaccard": round(sink_family_j, 4),
        "motif_jaccard": round(motif_j, 4),
        "shared_sink_family": [item for item in left_sink_family if item in set(right_sink_family)],
        "shared_top_corridor_representatives": shared_corridors,
        "shared_native_component_ids": shared_components,
        "shared_native_component_representatives": [component_repr(component_id, components_by_id) for component_id in shared_components],
        "shared_motif_signatures": shared_motifs,
        "shared_top_root_witness": (
            str(left.get("top_root_witness", ""))
            if str(left.get("top_root_witness", "")) and str(left.get("top_root_witness", "")) == str(right.get("top_root_witness", ""))
            else ""
        ),
    }


def build_shadow_relations(
    hydrated_by_id: dict[str, dict[str, Any]],
    components_by_id: dict[str, dict[str, Any]],
    shadow_threshold: float,
) -> list[dict[str, Any]]:
    hydrated_ids = sorted(hydrated_by_id.keys())
    rows: list[dict[str, Any]] = []
    for idx, left_id in enumerate(hydrated_ids):
        for right_id in hydrated_ids[idx + 1:]:
            left = hydrated_by_id[left_id]
            right = hydrated_by_id[right_id]
            if str(left.get("sink_role", "")) == str(right.get("sink_role", "")):
                continue
            features = shadow_pair_features(left, right, components_by_id)
            if float(features["score"]) < shadow_threshold:
                continue
            if not (
                bool(features["same_minimal_source_bundle"])
                or bool(features["same_top_native_corridor"])
                or float(features["component_jaccard"]) >= 0.5
                or float(features["motif_jaccard"]) >= 0.5
            ):
                continue

            left_role = str(features["left_role_class"])
            right_role = str(features["right_role_class"])
            if role_rank(left_role) <= role_rank(right_role):
                upstream_prefix, downstream_prefix = "left", "right"
            else:
                upstream_prefix, downstream_prefix = "right", "left"

            shared_packet_signature = features["minimal_source_bundle"]
            if not shared_packet_signature and features["shared_top_corridor_representatives"]:
                shared_packet_signature = " -> ".join(features["shared_top_corridor_representatives"][:4])
            if not shared_packet_signature and features["shared_motif_signatures"]:
                shared_packet_signature = features["shared_motif_signatures"][0]

            explanation_parts = [
                f"role mismatch {features[f'{upstream_prefix}_role_class']} -> {features[f'{downstream_prefix}_role_class']}",
            ]
            if features["same_minimal_source_bundle"]:
                explanation_parts.append("same source bundle")
            if features["same_top_native_corridor"]:
                explanation_parts.append("same top corridor")
            if float(features["component_jaccard"]) >= 0.5:
                explanation_parts.append("high native component overlap")
            if float(features["motif_jaccard"]) >= 0.5:
                explanation_parts.append("aligned motif packet")

            rows.append({
                "relation_type": "shadow_relation",
                "upstream_hydrated_id": str(features[f"{upstream_prefix}_hydrated_id"]),
                "upstream_module": str(features[f"{upstream_prefix}_module"]),
                "upstream_role_class": str(features[f"{upstream_prefix}_role_class"]),
                "downstream_hydrated_id": str(features[f"{downstream_prefix}_hydrated_id"]),
                "downstream_module": str(features[f"{downstream_prefix}_module"]),
                "downstream_role_class": str(features[f"{downstream_prefix}_role_class"]),
                "score": float(features["score"]),
                "shared_packet_signature": shared_packet_signature,
                "same_minimal_source_bundle": bool(features["same_minimal_source_bundle"]),
                "same_top_native_corridor": bool(features["same_top_native_corridor"]),
                "component_jaccard": float(features["component_jaccard"]),
                "sink_family_jaccard": float(features["sink_family_jaccard"]),
                "motif_jaccard": float(features["motif_jaccard"]),
                "shared_sink_family": features["shared_sink_family"],
                "shared_top_corridor_representatives": features["shared_top_corridor_representatives"],
                "shared_native_component_ids": features["shared_native_component_ids"],
                "shared_native_component_representatives": features["shared_native_component_representatives"],
                "shared_motif_signatures": features["shared_motif_signatures"],
                "shared_top_root_witness": features["shared_top_root_witness"],
                "why_transport_not_duplication": "; ".join(explanation_parts),
            })

    rows.sort(
        key=lambda row: (
            -float(row["score"]),
            row["upstream_module"],
            row["downstream_module"],
        )
    )
    return rows


def build_assumption_packet_reuse(
    atomic_by_id: dict[str, dict[str, Any]],
    hydrated_by_id: dict[str, dict[str, Any]],
    usage_by_atomic: dict[str, set[str]],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for atomic_id, atomic in atomic_by_id.items():
        carriers = sorted(
            usage_by_atomic.get(atomic_id, set()),
            key=lambda hydrated_id: str(hydrated_by_id.get(hydrated_id, {}).get("module", hydrated_id)),
        )
        carrier_modules = [
            str(hydrated_by_id.get(hydrated_id, {}).get("module", hydrated_id))
            for hydrated_id in carriers
        ]
        sink_names = ordered_unique([str(x) for x in atomic.get("sink_names", []) if str(x)])
        sink_modules = ordered_unique([str(x) for x in atomic.get("sink_modules", []) if str(x)])
        carrier_count = len(carriers)
        sink_name_count = len(sink_names)
        if carrier_count < 2 and sink_name_count < 2:
            continue
        reuse_score = round(
            6.0 * max(0, carrier_count - 1)
            + 3.0 * max(0, sink_name_count - 1)
            + 0.5 * int(atomic.get("path_multiplicity", 0) or 0)
            + 0.05 * float(atomic.get("compression_potential", 0.0) or 0.0),
            4,
        )
        source_modules = ordered_unique([str(x) for x in atomic.get("source_modules", []) if str(x)])
        suggested_upstream_home = source_modules[0] if len(source_modules) == 1 else (source_modules[0] if source_modules else "")
        rows.append({
            "atomic_id": atomic_id,
            "reuse_score": reuse_score,
            "carrier_count": carrier_count,
            "carrier_hydrated_ids": carriers,
            "carrier_modules": carrier_modules,
            "sink_name_count": sink_name_count,
            "sink_names": sink_names,
            "sink_modules": sink_modules,
            "source_modules": source_modules,
            "source_bundle": [str(x) for x in atomic.get("source_bundle", []) if str(x)],
            "motif_signature": str(atomic.get("motif_signature", "")),
            "native_component_representatives": [str(x) for x in atomic.get("native_component_representatives", []) if str(x)],
            "path_multiplicity": int(atomic.get("path_multiplicity", 0) or 0),
            "compression_potential": float(atomic.get("compression_potential", 0.0) or 0.0),
            "suggested_upstream_home": suggested_upstream_home,
        })

    rows.sort(
        key=lambda row: (
            -float(row["reuse_score"]),
            -int(row["carrier_count"]),
            -int(row["sink_name_count"]),
            row["atomic_id"],
        )
    )
    return rows


def build_summary(
    dedup_families: list[dict[str, Any]],
    shadow_relations: list[dict[str, Any]],
    assumption_packet_reuse: list[dict[str, Any]],
    sink_by_name: dict[str, dict[str, Any]],
    hydrated_by_id: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    return {
        "sink_surface_count": len(sink_by_name),
        "hydrated_carrier_count": len(hydrated_by_id),
        "dedup_family_count": len(dedup_families),
        "shadow_relation_count": len(shadow_relations),
        "reused_packet_count": len(assumption_packet_reuse),
        "top_dedup_family_score": round(float(dedup_families[0]["family_score"]), 4) if dedup_families else 0.0,
        "top_shadow_score": round(float(shadow_relations[0]["score"]), 4) if shadow_relations else 0.0,
    }


def render_markdown(
    summary: dict[str, Any],
    dedup_families: list[dict[str, Any]],
    shadow_relations: list[dict[str, Any]],
    assumption_packet_reuse: list[dict[str, Any]],
    structure_path: Path,
    bipartite_path: Path,
    shadow_threshold: float,
    top: int,
) -> str:
    lines: list[str] = []
    lines.append("# Structural Dedup")
    lines.append("")
    lines.append(
        "This report separates true sink-surface dedup candidates from shadow transport relations so repeated packets are not confused with source-to-consumer reflections."
    )
    lines.append("")
    lines.append(f"- structure: `{structure_path}`")
    lines.append(f"- bipartite artifact: `{bipartite_path}`")
    lines.append(f"- shadow threshold: `{shadow_threshold}`")
    lines.append("")
    lines.append("## Summary")
    lines.append(f"- sink surfaces: `{summary.get('sink_surface_count', 0)}`")
    lines.append(f"- hydrated carriers: `{summary.get('hydrated_carrier_count', 0)}`")
    lines.append(f"- dedup families: `{summary.get('dedup_family_count', 0)}`")
    lines.append(f"- shadow relations: `{summary.get('shadow_relation_count', 0)}`")
    lines.append(f"- reused assumption packets: `{summary.get('reused_packet_count', 0)}`")
    lines.append(f"- top dedup family score: `{summary.get('top_dedup_family_score', 0.0)}`")
    lines.append(f"- top shadow score: `{summary.get('top_shadow_score', 0.0)}`")
    lines.append("")
    lines.append("## Dedup Families")
    if not dedup_families:
        lines.append("- none")
        lines.append("")
    else:
        for row in dedup_families[:top]:
            lines.append(
                f"- `{row['family_id']}`: canonical `{row['candidate_canonical_endpoint']}` | members `{row['member_count']}` | score `{row['family_score']}` | subtype `{row.get('relation_subtype', 'true_dedup_candidate')}`"
            )
            lines.append(f"  - bundle: `{row['shared_minimal_source_bundle']}`")
            if row.get("shared_name_stem"):
                lines.append(f"  - shared stem: `{row['shared_name_stem']}`")
            lines.append(f"  - recommended action: `{row.get('recommended_action', 'review_for_contraction')}`")
            lines.append(f"  - members: `{', '.join(row['member_sinks'])}`")
            if row["shared_sink_family"]:
                lines.append(f"  - sink family: `{', '.join(row['shared_sink_family'])}`")
            if row["shared_top_corridor_representatives"]:
                lines.append(
                    f"  - corridor reps: `{', '.join(row['shared_top_corridor_representatives'][:6])}`"
                )
            if row["motif_signature"]:
                lines.append(f"  - motif: `{row['motif_signature']}`")
        lines.append("")
    lines.append("## Shadow Relations")
    if not shadow_relations:
        lines.append("- none")
        lines.append("")
    else:
        for row in shadow_relations[:top]:
            lines.append(
                f"- `{row['upstream_module']}` -> `{row['downstream_module']}`: score `{row['score']}` | packet `{row['shared_packet_signature'] or '-'}`"
            )
            lines.append(
                f"  - roles: `{row['upstream_role_class']}` -> `{row['downstream_role_class']}` | comp-j `{row['component_jaccard']}` | sink-j `{row['sink_family_jaccard']}` | motif-j `{row['motif_jaccard']}`"
            )
            if row["shared_top_corridor_representatives"]:
                lines.append(
                    f"  - shared corridor reps: `{', '.join(row['shared_top_corridor_representatives'][:6])}`"
                )
            lines.append(f"  - why: `{row['why_transport_not_duplication']}`")
        lines.append("")
    lines.append("## Assumption Packet Reuse")
    if not assumption_packet_reuse:
        lines.append("- none")
        lines.append("")
    else:
        for row in assumption_packet_reuse[:top]:
            lines.append(
                f"- `{row['atomic_id']}`: reuse-score `{row['reuse_score']}` | carriers `{row['carrier_count']}` | sinks `{row['sink_name_count']}` | upstream `{row['suggested_upstream_home'] or '-'}`"
            )
            lines.append(f"  - carrier modules: `{', '.join(row['carrier_modules'])}`")
            if row["motif_signature"]:
                lines.append(f"  - motif: `{row['motif_signature']}`")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    structure_path = normalize_user_path(args.structure, default_decl_structure_file())
    bipartite_path = normalize_user_path(args.bipartite, default_source_sink_bipartite_file())
    json_out = normalize_user_path(args.json_out, repo_root() / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, repo_root() / DEFAULT_MD_OUT)

    structure_payload = load_json(structure_path)
    bipartite_payload = load_json(bipartite_path)

    components_by_id = parse_structure(structure_payload)
    hydrated_by_id = normalize_hydrated_rows(bipartite_payload)
    atomic_by_id = normalize_atomic_rows(bipartite_payload)
    sink_by_name = normalize_sink_rows(bipartite_payload)
    usage_by_atomic = parse_incidence(bipartite_payload)

    dedup_families = build_dedup_families(atomic_by_id, sink_by_name)
    shadow_relations = build_shadow_relations(
        hydrated_by_id,
        components_by_id,
        shadow_threshold=float(args.shadow_threshold),
    )
    assumption_packet_reuse = build_assumption_packet_reuse(
        atomic_by_id,
        hydrated_by_id,
        usage_by_atomic,
    )
    summary = build_summary(
        dedup_families,
        shadow_relations,
        assumption_packet_reuse,
        sink_by_name,
        hydrated_by_id,
    )

    payload = {
        "kind": "structural_dedup",
        "structure": str(structure_path),
        "bipartite_artifact": str(bipartite_path),
        "shadow_threshold": float(args.shadow_threshold),
        "summary": summary,
        "dedup_families": dedup_families,
        "shadow_relations": shadow_relations,
        "assumption_packet_reuse": assumption_packet_reuse,
    }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    md_out.write_text(
        render_markdown(
            summary,
            dedup_families,
            shadow_relations,
            assumption_packet_reuse,
            structure_path,
            bipartite_path,
            float(args.shadow_threshold),
            int(args.top),
        ),
        encoding="utf-8",
    )

    print(f"[structural-dedup] wrote {json_out}")
    print(f"[structural-dedup] wrote {md_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
