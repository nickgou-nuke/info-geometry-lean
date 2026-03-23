#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
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
DEFAULT_JSON_OUT = "reports/dag/structural-fibers.json"
DEFAULT_MD_OUT = "reports/dag/structural-fibers.md"

ROLE_ORDER = {
    "constructive_source": 0,
    "transport_only": 1,
    "consumer_sink": 2,
}


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Generate a packet-conditioned structural fiber report over the native condensation "
            "topology and the source-sink bipartite correspondence artifact."
        )
    )
    ap.add_argument("--structure", default=DEFAULT_STRUCTURE)
    ap.add_argument("--bipartite", default=DEFAULT_BIPARTITE)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--top", type=int, default=25)
    return ap.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    return raw if isinstance(raw, dict) else {}


def ordered_unique(items: list[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        text = str(item).strip()
        if not text or text in seen:
            continue
        seen.add(text)
        out.append(text)
    return out


def short_name(name: str) -> str:
    return name.rsplit('.', 1)[-1]


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


def component_reprs(component_ids: list[str], components_by_id: dict[str, dict[str, Any]]) -> list[str]:
    out: list[str] = []
    for component_id in component_ids:
        text = component_repr(str(component_id), components_by_id)
        if text:
            out.append(text)
    return ordered_unique(out)


def normalize_atomic_rows(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in payload.get("atomic_nodes", []):
        if not isinstance(row, dict):
            continue
        atomic_id = str(row.get("atomic_id", ""))
        if atomic_id:
            out[atomic_id] = row
    return out


def normalize_hydrated_rows(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in payload.get("hydrated_nodes", []):
        if not isinstance(row, dict):
            continue
        hydrated_id = str(row.get("hydrated_id", ""))
        if hydrated_id:
            out[hydrated_id] = row
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


def parse_incidence_edges(payload: dict[str, Any]) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in payload.get("incidence_edges", []):
        if not isinstance(row, dict):
            continue
        if str(row.get("role", "")) != "supports":
            continue
        if str(row.get("projection_kind", "")) != "node_support":
            continue
        atomic_id = str(row.get("atomic_id", ""))
        if atomic_id:
            out[atomic_id].append(row)
    return dict(out)


def role_rank(role: str) -> int:
    return ROLE_ORDER.get(role, 99)


def choose_canonical_sink(sink_names: list[str], sink_by_name: dict[str, dict[str, Any]]) -> str:
    if not sink_names:
        return ""

    def rank(name: str) -> tuple[Any, ...]:
        row = sink_by_name.get(name, {})
        return (
            int(row.get("severity", 99) or 99),
            len(short_name(name)),
            -int(row.get("flow_in_degree", 0) or 0),
            name,
        )

    return min(sink_names, key=rank)


def common_prefix(seqs: list[list[str]]) -> list[str]:
    if not seqs:
        return []
    prefix: list[str] = []
    shortest = min(len(seq) for seq in seqs)
    for idx in range(shortest):
        candidate = seqs[0][idx]
        if all(seq[idx] == candidate for seq in seqs[1:]):
            prefix.append(candidate)
        else:
            break
    return prefix


def common_suffix(seqs: list[list[str]]) -> list[str]:
    if not seqs:
        return []
    suffix: list[str] = []
    shortest = min(len(seq) for seq in seqs)
    for offset in range(1, shortest + 1):
        candidate = seqs[0][-offset]
        if all(seq[-offset] == candidate for seq in seqs[1:]):
            suffix.append(candidate)
        else:
            break
    suffix.reverse()
    return suffix


def branch_points(seqs: list[list[str]], prefix: list[str]) -> list[str]:
    out: list[str] = []
    start = len(prefix)
    for seq in seqs:
        if start < len(seq):
            out.append(seq[start])
    return ordered_unique(out)


def merge_points(seqs: list[list[str]], suffix: list[str]) -> list[str]:
    out: list[str] = []
    suffix_len = len(suffix)
    for seq in seqs:
        idx = len(seq) - suffix_len - 1
        if idx >= 0:
            out.append(seq[idx])
    return ordered_unique(out)


def jaccard(left: list[str] | set[str], right: list[str] | set[str]) -> float:
    left_set = {str(x) for x in left if str(x)}
    right_set = {str(x) for x in right if str(x)}
    if not left_set or not right_set:
        return 0.0
    return len(left_set & right_set) / len(left_set | right_set)


def corridor_representatives(atomic: dict[str, Any], components_by_id: dict[str, dict[str, Any]]) -> list[str]:
    reps = [str(x) for x in atomic.get("native_component_representatives", []) if str(x)]
    if reps:
        return ordered_unique(reps)
    component_ids = [str(x) for x in atomic.get("native_component_ids", []) if str(x)]
    return component_reprs(component_ids, components_by_id)


def role_chain(edges: list[dict[str, Any]], hydrated_by_id: dict[str, dict[str, Any]]) -> list[str]:
    roles: list[str] = []
    for row in edges:
        hydrated_id = str(row.get("hydrated_id", ""))
        hydrated = hydrated_by_id.get(hydrated_id, {})
        role = str(
            hydrated.get("sink_role")
            or row.get("hydrated_role")
            or row.get("carrier_role")
            or "unknown"
        )
        roles.append(role)
    return sorted(set(roles), key=role_rank)


def packet_kind(sink_count: int, carrier_count: int, roles: list[str]) -> str:
    transport_present = "transport_only" in roles
    if sink_count > 1 and transport_present:
        return "presentation_plus_transport"
    if sink_count > 1:
        return "presentation_duplicate"
    if transport_present or carrier_count > 2:
        return "transport_projection"
    return "single_strand"


def packet_score(atomic: dict[str, Any], sink_count: int, carrier_count: int, roles: list[str]) -> float:
    transport_present = "transport_only" in roles
    return round(
        6.0 * max(0, sink_count - 1)
        + 2.0 * max(0, carrier_count - 2)
        + (2.0 if transport_present else 0.0)
        + 0.5 * int(atomic.get("path_multiplicity", 0) or 0)
        + 0.05 * float(atomic.get("compression_potential", 0.0) or 0.0),
        4,
    )


def packet_fiber_id(atomic_id: str) -> str:
    digest = hashlib.sha1(atomic_id.encode("utf-8")).hexdigest()[:12]
    return f"packet:{digest}"


def group_id(prefix: str, parts: list[str]) -> str:
    digest = hashlib.sha1("|".join(parts).encode("utf-8")).hexdigest()[:12]
    return f"{prefix}:{digest}"


def build_packet_fibers(
    atomic_by_id: dict[str, dict[str, Any]],
    hydrated_by_id: dict[str, dict[str, Any]],
    sink_by_name: dict[str, dict[str, Any]],
    incidence_by_atomic: dict[str, list[dict[str, Any]]],
    components_by_id: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for atomic_id, atomic in atomic_by_id.items():
        edges = incidence_by_atomic.get(atomic_id, [])
        source_modules = ordered_unique([str(x) for x in atomic.get("source_modules", []) if str(x)])
        sink_family = ordered_unique([str(x) for x in atomic.get("sink_modules", []) if str(x)])
        sink_names = ordered_unique([str(x) for x in atomic.get("sink_names", []) if str(x)])
        roles = role_chain(edges, hydrated_by_id)
        carriers = ordered_unique([str(row.get("hydrated_id", "")) for row in edges if str(row.get("hydrated_id", ""))])
        carrier_modules = ordered_unique([
            str(hydrated_by_id.get(hydrated_id, {}).get("module", hydrated_id))
            for hydrated_id in carriers
        ])
        corridor = corridor_representatives(atomic, components_by_id)
        canonical_sink = choose_canonical_sink(sink_names, sink_by_name)
        wrappers = [name for name in sink_names if name != canonical_sink]
        sink_count = len(sink_names)
        carrier_count = len(carriers)
        kind = packet_kind(sink_count, carrier_count, roles)
        score = packet_score(atomic, sink_count, carrier_count, roles)
        rows.append({
            "packet_id": packet_fiber_id(atomic_id),
            "relation_type": "packet_fiber",
            "atomic_id": atomic_id,
            "packet_kind": kind,
            "packet_score": score,
            "source_modules": source_modules,
            "source_bundle": [str(x) for x in atomic.get("source_bundle", []) if str(x)],
            "supporting_atomic_decls": [str(x) for x in atomic.get("supporting_atomic_decls", []) if str(x)],
            "sink_family": sink_family,
            "sink_names": sink_names,
            "sink_name_count": sink_count,
            "candidate_canonical_endpoint": canonical_sink,
            "presentation_wrappers": wrappers,
            "presentation_wrapper_count": len(wrappers),
            "carrier_hydrated_ids": carriers,
            "carrier_modules": carrier_modules,
            "carrier_count": carrier_count,
            "role_chain": roles,
            "motif_signature": str(atomic.get("motif_signature", "")),
            "path_multiplicity": int(atomic.get("path_multiplicity", 0) or 0),
            "compression_potential": float(atomic.get("compression_potential", 0.0) or 0.0),
            "native_component_ids": [str(x) for x in atomic.get("native_component_ids", []) if str(x)],
            "native_component_representatives": corridor,
            "native_root_witnesses": [str(x) for x in atomic.get("native_root_witnesses", []) if str(x)],
            "native_strict_dominator_representatives": [str(x) for x in atomic.get("native_strict_dominator_representatives", []) if str(x)],
            "native_depth_min": int(atomic.get("native_depth_min", 0) or 0),
            "native_depth_max": int(atomic.get("native_depth_max", 0) or 0),
        })

    rows.sort(
        key=lambda row: (
            -float(row["packet_score"]),
            -int(row["presentation_wrapper_count"]),
            row["candidate_canonical_endpoint"] or row["atomic_id"],
        )
    )
    return rows


def group_rows_by_source_sink(packet_fibers: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[tuple[str, ...], tuple[str, ...]], list[dict[str, Any]]] = defaultdict(list)
    for row in packet_fibers:
        key = (tuple(row["source_modules"]), tuple(row["sink_family"]))
        grouped[key].append(row)

    rows: list[dict[str, Any]] = []
    for (source_modules_key, sink_family_key), members in grouped.items():
        source_modules = list(source_modules_key)
        sink_family = list(sink_family_key)
        corridors = [list(row["native_component_representatives"]) for row in members if row["native_component_representatives"]]
        shared_source_trunk = common_prefix(corridors)
        shared_sink_trunk = common_suffix(corridors)
        unique_corridor_classes = ordered_unique([" -> ".join(row["native_component_representatives"]) for row in members])
        sink_names = ordered_unique([name for row in members for name in row["sink_names"]])
        wrappers = ordered_unique([name for row in members for name in row["presentation_wrappers"]])
        packet_kinds = Counter(str(row["packet_kind"]) for row in members)
        packet_count = len(members)
        corridor_class_count = len(unique_corridor_classes)
        wrapper_count = len(wrappers)
        compression_sum = sum(float(row["compression_potential"]) for row in members)
        if packet_count == 1:
            classification = "single_packet_presentation" if wrapper_count > 0 else "single_packet"
        elif corridor_class_count > 1 and wrapper_count > 0:
            classification = "multi_packet_mixed"
        elif corridor_class_count > 1:
            classification = "parallel_transport"
        elif wrapper_count > 0:
            classification = "presentation_cluster"
        else:
            classification = "multi_packet_projection"
        score = round(
            8.0 * max(0, packet_count - 1)
            + 3.0 * max(0, corridor_class_count - 1)
            + 2.0 * wrapper_count
            + 0.05 * compression_sum,
            4,
        )
        endpoints = ordered_unique([str(row["candidate_canonical_endpoint"]) for row in members if str(row["candidate_canonical_endpoint"])])
        rows.append({
            "group_id": group_id("fiber-group", source_modules + ["//"] + sink_family),
            "relation_type": "source_sink_fiber_group",
            "classification": classification,
            "group_score": score,
            "source_modules": source_modules,
            "sink_family": sink_family,
            "packet_count": packet_count,
            "packet_ids": [str(row["packet_id"]) for row in members],
            "atomic_ids": [str(row["atomic_id"]) for row in members],
            "source_bundle_count": packet_count,
            "corridor_class_count": corridor_class_count,
            "sink_surface_count": len(sink_names),
            "presentation_wrapper_count": wrapper_count,
            "packet_kind_counts": dict(packet_kinds),
            "candidate_canonical_endpoints": endpoints,
            "presentation_wrappers": wrappers,
            "shared_source_trunk_representatives": shared_source_trunk,
            "shared_sink_trunk_representatives": shared_sink_trunk,
            "branch_points": branch_points(corridors, shared_source_trunk),
            "merge_points": merge_points(corridors, shared_sink_trunk),
            "top_root_witnesses": ordered_unique([
                str(row["native_root_witnesses"][0])
                for row in members
                if row.get("native_root_witnesses")
            ]),
            "corridor_representative_classes": [
                row["native_component_representatives"]
                for row in members
            ],
            "motif_signatures": ordered_unique([str(row["motif_signature"]) for row in members if str(row["motif_signature"])]) ,
            "compression_potential_sum": round(compression_sum, 4),
        })

    rows.sort(
        key=lambda row: (
            -float(row["group_score"]),
            -int(row["packet_count"]),
            row["sink_family"][0] if row["sink_family"] else "",
        )
    )
    return rows


def build_sink_family_entanglements(
    packet_fibers: list[dict[str, Any]],
    source_sink_groups: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    packets_by_family: dict[tuple[str, ...], list[dict[str, Any]]] = defaultdict(list)
    groups_by_family: dict[tuple[str, ...], list[dict[str, Any]]] = defaultdict(list)
    for row in packet_fibers:
        packets_by_family[tuple(row["sink_family"])].append(row)
    for row in source_sink_groups:
        groups_by_family[tuple(row["sink_family"])].append(row)

    rows: list[dict[str, Any]] = []
    for family_key, members in packets_by_family.items():
        sink_family = list(family_key)
        group_members = groups_by_family.get(family_key, [])
        source_modules = ordered_unique([module for row in members for module in row["source_modules"]])
        sink_names = ordered_unique([name for row in members for name in row["sink_names"]])
        wrappers = ordered_unique([name for row in members for name in row["presentation_wrappers"]])
        corridors = [list(row["native_component_representatives"]) for row in members if row["native_component_representatives"]]
        corridor_classes = ordered_unique([" -> ".join(row["native_component_representatives"]) for row in members])
        shared_source_trunk = common_prefix(corridors)
        shared_sink_trunk = common_suffix(corridors)
        packet_count = len(members)
        source_module_count = len(source_modules)
        corridor_class_count = len(corridor_classes)
        wrapper_count = len(wrappers)
        compression_sum = sum(float(row["compression_potential"]) for row in members)
        if packet_count == 1:
            classification = "presentation_heavy" if wrapper_count > 0 else "single_strand"
        elif source_module_count == 1 and corridor_class_count > 1:
            classification = "transport_fibered"
        elif source_module_count > 1 and corridor_class_count == 1:
            classification = "assumption_fibered"
        elif source_module_count > 1 and corridor_class_count > 1:
            classification = "bulk_entangled"
        elif wrapper_count > 0:
            classification = "presentation_heavy"
        else:
            classification = "mixed_multi_packet"
        score = round(
            10.0 * max(0, packet_count - 1)
            + 4.0 * max(0, source_module_count - 1)
            + 3.0 * max(0, corridor_class_count - 1)
            + 2.0 * wrapper_count
            + 0.05 * compression_sum,
            4,
        )
        packet_kind_counts = Counter(str(row["packet_kind"]) for row in members)
        candidate_endpoints = ordered_unique([
            str(row["candidate_canonical_endpoint"])
            for row in members
            if str(row["candidate_canonical_endpoint"])
        ])
        rows.append({
            "family_id": group_id("sink-family", sink_family),
            "relation_type": "sink_family_entanglement",
            "classification": classification,
            "entanglement_score": score,
            "sink_family": sink_family,
            "packet_count": packet_count,
            "source_sink_group_count": len(group_members),
            "source_module_count": source_module_count,
            "source_modules": source_modules,
            "source_bundle_count": len(members),
            "sink_surface_count": len(sink_names),
            "presentation_wrapper_count": wrapper_count,
            "corridor_class_count": corridor_class_count,
            "candidate_canonical_endpoints": candidate_endpoints,
            "presentation_wrappers": wrappers,
            "packet_kind_counts": dict(packet_kind_counts),
            "shared_source_trunk_representatives": shared_source_trunk,
            "shared_sink_trunk_representatives": shared_sink_trunk,
            "branch_points": branch_points(corridors, shared_source_trunk),
            "merge_points": merge_points(corridors, shared_sink_trunk),
            "top_root_witnesses": ordered_unique([
                str(row["native_root_witnesses"][0])
                for row in members
                if row.get("native_root_witnesses")
            ]),
            "atomic_ids": [str(row["atomic_id"]) for row in members],
            "packet_ids": [str(row["packet_id"]) for row in members],
            "compression_potential_sum": round(compression_sum, 4),
        })

    rows.sort(
        key=lambda row: (
            -float(row["entanglement_score"]),
            -int(row["packet_count"]),
            row["sink_family"][0] if row["sink_family"] else "",
        )
    )
    return rows


def build_summary(
    packet_fibers: list[dict[str, Any]],
    source_sink_groups: list[dict[str, Any]],
    sink_family_entanglements: list[dict[str, Any]],
    structure_payload: dict[str, Any],
) -> dict[str, Any]:
    packet_kind_counts = Counter(str(row["packet_kind"]) for row in packet_fibers)
    entanglement_kind_counts = Counter(str(row["classification"]) for row in sink_family_entanglements)
    return {
        "component_count": int(structure_payload.get("componentCount", 0) or 0),
        "packet_count": len(packet_fibers),
        "source_sink_group_count": len(source_sink_groups),
        "multi_packet_group_count": sum(1 for row in source_sink_groups if int(row.get("packet_count", 0) or 0) > 1),
        "sink_family_entanglement_count": len(sink_family_entanglements),
        "multi_packet_sink_family_count": sum(1 for row in sink_family_entanglements if int(row.get("packet_count", 0) or 0) > 1),
        "packet_kind_counts": dict(packet_kind_counts),
        "entanglement_kind_counts": dict(entanglement_kind_counts),
        "top_packet_score": round(float(packet_fibers[0]["packet_score"]), 4) if packet_fibers else 0.0,
        "top_group_score": round(float(source_sink_groups[0]["group_score"]), 4) if source_sink_groups else 0.0,
        "top_entanglement_score": round(float(sink_family_entanglements[0]["entanglement_score"]), 4) if sink_family_entanglements else 0.0,
    }


def render_markdown(
    summary: dict[str, Any],
    packet_fibers: list[dict[str, Any]],
    source_sink_groups: list[dict[str, Any]],
    sink_family_entanglements: list[dict[str, Any]],
    structure_path: Path,
    bipartite_path: Path,
    top: int,
) -> str:
    lines: list[str] = []
    lines.append("# Structural Fibers")
    lines.append("")
    lines.append(
        "This report decomposes the native source-sink correspondence into packet-conditioned corridor strands so bulk entanglement can be separated from sink-surface pressure."
    )
    lines.append("")
    lines.append(f"- structure: `{structure_path}`")
    lines.append(f"- bipartite artifact: `{bipartite_path}`")
    lines.append("")
    lines.append("## Summary")
    lines.append(f"- native components: `{summary.get('component_count', 0)}`")
    lines.append(f"- packet fibers: `{summary.get('packet_count', 0)}`")
    lines.append(f"- source-sink fiber groups: `{summary.get('source_sink_group_count', 0)}`")
    lines.append(f"- multi-packet source-sink groups: `{summary.get('multi_packet_group_count', 0)}`")
    lines.append(f"- sink-family entanglements: `{summary.get('sink_family_entanglement_count', 0)}`")
    lines.append(f"- multi-packet sink families: `{summary.get('multi_packet_sink_family_count', 0)}`")
    lines.append(f"- packet kinds: `{summary.get('packet_kind_counts', {})}`")
    lines.append(f"- entanglement kinds: `{summary.get('entanglement_kind_counts', {})}`")
    lines.append(f"- top packet score: `{summary.get('top_packet_score', 0.0)}`")
    lines.append(f"- top group score: `{summary.get('top_group_score', 0.0)}`")
    lines.append(f"- top entanglement score: `{summary.get('top_entanglement_score', 0.0)}`")
    lines.append("")
    lines.append("## Packet Fibers")
    if not packet_fibers:
        lines.append("- none")
        lines.append("")
    else:
        for row in packet_fibers[:top]:
            lines.append(
                f"- `{row['atomic_id']}`: kind `{row['packet_kind']}` | score `{row['packet_score']}` | source `{', '.join(row['source_modules']) or '-'}` | sink `{', '.join(row['sink_family']) or '-'}`"
            )
            lines.append(
                f"  - canonical endpoint: `{row['candidate_canonical_endpoint'] or '-'}` | wrappers `{row['presentation_wrapper_count']}` | carriers `{row['carrier_count']}` | roles `{', '.join(row['role_chain']) or '-'}`"
            )
            if row["native_component_representatives"]:
                lines.append(
                    f"  - corridor: `{', '.join(row['native_component_representatives'][:6])}`"
                )
            if row["native_strict_dominator_representatives"]:
                lines.append(
                    f"  - strict dominators: `{', '.join(row['native_strict_dominator_representatives'][:6])}`"
                )
        lines.append("")
    lines.append("## Source-Sink Fiber Groups")
    if not source_sink_groups:
        lines.append("- none")
        lines.append("")
    else:
        for row in source_sink_groups[:top]:
            lines.append(
                f"- `{', '.join(row['source_modules']) or '-'}` -> `{', '.join(row['sink_family']) or '-'}`: class `{row['classification']}` | packets `{row['packet_count']}` | corridors `{row['corridor_class_count']}` | score `{row['group_score']}`"
            )
            lines.append(
                f"  - canonical endpoints: `{', '.join(row['candidate_canonical_endpoints']) or '-'}` | wrappers `{row['presentation_wrapper_count']}` | sink surfaces `{row['sink_surface_count']}`"
            )
            if row["shared_source_trunk_representatives"]:
                lines.append(
                    f"  - shared source trunk: `{', '.join(row['shared_source_trunk_representatives'][:6])}`"
                )
            if row["shared_sink_trunk_representatives"]:
                lines.append(
                    f"  - shared sink trunk: `{', '.join(row['shared_sink_trunk_representatives'][:6])}`"
                )
            if row["branch_points"]:
                lines.append(f"  - branch points: `{', '.join(row['branch_points'][:6])}`")
            if row["merge_points"]:
                lines.append(f"  - merge points: `{', '.join(row['merge_points'][:6])}`")
        lines.append("")
    lines.append("## Sink-Family Entanglements")
    if not sink_family_entanglements:
        lines.append("- none")
        lines.append("")
    else:
        for row in sink_family_entanglements[:top]:
            lines.append(
                f"- `{', '.join(row['sink_family']) or '-'}`: class `{row['classification']}` | packets `{row['packet_count']}` | source modules `{row['source_module_count']}` | corridors `{row['corridor_class_count']}` | score `{row['entanglement_score']}`"
            )
            lines.append(
                f"  - canonical endpoints: `{', '.join(row['candidate_canonical_endpoints']) or '-'}` | wrappers `{row['presentation_wrapper_count']}` | sink surfaces `{row['sink_surface_count']}`"
            )
            lines.append(f"  - source modules: `{', '.join(row['source_modules']) or '-'}`")
            if row["shared_sink_trunk_representatives"]:
                lines.append(
                    f"  - shared sink trunk: `{', '.join(row['shared_sink_trunk_representatives'][:6])}`"
                )
            if row["branch_points"]:
                lines.append(f"  - branch points: `{', '.join(row['branch_points'][:6])}`")
            if row["merge_points"]:
                lines.append(f"  - merge points: `{', '.join(row['merge_points'][:6])}`")
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
    atomic_by_id = normalize_atomic_rows(bipartite_payload)
    hydrated_by_id = normalize_hydrated_rows(bipartite_payload)
    sink_by_name = normalize_sink_rows(bipartite_payload)
    incidence_by_atomic = parse_incidence_edges(bipartite_payload)

    packet_fibers = build_packet_fibers(
        atomic_by_id,
        hydrated_by_id,
        sink_by_name,
        incidence_by_atomic,
        components_by_id,
    )
    source_sink_groups = group_rows_by_source_sink(packet_fibers)
    sink_family_entanglements = build_sink_family_entanglements(packet_fibers, source_sink_groups)
    summary = build_summary(packet_fibers, source_sink_groups, sink_family_entanglements, structure_payload)

    payload = {
        "kind": "structural_fibers",
        "structure": str(structure_path),
        "bipartite_artifact": str(bipartite_path),
        "summary": summary,
        "packet_fibers": packet_fibers,
        "source_sink_fiber_groups": source_sink_groups,
        "sink_family_entanglements": sink_family_entanglements,
    }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    md_out.write_text(
        render_markdown(
            summary,
            packet_fibers,
            source_sink_groups,
            sink_family_entanglements,
            structure_path,
            bipartite_path,
            int(args.top),
        ),
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
