#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import networkx as nx

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.plot_decl_graph import (
        FRONTIER_CATEGORIES,
        build_declaration_graph,
        build_module_graph,
        burn_down_rows,
        filter_declaration_graph_by_surface,
        load_decl_meta,
        load_surface_categories,
        module_strength_rows,
        normalize_user_path,
    )
    from tools.pathing import default_decl_graph_file, default_decl_metadata_file, default_source_sink_bipartite_file, repo_root
else:
    from tools.infra.plot_decl_graph import (
        FRONTIER_CATEGORIES,
        build_declaration_graph,
        build_module_graph,
        burn_down_rows,
        filter_declaration_graph_by_surface,
        load_decl_meta,
        load_surface_categories,
        module_strength_rows,
        normalize_user_path,
    )
    from tools.pathing import default_decl_graph_file, default_decl_metadata_file, default_source_sink_bipartite_file, repo_root


DEFAULT_GRAPH = str(default_decl_graph_file().relative_to(repo_root()))
DEFAULT_DECLS = str(default_decl_metadata_file().relative_to(repo_root()))
DEFAULT_SURFACE_INDEX = "reports/dag/theorem-surface-index.json"
DEFAULT_MD_OUT = "reports/dag/source-sink-compression.md"
DEFAULT_JSON_OUT = "reports/dag/source-sink-compression.json"
DEFAULT_GRAPHML_OUT = "reports/dag/source-sink-incidence.graphml"
DEFAULT_SVG_OUT = "reports/dag/source-sink-incidence.svg"
DEFAULT_ARTIFACT_OUT = str(default_source_sink_bipartite_file().relative_to(repo_root()))

SIDE_COLORS = {
    "source": "#2E8B57",
    "bundle": "#4C78A8",
    "sink": "#D55E00",
}
SINK_CATEGORY_WEIGHT = {
    "surrogate_or_vacuous": 4.0,
    "package_reprojection": 2.0,
    "hypothesis_bridge": 1.0,
}
SINK_CATEGORY_SEVERITY = {
    "surrogate_or_vacuous": 3,
    "package_reprojection": 2,
    "hypothesis_bridge": 1,
}
PRIMARY_MOTIFS: list[tuple[str, tuple[str, ...]]] = [
    ("unitRelativeVolume", ("unitrelativevolume", "relativevolumechangern", "unit_relative_volume")),
    ("RN/Kähler/log-det", ("kahler", "logdet", "log_det", "relativevolume", "radonnikodym")),
    ("chiralScale=0", ("chiralscale_eq_zero", "chiralscalezero", "scale_eq_zero")),
    ("IsNormalInference", ("isnormalinference", "normalinference")),
    ("projectors commute", ("projectors_commute", "projector_commute")),
    ("anomaly=0", ("anomaly_eq_zero", "anomalyoperator_eq_zero", "zero_anomaly")),
    ("Dirac collapse", ("chiraldirac", "chiral_action_reduces", "dirac_eq")),
    ("holonomy=0", ("holonomy_eq_zero", "holonomy_zero")),
    ("Einstein closure", ("einsteinequation", "einstein_equation", "stressenergy")),
    ("Yang-Mills closure", ("yangmills", "yang_mills")),
]
SOURCE_KINDS = {"theorem"}
FALLBACK_SOURCE_KINDS = {"theorem", "def", "opaque"}


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Build a source-bundle/sink-bundle incidence layer between the atomic declaration DAG "
            "and the hydrated module graph. This is the path-compression / theorem-generation view."
        )
    )
    ap.add_argument("--graph", default=DEFAULT_GRAPH, help="Declaration DAG JSON from the Lean Indexer.")
    ap.add_argument("--decls", default=DEFAULT_DECLS, help="Declaration metadata JSONL.")
    ap.add_argument("--surface-index", default=DEFAULT_SURFACE_INDEX)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--artifact-out", default=DEFAULT_ARTIFACT_OUT)
    ap.add_argument("--graphml-out", default=DEFAULT_GRAPHML_OUT)
    ap.add_argument("--svg-out", default=DEFAULT_SVG_OUT)
    ap.add_argument("--hotspot-module-count", type=int, default=8)
    ap.add_argument("--sink-per-module", type=int, default=4)
    ap.add_argument("--max-sinks", type=int, default=28)
    ap.add_argument("--max-path-depth", type=int, default=14)
    ap.add_argument("--top-bundles", type=int, default=18)
    ap.add_argument("--top-hydrated-modules", type=int, default=20)
    return ap.parse_args()


def short_name(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def collapse_consecutive(items: list[str]) -> list[str]:
    out: list[str] = []
    for item in items:
        if not item:
            continue
        if not out or out[-1] != item:
            out.append(item)
    return out


def motif_label(name: str) -> str:
    lowered = short_name(name).lower()
    for label, needles in PRIMARY_MOTIFS:
        if any(needle in lowered for needle in needles):
            return label
    return short_name(name)


def motif_signature(path_nodes: list[str]) -> list[str]:
    return collapse_consecutive([motif_label(name) for name in path_nodes])


def select_hotspot_modules(frontier_module_graph: nx.DiGraph, count: int) -> list[dict[str, Any]]:
    hotspot_rows = module_strength_rows(frontier_module_graph)[: max(count, 1)]
    return burn_down_rows(hotspot_rows)


def select_sink_rows(
    decl_graph: nx.DiGraph,
    flow_graph: nx.DiGraph,
    hotspot_rows: list[dict[str, Any]],
    *,
    sink_per_module: int,
    max_sinks: int,
) -> list[dict[str, Any]]:
    hotspot_rank = {row["module"]: int(row["burn_down_rank"]) for row in hotspot_rows}
    candidates: list[dict[str, Any]] = []
    for node, data in decl_graph.nodes(data=True):
        module = str(data.get("module", "unknown"))
        category = str(data.get("surface_category", "unknown"))
        kind = str(data.get("kind", "unknown"))
        if module not in hotspot_rank:
            continue
        if category not in FRONTIER_CATEGORIES or kind != "theorem":
            continue
        candidates.append(
            {
                "name": node,
                "module": module,
                "category": category,
                "kind": kind,
                "burn_down_rank": hotspot_rank[module],
                "flow_out_degree": int(flow_graph.out_degree(node)),
                "flow_in_degree": int(flow_graph.in_degree(node)),
                "severity": SINK_CATEGORY_SEVERITY.get(category, 0),
            }
        )

    candidates.sort(
        key=lambda row: (
            int(row["burn_down_rank"]),
            int(row["flow_out_degree"]),
            -int(row["severity"]),
            -int(row["flow_in_degree"]),
            row["name"],
        )
    )

    out: list[dict[str, Any]] = []
    per_module: Counter[str] = Counter()
    for row in candidates:
        module = str(row["module"])
        if per_module[module] >= sink_per_module:
            continue
        out.append(row)
        per_module[module] += 1
        if len(out) >= max_sinks:
            break
    return out


def collect_source_stats(
    decl_graph: nx.DiGraph,
    flow_graph: nx.DiGraph,
    sink_rows: list[dict[str, Any]],
    *,
    max_depth: int,
) -> tuple[dict[str, dict[str, Any]], dict[str, list[dict[str, Any]]]]:
    source_stats: dict[str, dict[str, Any]] = {}
    sink_to_candidates: dict[str, list[dict[str, Any]]] = defaultdict(list)

    for sink_row in sink_rows:
        sink = str(sink_row["name"])
        lengths = nx.single_source_shortest_path_length(decl_graph, sink, cutoff=max_depth)
        primary_candidates: list[dict[str, Any]] = []
        fallback_candidates: list[dict[str, Any]] = []

        for node, distance in lengths.items():
            if node == sink:
                continue
            data = decl_graph.nodes[node]
            category = str(data.get("surface_category", "unknown"))
            kind = str(data.get("kind", "unknown"))
            row = {
                "name": node,
                "distance": int(distance),
                "module": str(data.get("module", "unknown")),
                "category": category,
                "kind": kind,
                "flow_in_degree": int(flow_graph.in_degree(node)),
                "flow_out_degree": int(flow_graph.out_degree(node)),
            }
            if category == "likely_constructive" and kind in SOURCE_KINDS:
                primary_candidates.append(row)
            elif category == "neutral_definition" and kind in FALLBACK_SOURCE_KINDS:
                fallback_candidates.append(row)

        selected = primary_candidates if primary_candidates else fallback_candidates
        sink_to_candidates[sink] = selected
        for row in selected:
            stats = source_stats.setdefault(
                row["name"],
                {
                    "name": row["name"],
                    "module": row["module"],
                    "category": row["category"],
                    "kind": row["kind"],
                    "reachable_sinks": 0,
                    "closest_sink_distance": 10**9,
                    "flow_in_degree": row["flow_in_degree"],
                    "flow_out_degree": row["flow_out_degree"],
                    "sink_modules": set(),
                },
            )
            stats["reachable_sinks"] += 1
            stats["closest_sink_distance"] = min(int(stats["closest_sink_distance"]), int(row["distance"]))
            stats["sink_modules"].add(str(sink_row["module"]))

    for stats in source_stats.values():
        reachable = float(stats["reachable_sinks"])
        fanout = float(stats["flow_out_degree"])
        indegree = float(stats["flow_in_degree"])
        closest = float(stats["closest_sink_distance"])
        stats["source_score"] = round((reachable * math.log1p(1.0 + fanout)) + (1.0 / (1.0 + closest)) - 0.05 * indegree, 4)
        stats["sink_modules"] = sorted(stats["sink_modules"])

    return source_stats, sink_to_candidates


def pick_canonical_source(
    sink_name: str,
    sink_to_candidates: dict[str, list[dict[str, Any]]],
    source_stats: dict[str, dict[str, Any]],
) -> dict[str, Any] | None:
    candidates = sink_to_candidates.get(sink_name, [])
    if not candidates:
        return None
    ordered = sorted(
        candidates,
        key=lambda row: (
            -float(source_stats[row["name"]]["source_score"]),
            int(row["distance"]),
            int(row["flow_in_degree"]),
            row["name"],
        ),
    )
    return ordered[0]


def bundle_key_for_path(decl_graph: nx.DiGraph, path_nodes: list[str]) -> tuple[str, ...]:
    bundle = [
        node
        for node in path_nodes
        if str(decl_graph.nodes[node].get("surface_category", "unknown")) in {"likely_constructive", "neutral_definition"}
        and str(decl_graph.nodes[node].get("kind", "unknown")) in FALLBACK_SOURCE_KINDS
    ]
    return tuple(bundle or [path_nodes[0]])


def build_canonical_paths(
    decl_graph: nx.DiGraph,
    sink_rows: list[dict[str, Any]],
    sink_to_candidates: dict[str, list[dict[str, Any]]],
    source_stats: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    for sink_row in sink_rows:
        sink = str(sink_row["name"])
        source_row = pick_canonical_source(sink, sink_to_candidates, source_stats)
        if source_row is None:
            continue
        source = str(source_row["name"])
        try:
            consumer_to_source = nx.shortest_path(decl_graph, sink, source)
        except (nx.NetworkXNoPath, nx.NodeNotFound):
            continue
        path_nodes = list(reversed(consumer_to_source))
        path_modules = collapse_consecutive([str(decl_graph.nodes[node].get("module", "unknown")) for node in path_nodes])
        bundle = bundle_key_for_path(decl_graph, path_nodes)
        motifs = motif_signature(path_nodes)
        sink_weight = float(SINK_CATEGORY_WEIGHT.get(str(sink_row["category"]), 1.0))
        compression_potential = max(len(path_nodes) - 1, 1) * sink_weight
        entries.append(
            {
                "source": source,
                "source_module": str(source_row["module"]),
                "source_score": float(source_stats[source]["source_score"]),
                "sink": sink,
                "sink_module": str(sink_row["module"]),
                "sink_category": str(sink_row["category"]),
                "path_nodes": path_nodes,
                "path_modules": path_modules,
                "path_length": len(path_nodes) - 1,
                "motif_signature": motifs,
                "motif_signature_text": " -> ".join(motifs),
                "source_bundle": list(bundle),
                "compression_potential": round(compression_potential, 3),
            }
        )
    return entries


def deterministic_bundle_id(bundle: tuple[str, ...]) -> str:
    basis = "\n".join(sorted(bundle)).encode("utf-8")
    return f"bundle:{hashlib.sha1(basis).hexdigest()[:12]}"


def summarize_bundles(entries: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], dict[tuple[str, ...], str]]:
    grouped: dict[tuple[str, ...], list[dict[str, Any]]] = defaultdict(list)
    for entry in entries:
        grouped[tuple(entry["source_bundle"])].append(entry)

    rows: list[dict[str, Any]] = []
    bundle_ids: dict[tuple[str, ...], str] = {}
    for idx, (bundle, bundle_entries) in enumerate(
        sorted(
            grouped.items(),
            key=lambda item: (
                -sum(float(entry["compression_potential"]) for entry in item[1]),
                -len(item[1]),
                " | ".join(item[0]),
            ),
        ),
        start=1,
    ):
        bundle_id = deterministic_bundle_id(bundle)
        bundle_ids[bundle] = bundle_id
        motif_counts = Counter(entry["motif_signature_text"] for entry in bundle_entries)
        sink_modules = sorted({str(entry["sink_module"]) for entry in bundle_entries})
        rows.append(
            {
                "bundle_id": bundle_id,
                "source_bundle": list(bundle),
                "source_modules": sorted({str(entry["source_module"]) for entry in bundle_entries}),
                "sink_count": len(bundle_entries),
                "sink_modules": sink_modules,
                "sink_names": sorted({str(entry["sink"]) for entry in bundle_entries}),
                "path_multiplicity": len(bundle_entries),
                "avg_path_length": round(
                    sum(int(entry["path_length"]) for entry in bundle_entries) / max(len(bundle_entries), 1), 3
                ),
                "motif_signature": motif_counts.most_common(1)[0][0] if motif_counts else "",
                "motif_signature_count": motif_counts.most_common(1)[0][1] if motif_counts else 0,
                "compression_potential": round(
                    sum(float(entry["compression_potential"]) for entry in bundle_entries),
                    3,
                ),
            }
        )
    return rows, bundle_ids


def summarize_motif_families(entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for entry in entries:
        grouped[str(entry["motif_signature_text"])].append(entry)
    rows: list[dict[str, Any]] = []
    for signature, motif_entries in grouped.items():
        rows.append(
            {
                "motif_signature": signature,
                "path_count": len(motif_entries),
                "sink_modules": sorted({str(entry["sink_module"]) for entry in motif_entries}),
                "source_modules": sorted({str(entry["source_module"]) for entry in motif_entries}),
                "avg_path_length": round(
                    sum(int(entry["path_length"]) for entry in motif_entries) / max(len(motif_entries), 1), 3
                ),
                "compression_potential": round(
                    sum(float(entry["compression_potential"]) for entry in motif_entries),
                    3,
                ),
            }
        )
    rows.sort(
        key=lambda row: (
            -float(row["compression_potential"]),
            -int(row["path_count"]),
            row["motif_signature"],
        )
    )
    return rows


def module_role(roles: set[str]) -> str:
    if roles == {"source"}:
        return "constructive_source"
    if roles == {"sink"}:
        return "consumer_sink"
    if roles == {"transport"}:
        return "transport_only"
    if roles == {"source", "transport"}:
        return "source_transport"
    if roles == {"sink", "transport"}:
        return "sink_transport"
    if roles == {"source", "sink"}:
        return "source_sink"
    if roles == {"source", "sink", "transport"}:
        return "source_transport_sink"
    return "mixed"


def summarize_hydrated_projection(
    decl_graph: nx.DiGraph,
    entries: list[dict[str, Any]],
    bundle_ids: dict[tuple[str, ...], str],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    module_stats: dict[str, dict[str, Any]] = {}
    edge_stats: dict[tuple[str, str], dict[str, Any]] = {}

    for entry in entries:
        bundle = tuple(entry["source_bundle"])
        bundle_id = bundle_ids[bundle]
        bundle_source_modules = {
            str(decl_graph.nodes[node].get("module", "unknown")) for node in entry["source_bundle"]
        }
        sink_module = str(entry["sink_module"])
        module_path = collapse_consecutive(list(entry["path_modules"]))
        motif_text = str(entry["motif_signature_text"])
        compression = float(entry["compression_potential"])

        for module in module_path:
            stats = module_stats.setdefault(
                module,
                {
                    "module": module,
                    "roles": set(),
                    "atomic_support": set(),
                    "bundle_counts": Counter(),
                    "motif_counts": Counter(),
                    "sink_modules": set(),
                    "sink_names": set(),
                    "path_multiplicity": 0,
                    "compression_potential": 0.0,
                },
            )
            stats["path_multiplicity"] += 1
            stats["compression_potential"] += compression
            stats["motif_counts"][motif_text] += 1
            stats["bundle_counts"][bundle_id] += 1
            stats["sink_modules"].add(sink_module)
            stats["sink_names"].add(str(entry["sink"]))
            if module == sink_module:
                stats["roles"].add("sink")
            elif module in bundle_source_modules:
                stats["roles"].add("source")
            else:
                stats["roles"].add("transport")
            for node in entry["path_nodes"]:
                if str(decl_graph.nodes[node].get("module", "unknown")) == module:
                    stats["atomic_support"].add(node)

        for src_module, dst_module in zip(module_path, module_path[1:]):
            edge = edge_stats.setdefault(
                (src_module, dst_module),
                {
                    "source_module": src_module,
                    "target_module": dst_module,
                    "path_count": 0,
                    "compression_potential": 0.0,
                    "motif_counts": Counter(),
                    "bundle_counts": Counter(),
                    "atomic_path_examples": [],
                },
            )
            edge["path_count"] += 1
            edge["compression_potential"] += compression
            edge["motif_counts"][motif_text] += 1
            edge["bundle_counts"][bundle_id] += 1
            if len(edge["atomic_path_examples"]) < 3:
                edge["atomic_path_examples"].append(list(entry["path_nodes"]))

    hydrated_modules: list[dict[str, Any]] = []
    for module, stats in module_stats.items():
        top_bundle = stats["bundle_counts"].most_common(1)[0][0] if stats["bundle_counts"] else ""
        motif_rows = [
            {"signature": signature, "count": count}
            for signature, count in stats["motif_counts"].most_common(3)
        ]
        hydrated_modules.append(
            {
                "module": module,
                "sink_role": module_role(set(stats["roles"])),
                "supporting_atomic_decls": sorted(stats["atomic_support"])[:12],
                "minimal_source_bundle": top_bundle,
                "canonical_downstream_sink_family": sorted(stats["sink_modules"])[:8],
                "path_multiplicity": int(stats["path_multiplicity"]),
                "path_motif_signatures": motif_rows,
                "compression_potential": round(float(stats["compression_potential"]), 3),
            }
        )
    hydrated_modules.sort(
        key=lambda row: (
            -float(row["compression_potential"]),
            -int(row["path_multiplicity"]),
            row["module"],
        )
    )

    hydrated_edges: list[dict[str, Any]] = []
    for (src_module, dst_module), stats in edge_stats.items():
        hydrated_edges.append(
            {
                "source_module": src_module,
                "target_module": dst_module,
                "path_count": int(stats["path_count"]),
                "compression_potential": round(float(stats["compression_potential"]), 3),
                "direct_projection": True,
                "hypothesis_packets": [
                    {"signature": signature, "count": count}
                    for signature, count in stats["motif_counts"].most_common(3)
                ],
                "bundle_ids": [bundle_id for bundle_id, _ in stats["bundle_counts"].most_common(3)],
                "atomic_path_examples": stats["atomic_path_examples"],
            }
        )
    hydrated_edges.sort(
        key=lambda row: (
            -float(row["compression_potential"]),
            -int(row["path_count"]),
            row["source_module"],
            row["target_module"],
        )
    )
    return hydrated_modules, hydrated_edges


def build_bipartite_artifact(
    decl_graph: nx.DiGraph,
    bundle_rows: list[dict[str, Any]],
    bundle_ids: dict[tuple[str, ...], str],
    entries: list[dict[str, Any]],
    hydrated_modules: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    hydrated_by_module = {row["module"]: row for row in hydrated_modules}
    incidence: dict[tuple[str, str, str], dict[str, Any]] = {}

    for entry in entries:
        bundle_key = tuple(entry["source_bundle"])
        bundle_id = bundle_ids[bundle_key]
        bundle_source_modules = {
            str(decl_graph.nodes[node].get("module", "unknown")) for node in entry["source_bundle"]
        }
        for module in collapse_consecutive(list(entry["path_modules"])):
            carrier_role = "sink" if module == entry["sink_module"] else "source" if module in bundle_source_modules else "transport"
            key = (bundle_id, module, carrier_role)
            stats = incidence.setdefault(
                key,
                {
                    "atomic_id": bundle_id,
                    "hydrated_id": module,
                    "role": "supports",
                    "carrier_role": carrier_role,
                    "projection_kind": "node_support",
                    "bundle_id": bundle_id,
                    "motif_counts": Counter(),
                    "witness_count": 0,
                    "compression_score": 0.0,
                    "canonical_witness_paths": [],
                    "sink_names": set(),
                    "sink_modules": set(),
                },
            )
            stats["motif_counts"][str(entry["motif_signature_text"])] += 1
            stats["witness_count"] += 1
            stats["compression_score"] += float(entry["compression_potential"])
            stats["sink_names"].add(str(entry["sink"]))
            stats["sink_modules"].add(str(entry["sink_module"]))
            if len(stats["canonical_witness_paths"]) < 3:
                stats["canonical_witness_paths"].append(list(entry["path_nodes"]))

    atomic_nodes: list[dict[str, Any]] = []
    for row in bundle_rows:
        bundle_decls = list(row["source_bundle"])
        bundle_categories = Counter(str(decl_graph.nodes[name].get("surface_category", "unknown")) for name in bundle_decls)
        bundle_kinds = Counter(str(decl_graph.nodes[name].get("kind", "unknown")) for name in bundle_decls)
        constructive_count = sum(1 for name in bundle_decls if str(decl_graph.nodes[name].get("surface_category", "unknown")) == "likely_constructive")
        atomic_nodes.append(
            {
                "atomic_id": str(row["bundle_id"]),
                "kind": "source_bundle",
                "category": "source_bundle",
                "source_bundle": bundle_decls,
                "supporting_atomic_decls": bundle_decls,
                "source_modules": list(row["source_modules"]),
                "source_categories": dict(sorted(bundle_categories.items())),
                "source_kinds": dict(sorted(bundle_kinds.items())),
                "source_purity_score": round(constructive_count / max(len(bundle_decls), 1), 4),
                "scc_id": None,
                "sink_modules": list(row["sink_modules"]),
                "sink_names": list(row["sink_names"]),
                "path_multiplicity": int(row["path_multiplicity"]),
                "avg_path_length": float(row["avg_path_length"]),
                "motif_signature": str(row["motif_signature"]),
                "compression_potential": float(row["compression_potential"]),
            }
        )

    hydrated_nodes: list[dict[str, Any]] = []
    for row in hydrated_modules:
        hydrated_nodes.append(
            {
                "hydrated_id": str(row["module"]),
                "kind": "module",
                "carrier_type": "module",
                "module": str(row["module"]),
                "sink_role": str(row["sink_role"]),
                "supporting_atomic_decls": list(row["supporting_atomic_decls"]),
                "minimal_source_bundle": str(row["minimal_source_bundle"]),
                "canonical_downstream_sink_family": list(row["canonical_downstream_sink_family"]),
                "path_multiplicity": int(row["path_multiplicity"]),
                "path_motif_signatures": list(row["path_motif_signatures"]),
                "compression_potential": float(row["compression_potential"]),
            }
        )

    incidence_edges: list[dict[str, Any]] = []
    for (_, _, _), stats in incidence.items():
        hydrated = hydrated_by_module.get(stats["hydrated_id"], {})
        top_motif = stats["motif_counts"].most_common(1)[0][0] if stats["motif_counts"] else ""
        canonical_paths = list(stats["canonical_witness_paths"])
        incidence_edges.append(
            {
                "atomic_id": str(stats["atomic_id"]),
                "hydrated_id": str(stats["hydrated_id"]),
                "role": str(stats["role"]),
                "projection_kind": str(stats["projection_kind"]),
                "carrier_role": str(stats["carrier_role"]),
                "bundle_id": str(stats["bundle_id"]),
                "motif_signature": top_motif,
                "witness_count": int(stats["witness_count"]),
                "compression_score": round(float(stats["compression_score"]), 3),
                "canonical_path_example": canonical_paths[0] if canonical_paths else [],
                "canonical_witness_paths": canonical_paths,
                "sink_names": sorted(stats["sink_names"]),
                "sink_modules": sorted(stats["sink_modules"]),
                "hydrated_role": str(hydrated.get("sink_role", "unknown")),
            }
        )
    incidence_edges.sort(
        key=lambda row: (
            -float(row["compression_score"]),
            -int(row["witness_count"]),
            row["atomic_id"],
            row["hydrated_id"],
            row["role"],
        )
    )
    return atomic_nodes, hydrated_nodes, incidence_edges


def build_incidence_graph(
    decl_graph: nx.DiGraph,
    bundle_rows: list[dict[str, Any]],
    bundle_ids: dict[tuple[str, ...], str],
    entries: list[dict[str, Any]],
    *,
    top_bundles: int,
) -> nx.DiGraph:
    selected_bundle_rows = bundle_rows[: max(top_bundles, 1)]
    selected_bundle_ids = {row["bundle_id"] for row in selected_bundle_rows}
    graph = nx.DiGraph()
    bundle_lookup = {row["bundle_id"]: row for row in selected_bundle_rows}

    for row in selected_bundle_rows:
        graph.add_node(
            row["bundle_id"],
            kind="bundle",
            layer=1,
            label=f"{row['bundle_id']}: {row['motif_signature'] or 'bundle'}",
            compression_potential=float(row["compression_potential"]),
            path_multiplicity=int(row["path_multiplicity"]),
        )

    sink_to_bundle_id = {
        str(entry["sink"]): bundle_ids[tuple(entry["source_bundle"])]
        for entry in entries
        if bundle_ids[tuple(entry["source_bundle"])] in selected_bundle_ids
    }

    for row in selected_bundle_rows:
        bundle_id = str(row["bundle_id"])
        for source in row["source_bundle"]:
            graph.add_node(
                source,
                kind="source",
                layer=0,
                label=short_name(source),
                module=str(decl_graph.nodes[source].get("module", "unknown")),
                surface_category=str(decl_graph.nodes[source].get("surface_category", "unknown")),
            )
            graph.add_edge(source, bundle_id, relation="supports")

        for sink in row["sink_names"]:
            graph.add_node(
                sink,
                kind="sink",
                layer=2,
                label=short_name(sink),
                module=str(decl_graph.nodes[sink].get("module", "unknown")),
                surface_category=str(decl_graph.nodes[sink].get("surface_category", "unknown")),
            )
            graph.add_edge(bundle_id, sink, relation="generates")

    for sink, bundle_id in sink_to_bundle_id.items():
        graph.nodes[sink]["bundle_id"] = bundle_id
        graph.nodes[sink]["bundle_label"] = str(bundle_lookup[bundle_id]["motif_signature"])
    return graph


def plot_incidence_graph(graph: nx.DiGraph, out_path: Path) -> None:
    if graph.number_of_nodes() == 0:
        raise SystemExit("source-sink incidence graph is empty")

    layer_nodes: dict[int, list[str]] = defaultdict(list)
    for node, data in graph.nodes(data=True):
        layer_nodes[int(data.get("layer", 1))].append(node)

    pos: dict[str, tuple[float, float]] = {}
    for layer, nodes in sorted(layer_nodes.items()):
        ordered = sorted(
            nodes,
            key=lambda node: (
                -float(graph.nodes[node].get("compression_potential", 0.0)),
                graph.nodes[node].get("label", node),
            ),
        )
        count = len(ordered)
        for idx, node in enumerate(ordered):
            y = 0.0 if count == 1 else 1.0 - (2.0 * idx / max(count - 1, 1))
            pos[node] = (float(layer), y)

    fig, ax = plt.subplots(figsize=(20, max(10, 6 + graph.number_of_nodes() / 5)))
    ax.set_axis_off()

    nx.draw_networkx_edges(
        graph,
        pos,
        ax=ax,
        arrows=True,
        arrowstyle="-|>",
        arrowsize=10,
        width=0.8,
        alpha=0.22,
        edge_color="#666666",
        connectionstyle="arc3,rad=0.04",
    )

    node_colors = [SIDE_COLORS.get(str(graph.nodes[node].get("kind", "bundle")), "#4C78A8") for node in graph.nodes()]
    node_sizes: list[float] = []
    for node in graph.nodes():
        kind = str(graph.nodes[node].get("kind", "bundle"))
        if kind == "bundle":
            node_sizes.append(260 + 12 * math.sqrt(max(float(graph.nodes[node].get("compression_potential", 1.0)), 1.0)))
        else:
            node_sizes.append(160)
    nx.draw_networkx_nodes(
        graph,
        pos,
        ax=ax,
        node_size=node_sizes,
        node_color=node_colors,
        linewidths=0.6,
        edgecolors="#111111",
        alpha=0.96,
    )
    labels = {node: str(graph.nodes[node].get("label", short_name(node))) for node in graph.nodes()}
    nx.draw_networkx_labels(graph, pos, ax=ax, labels=labels, font_size=6)

    from matplotlib.lines import Line2D

    legend_handles = [
        Line2D([0], [0], marker="o", color="w", label=kind, markerfacecolor=color, markeredgecolor="#111111", markersize=8)
        for kind, color in SIDE_COLORS.items()
    ]
    ax.legend(handles=legend_handles, title="Incidence-layer role", loc="upper left", frameon=False)
    ax.set_title("InfoGeometry source-bundle / sink-bundle incidence layer")
    fig.tight_layout()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, format="svg", bbox_inches="tight")
    plt.close(fig)


def render_markdown(
    hotspot_rows: list[dict[str, Any]],
    source_rows: list[dict[str, Any]],
    sink_rows: list[dict[str, Any]],
    bundle_rows: list[dict[str, Any]],
    motif_rows: list[dict[str, Any]],
    hydrated_modules: list[dict[str, Any]],
    hydrated_edges: list[dict[str, Any]],
) -> str:
    lines: list[str] = []
    lines.append("# Source-Sink Compression Report")
    lines.append("")
    lines.append("Model:")
    lines.append("- atomic graph: declaration-to-declaration DAG under `artifacts/dag/full_graph.json`")
    lines.append("- incidence layer: source bundles -> sink theorems grouped by canonical atomic support paths")
    lines.append("- bundle ids are content-stable hashes of sorted bundle members, not rank-based labels")
    lines.append("- hydrated projection: module-level carriers enriched with source bundles, sink families, motifs, and compression potential")
    lines.append("")
    lines.append("Flow orientation:")
    lines.append("- this report reverses the declaration dependency arrows into generative flow: constructive sources -> downstream sinks")
    lines.append("")
    lines.append("## Hotspot Modules")
    for row in hotspot_rows[:8]:
        lines.append(
            f"- `#{row['burn_down_rank']} {row['module']}`"
            f" score={float(row['burn_down_score']):.3f}"
            f" mix={int(row['hypothesis_bridge'])}/{int(row['package_reprojection'])}/{int(row['surrogate_or_vacuous'])}"
        )
    lines.append("")
    lines.append("## Canonical Sources")
    for row in source_rows[:10]:
        lines.append(
            f"- `{row['name']}`"
            f" score={float(row['source_score']):.3f}"
            f" reachable_sinks={int(row['reachable_sinks'])}"
            f" closest_distance={int(row['closest_sink_distance'])}"
        )
    lines.append("")
    lines.append("## Selected Sinks")
    for row in sink_rows[:12]:
        lines.append(
            f"- `{row['name']}`"
            f" category=`{row['category']}`"
            f" hotspot_rank={int(row['burn_down_rank'])}"
            f" flow_out_degree={int(row['flow_out_degree'])}"
        )
    lines.append("")
    lines.append("## Top Source Bundles")
    lines.append("")
    lines.append("| Rank | Bundle | Sources | Sinks | Avg path | Compression | Motif |")
    lines.append("| --- | --- | --- | ---: | ---: | ---: | --- |")
    for rank, row in enumerate(bundle_rows[:12], start=1):
        sources = ", ".join(f"`{short_name(name)}`" for name in row["source_bundle"][:3]) or "-"
        lines.append(
            f"| {rank} | `{row['bundle_id']}` | {sources} | {int(row['sink_count'])} | "
            f"{float(row['avg_path_length']):.3f} | {float(row['compression_potential']):.3f} | "
            f"`{row['motif_signature']}` |"
        )
    lines.append("")
    lines.append("## Repeated Path Motifs")
    lines.append("")
    lines.append("| Rank | Motif signature | Paths | Avg path | Compression |")
    lines.append("| --- | --- | ---: | ---: | ---: |")
    for rank, row in enumerate(motif_rows[:12], start=1):
        lines.append(
            f"| {rank} | `{row['motif_signature']}` | {int(row['path_count'])} | "
            f"{float(row['avg_path_length']):.3f} | {float(row['compression_potential']):.3f} |"
        )
    lines.append("")
    lines.append("## Hydrated Module Projection")
    lines.append("")
    lines.append("| Rank | Module | Role | Paths | Compression | Source bundle | Top motif |")
    lines.append("| --- | --- | --- | ---: | ---: | --- | --- |")
    for rank, row in enumerate(hydrated_modules[:15], start=1):
        top_motif = row["path_motif_signatures"][0]["signature"] if row["path_motif_signatures"] else ""
        lines.append(
            f"| {rank} | `{row['module']}` | `{row['sink_role']}` | {int(row['path_multiplicity'])} | "
            f"{float(row['compression_potential']):.3f} | `{row['minimal_source_bundle']}` | `{top_motif}` |"
        )
    lines.append("")
    lines.append("## Hydrated Edge Projection")
    for row in hydrated_edges[:12]:
        packet = row["hypothesis_packets"][0]["signature"] if row["hypothesis_packets"] else ""
        lines.append(
            f"- `{row['source_module']} -> {row['target_module']}`"
            f" paths={int(row['path_count'])}"
            f" compression={float(row['compression_potential']):.3f}"
            f" packet=`{packet}`"
        )
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    root = repo_root()
    graph_path = normalize_user_path(args.graph, root)
    decls_path = normalize_user_path(args.decls, root)
    surface_index_path = normalize_user_path(args.surface_index, root)
    md_out = normalize_user_path(args.md_out, root)
    json_out = normalize_user_path(args.json_out, root)
    artifact_out = normalize_user_path(args.artifact_out, root)
    graphml_out = normalize_user_path(args.graphml_out, root)
    svg_out = normalize_user_path(args.svg_out, root)

    decl_meta = load_decl_meta(decls_path, root)
    surface_categories = load_surface_categories(surface_index_path, decl_meta)
    decl_graph = build_declaration_graph(graph_path, decl_meta, surface_categories)
    flow_graph = decl_graph.reverse(copy=True)
    frontier_decl_graph = filter_declaration_graph_by_surface(decl_graph, FRONTIER_CATEGORIES)
    frontier_module_graph = build_module_graph(frontier_decl_graph)
    hotspot_rows = select_hotspot_modules(frontier_module_graph, args.hotspot_module_count)
    sink_rows = select_sink_rows(
        decl_graph,
        flow_graph,
        hotspot_rows,
        sink_per_module=args.sink_per_module,
        max_sinks=args.max_sinks,
    )
    source_stats, sink_to_candidates = collect_source_stats(
        decl_graph,
        flow_graph,
        sink_rows,
        max_depth=args.max_path_depth,
    )
    source_rows = sorted(
        source_stats.values(),
        key=lambda row: (
            -float(row["source_score"]),
            -int(row["reachable_sinks"]),
            int(row["closest_sink_distance"]),
            row["name"],
        ),
    )
    entries = build_canonical_paths(decl_graph, sink_rows, sink_to_candidates, source_stats)
    bundle_rows, bundle_ids = summarize_bundles(entries)
    motif_rows = summarize_motif_families(entries)
    hydrated_modules, hydrated_edges = summarize_hydrated_projection(decl_graph, entries, bundle_ids)
    atomic_nodes, hydrated_nodes, incidence_edges = build_bipartite_artifact(
        decl_graph,
        bundle_rows,
        bundle_ids,
        entries,
        hydrated_modules,
    )
    incidence_graph = build_incidence_graph(
        decl_graph,
        bundle_rows,
        bundle_ids,
        entries,
        top_bundles=args.top_bundles,
    )

    payload = {
        "schema_version": 1,
        "kind": "source_sink_bipartite",
        "model": {
            "atomic_graph": str(graph_path.relative_to(root)),
            "surface_index": str(surface_index_path.relative_to(root)),
            "incidence_layer": "canonical source bundles -> sink theorems via shortest atomic support paths",
            "hydrated_projection": "module carriers enriched with source bundles, sink families, motifs, and compression potential",
            "flow_orientation": "constructive sources -> downstream sinks",
        },
        "selection": {
            "hotspot_module_count": int(args.hotspot_module_count),
            "sink_per_module": int(args.sink_per_module),
            "max_sinks": int(args.max_sinks),
            "max_path_depth": int(args.max_path_depth),
        },
        "hotspot_modules": hotspot_rows,
        "source_nodes": source_rows,
        "sink_nodes": sink_rows,
        "incidence_entries": entries,
        "atomic_nodes": atomic_nodes,
        "hydrated_nodes": hydrated_nodes,
        "incidence_edges": incidence_edges,
        "motif_families": motif_rows,
        "bundles": atomic_nodes,
        "hydrated_modules": hydrated_nodes,
        "hydrated_edges": hydrated_edges,
    }

    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    artifact_out.parent.mkdir(parents=True, exist_ok=True)
    graphml_out.parent.mkdir(parents=True, exist_ok=True)
    svg_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(
        render_markdown(
            hotspot_rows,
            source_rows,
            sink_rows,
            bundle_rows,
            motif_rows,
            hydrated_modules,
            hydrated_edges,
        ),
        encoding="utf-8",
    )
    artifact_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    nx.write_graphml(incidence_graph, graphml_out)
    plot_incidence_graph(incidence_graph, svg_out)

    print(f"[source-sink-compression] wrote {md_out}")
    print(f"[source-sink-compression] wrote {artifact_out}")
    print(f"[source-sink-compression] wrote {json_out}")
    print(f"[source-sink-compression] wrote {graphml_out}")
    print(f"[source-sink-compression] wrote {svg_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
