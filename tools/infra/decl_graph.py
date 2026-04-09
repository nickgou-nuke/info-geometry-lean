#!/usr/bin/env python3
from __future__ import annotations

import json
import math
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

import networkx as nx


FRONTIER_CATEGORIES = {
    "hypothesis_bridge",
    "package_reprojection",
    "surrogate_or_vacuous",
}
CATEGORY_ORDER = [
    "likely_constructive",
    "hypothesis_bridge",
    "package_reprojection",
    "surrogate_or_vacuous",
    "neutral_definition",
    "unknown",
]
BURN_DOWN_WEIGHTS = {
    "surrogate_or_vacuous": 4.0,
    "package_reprojection": 2.0,
    "hypothesis_bridge": 1.0,
}


def normalize_repo_relative(root: Path, raw: Any) -> str:
    value = str(raw or "").strip()
    if not value or value == "unknown":
        return value
    candidate = Path(value)
    if candidate.is_absolute():
        try:
            return str(candidate.resolve().relative_to(root))
        except ValueError:
            return value
    if str(candidate).startswith("lean/"):
        return str(candidate)
    lean_candidate = root / "lean" / candidate
    if lean_candidate.exists():
        return str(Path("lean") / candidate)
    return str(candidate)


def load_decl_meta(path: Path, root: Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line:
            continue
        obj = json.loads(line)
        name = str(obj.get("name", "")).strip()
        if not name:
            continue
        out[name] = {
            "module": str(obj.get("module", "")).strip() or name.rsplit(".", 1)[0],
            "file": normalize_repo_relative(root, obj.get("file", "")),
            "kind": str(obj.get("kind", "")).strip() or "unknown",
            "line": int(obj["line"]) if obj.get("line") is not None else -1,
        }
    return out


def load_surface_categories(path: Path, decl_meta: dict[str, dict[str, Any]]) -> dict[str, str]:
    if not path.exists():
        return {name: "unknown" for name in decl_meta}
    payload = json.loads(path.read_text(encoding="utf-8"))
    categories = {name: "unknown" for name in decl_meta}
    for row in payload.get("rows", []):
        name = str(row.get("name", "")).strip()
        category = str(row.get("category", "unknown")).strip() or "unknown"
        if name:
            categories[name] = category
    return categories


def build_declaration_graph(
    graph_path: Path,
    decl_meta: dict[str, dict[str, Any]],
    surface_categories: dict[str, str],
) -> nx.DiGraph:
    payload = json.loads(graph_path.read_text(encoding="utf-8"))
    nodes = payload["nodes"]
    forward = payload["forward"]
    graph = nx.DiGraph()

    for name in nodes:
        meta = decl_meta.get(name, {})
        graph.add_node(
            name,
            module=str(meta.get("module", name.rsplit(".", 1)[0])),
            file=str(meta.get("file", "")),
            kind=str(meta.get("kind", "unknown")),
            line=int(meta.get("line", -1)),
            surface_category=surface_categories.get(name, "unknown"),
        )

    for src_idx, outgoing in enumerate(forward):
        src_name = nodes[src_idx]
        by_target: dict[int, set[str]] = defaultdict(set)
        for target_idx, edge_kind in outgoing:
            by_target[int(target_idx)].add(str(edge_kind))
        for target_idx, kinds in by_target.items():
            tgt_name = nodes[target_idx]
            graph.add_edge(
                src_name,
                tgt_name,
                kinds=",".join(sorted(kinds)),
                weight=len(kinds),
            )
    return graph


def dominant_category(counter: Counter[str]) -> str:
    for category in CATEGORY_ORDER:
        if counter.get(category, 0):
            return category
    return "unknown"


def build_module_graph(graph: nx.DiGraph) -> nx.DiGraph:
    module_surface_counts: dict[str, Counter[str]] = defaultdict(Counter)
    module_decl_counts: Counter[str] = Counter()

    for _, data in graph.nodes(data=True):
        module = str(data.get("module", "unknown"))
        module_decl_counts[module] += 1
        module_surface_counts[module][str(data.get("surface_category", "unknown"))] += 1

    module_graph = nx.DiGraph()
    for module, decl_count in module_decl_counts.items():
        counts = module_surface_counts[module]
        module_graph.add_node(
            module,
            decl_count=decl_count,
            dominant_surface=dominant_category(counts),
            likely_constructive=int(counts.get("likely_constructive", 0)),
            hypothesis_bridge=int(counts.get("hypothesis_bridge", 0)),
            package_reprojection=int(counts.get("package_reprojection", 0)),
            surrogate_or_vacuous=int(counts.get("surrogate_or_vacuous", 0)),
            neutral_definition=int(counts.get("neutral_definition", 0)),
            unknown=int(counts.get("unknown", 0)),
        )

    for src, tgt, data in graph.edges(data=True):
        src_module = str(graph.nodes[src].get("module", "unknown"))
        tgt_module = str(graph.nodes[tgt].get("module", "unknown"))
        if module_graph.has_edge(src_module, tgt_module):
            module_graph[src_module][tgt_module]["weight"] += 1
            kinds = set(filter(None, module_graph[src_module][tgt_module].get("kinds", "").split(",")))
            kinds.update(filter(None, str(data.get("kinds", "")).split(",")))
            module_graph[src_module][tgt_module]["kinds"] = ",".join(sorted(kinds))
        else:
            module_graph.add_edge(
                src_module,
                tgt_module,
                weight=1,
                kinds=str(data.get("kinds", "")),
            )
    return module_graph


def load_decl_graph_bundle(
    *,
    root: Path,
    graph_path: Path,
    decls_path: Path,
    surface_index_path: Path,
    frontier_categories: set[str] | None = None,
) -> dict[str, Any]:
    decl_meta = load_decl_meta(decls_path, root)
    surface_categories = load_surface_categories(surface_index_path, decl_meta)
    decl_graph = build_declaration_graph(graph_path, decl_meta, surface_categories)
    bundle: dict[str, Any] = {
        "decl_meta": decl_meta,
        "surface_categories": surface_categories,
        "decl_graph": decl_graph,
    }
    if frontier_categories is not None:
        frontier_decl_graph = filter_declaration_graph_by_surface(decl_graph, frontier_categories)
        bundle["frontier_decl_graph"] = frontier_decl_graph
        bundle["frontier_module_graph"] = build_module_graph(frontier_decl_graph)
    return bundle


def filter_declaration_graph_by_surface(graph: nx.DiGraph, categories: set[str]) -> nx.DiGraph:
    selected_nodes = [
        node
        for node, data in graph.nodes(data=True)
        if str(data.get("surface_category", "unknown")) in categories
    ]
    return graph.subgraph(selected_nodes).copy()


def module_strength_rows(graph: nx.DiGraph) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for node, data in graph.nodes(data=True):
        out_weight = sum(int(graph[node][nbr].get("weight", 1)) for nbr in graph.successors(node))
        in_weight = sum(int(graph[pred][node].get("weight", 1)) for pred in graph.predecessors(node))
        rows.append(
            {
                "module": node,
                "strength": out_weight + in_weight,
                "out_weight": out_weight,
                "in_weight": in_weight,
                "decl_count": int(data.get("decl_count", 0)),
                "dominant_surface": str(data.get("dominant_surface", "unknown")),
                "hypothesis_bridge": int(data.get("hypothesis_bridge", 0)),
                "package_reprojection": int(data.get("package_reprojection", 0)),
                "surrogate_or_vacuous": int(data.get("surrogate_or_vacuous", 0)),
            }
        )
    rows.sort(key=lambda row: (-row["strength"], -row["surrogate_or_vacuous"], row["module"]))
    return rows


def select_plot_subgraph(graph: nx.DiGraph, top_n: int) -> nx.DiGraph:
    selected = [row["module"] for row in module_strength_rows(graph)[: max(top_n, 1)]]
    if not selected:
        return graph.copy()
    return graph.subgraph(selected).copy()


def replaceable_surface_mass(row: dict[str, Any]) -> float:
    return (
        BURN_DOWN_WEIGHTS["surrogate_or_vacuous"] * float(row.get("surrogate_or_vacuous", 0))
        + BURN_DOWN_WEIGHTS["package_reprojection"] * float(row.get("package_reprojection", 0))
        + BURN_DOWN_WEIGHTS["hypothesis_bridge"] * float(row.get("hypothesis_bridge", 0))
    )


def support_pressure(row: dict[str, Any]) -> float:
    return (2.0 * float(row.get("in_weight", 0))) + float(row.get("out_weight", 0))


def dominant_pressure(row: dict[str, Any]) -> str:
    weighted = {
        "surrogate_or_vacuous": BURN_DOWN_WEIGHTS["surrogate_or_vacuous"] * float(row.get("surrogate_or_vacuous", 0)),
        "package_reprojection": BURN_DOWN_WEIGHTS["package_reprojection"] * float(row.get("package_reprojection", 0)),
        "hypothesis_bridge": BURN_DOWN_WEIGHTS["hypothesis_bridge"] * float(row.get("hypothesis_bridge", 0)),
    }
    name, value = max(weighted.items(), key=lambda item: (item[1], item[0]))
    return name if value > 0 else "unknown"


def primary_action(row: dict[str, Any]) -> str:
    surrogate = int(row.get("surrogate_or_vacuous", 0))
    package = int(row.get("package_reprojection", 0))
    hypothesis = int(row.get("hypothesis_bridge", 0))
    if surrogate > 0 and package > 0:
        return "replace surrogates, then collapse package layer"
    if surrogate > 0:
        return "direct constructive replacement"
    if package > 0 and hypothesis > 0:
        return "construct witnesses behind packaged hypotheses"
    if package > 0:
        return "collapse package layer"
    if hypothesis > 0:
        return "discharge hypothesis bridges"
    return "inspect manually"


def burn_down_rows(hotspot_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for hotspot_rank, row in enumerate(hotspot_rows, start=1):
        weighted_mass = replaceable_surface_mass(row)
        pressure = support_pressure(row)
        score = weighted_mass * math.log1p(max(pressure, 0.0))
        decl_count = int(row.get("decl_count", 0))
        rows.append(
            {
                **row,
                "hotspot_rank": hotspot_rank,
                "replaceable_surface_mass": round(weighted_mass, 3),
                "support_pressure": round(pressure, 3),
                "burn_down_score": round(score, 3),
                "dominant_pressure": dominant_pressure(row),
                "primary_action": primary_action(row),
                "surrogate_share": round(float(row.get("surrogate_or_vacuous", 0)) / decl_count, 4) if decl_count else 0.0,
                "package_share": round(float(row.get("package_reprojection", 0)) / decl_count, 4) if decl_count else 0.0,
                "hypothesis_share": round(float(row.get("hypothesis_bridge", 0)) / decl_count, 4) if decl_count else 0.0,
            }
        )
    rows.sort(
        key=lambda row: (
            -float(row["burn_down_score"]),
            -float(row["replaceable_surface_mass"]),
            -float(row["in_weight"]),
            row["module"],
        )
    )
    for burn_down_rank, row in enumerate(rows, start=1):
        row["burn_down_rank"] = burn_down_rank
    return rows


def annotate_hotspot_graph(graph: nx.DiGraph, burn_rows: list[dict[str, Any]]) -> None:
    by_module = {row["module"]: row for row in burn_rows}
    for node in graph.nodes():
        row = by_module.get(node)
        if not row:
            continue
        graph.nodes[node]["burn_down_rank"] = int(row["burn_down_rank"])
        graph.nodes[node]["hotspot_rank"] = int(row["hotspot_rank"])
        graph.nodes[node]["burn_down_score"] = float(row["burn_down_score"])
        graph.nodes[node]["replaceable_surface_mass"] = float(row["replaceable_surface_mass"])
        graph.nodes[node]["support_pressure"] = float(row["support_pressure"])
        graph.nodes[node]["dominant_pressure"] = str(row["dominant_pressure"])
        graph.nodes[node]["primary_action"] = str(row["primary_action"])
        graph.nodes[node]["hotspot_rank_label"] = f"#{row['burn_down_rank']} {node.split('.')[-1]}"
