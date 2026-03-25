#!/usr/bin/env python3
from __future__ import annotations

import argparse
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
    from tools.pathing import default_decl_graph_file, default_decl_metadata_file, repo_root
else:
    from tools.pathing import default_decl_graph_file, default_decl_metadata_file, repo_root


DEFAULT_GRAPH = str(default_decl_graph_file().relative_to(repo_root()))
DEFAULT_DECLS = str(default_decl_metadata_file().relative_to(repo_root()))
DEFAULT_SURFACE_INDEX = "reports/dag/theorem-surface-index.json"
DEFAULT_DECL_GRAPHML_OUT = "reports/dag/declaration-networkx.graphml"
DEFAULT_MODULE_GRAPHML_OUT = "reports/dag/module-networkx.graphml"
DEFAULT_MODULE_SVG_OUT = "reports/dag/module-networkx.svg"
DEFAULT_FRONTIER_DECL_GRAPHML_OUT = "reports/dag/declaration-networkx-frontier.graphml"
DEFAULT_FRONTIER_MODULE_GRAPHML_OUT = "reports/dag/module-networkx-frontier.graphml"
DEFAULT_FRONTIER_MODULE_SVG_OUT = "reports/dag/module-networkx-frontier.svg"
DEFAULT_FRONTIER_HOTSPOT_GRAPHML_OUT = "reports/dag/module-networkx-frontier-hotspots.graphml"
DEFAULT_FRONTIER_HOTSPOT_SVG_OUT = "reports/dag/module-networkx-frontier-hotspots.svg"
DEFAULT_FRONTIER_HOTSPOT_JSON_OUT = "reports/dag/module-networkx-frontier-hotspots.json"
DEFAULT_FRONTIER_BURNDOWN_MD_OUT = "reports/dag/frontier-burndown.md"
DEFAULT_FRONTIER_BURNDOWN_JSON_OUT = "reports/dag/frontier-burndown.json"
DEFAULT_SUMMARY_OUT = "reports/dag/networkx-graph-summary.json"
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
CATEGORY_COLORS = {
    "likely_constructive": "#2E8B57",
    "hypothesis_bridge": "#E69F00",
    "package_reprojection": "#CC79A7",
    "surrogate_or_vacuous": "#D55E00",
    "neutral_definition": "#7A7A7A",
    "unknown": "#4C78A8",
}
BURN_DOWN_WEIGHTS = {
    "surrogate_or_vacuous": 4.0,
    "package_reprojection": 2.0,
    "hypothesis_bridge": 1.0,
}


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Export the authoritative declaration DAG into NetworkX artifacts and render readable module-level graph views."
    )
    ap.add_argument("--graph", default=DEFAULT_GRAPH, help="Declaration DAG JSON from the Lean Indexer.")
    ap.add_argument("--decls", default=DEFAULT_DECLS, help="Declaration metadata JSONL.")
    ap.add_argument(
        "--surface-index",
        default=DEFAULT_SURFACE_INDEX,
        help="Optional theorem-surface classification JSON for node/module coloring.",
    )
    ap.add_argument("--decl-graphml-out", default=DEFAULT_DECL_GRAPHML_OUT)
    ap.add_argument("--module-graphml-out", default=DEFAULT_MODULE_GRAPHML_OUT)
    ap.add_argument("--module-svg-out", default=DEFAULT_MODULE_SVG_OUT)
    ap.add_argument("--frontier-decl-graphml-out", default=DEFAULT_FRONTIER_DECL_GRAPHML_OUT)
    ap.add_argument("--frontier-module-graphml-out", default=DEFAULT_FRONTIER_MODULE_GRAPHML_OUT)
    ap.add_argument("--frontier-module-svg-out", default=DEFAULT_FRONTIER_MODULE_SVG_OUT)
    ap.add_argument("--frontier-hotspot-graphml-out", default=DEFAULT_FRONTIER_HOTSPOT_GRAPHML_OUT)
    ap.add_argument("--frontier-hotspot-svg-out", default=DEFAULT_FRONTIER_HOTSPOT_SVG_OUT)
    ap.add_argument("--frontier-hotspot-json-out", default=DEFAULT_FRONTIER_HOTSPOT_JSON_OUT)
    ap.add_argument("--frontier-burndown-md-out", default=DEFAULT_FRONTIER_BURNDOWN_MD_OUT)
    ap.add_argument("--frontier-burndown-json-out", default=DEFAULT_FRONTIER_BURNDOWN_JSON_OUT)
    ap.add_argument("--summary-out", default=DEFAULT_SUMMARY_OUT)
    ap.add_argument("--plot-top-modules", type=int, default=80, help="How many modules to include in the readable full-graph plot.")
    ap.add_argument(
        "--plot-top-frontier-modules",
        type=int,
        default=60,
        help="How many modules to include in the readable theorem-surface frontier plot.",
    )
    ap.add_argument(
        "--frontier-hotspot-count",
        type=int,
        default=20,
        help="How many top frontier hotspot modules to isolate in the dedicated hotspot view.",
    )
    return ap.parse_args()


def normalize_user_path(path: str, root: Path) -> Path:
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate.resolve()
    return (root / candidate).resolve()


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


def plot_module_graph(
    graph: nx.DiGraph,
    out_path: Path,
    *,
    title: str,
    label_attr: str | None = None,
    size_attr: str = "decl_count",
) -> None:
    if graph.number_of_nodes() == 0:
        raise SystemExit("module graph is empty")

    undirected = graph.to_undirected()
    pos = nx.spring_layout(undirected, seed=7, k=1.4 / math.sqrt(max(graph.number_of_nodes(), 1)), iterations=200)
    fig_w = max(14, min(28, 10 + graph.number_of_nodes() / 6))
    fig_h = max(10, min(22, 8 + graph.number_of_nodes() / 8))
    fig, ax = plt.subplots(figsize=(fig_w, fig_h))
    ax.set_axis_off()

    edge_widths = [0.6 + math.log1p(int(data.get("weight", 1))) for _, _, data in graph.edges(data=True)]
    nx.draw_networkx_edges(
        graph,
        pos,
        ax=ax,
        arrows=True,
        arrowstyle="-|>",
        arrowsize=10,
        width=edge_widths,
        alpha=0.18,
        edge_color="#555555",
        connectionstyle="arc3,rad=0.08",
    )

    node_sizes: list[float] = []
    for node in graph.nodes():
        raw_value = float(graph.nodes[node].get(size_attr, graph.nodes[node].get("decl_count", 1)) or 1)
        if size_attr == "burn_down_score":
            node_sizes.append(220 + 8 * math.sqrt(max(raw_value, 1.0)))
        else:
            node_sizes.append(140 + 18 * math.sqrt(max(raw_value, 1.0)))

    node_colors = [
        CATEGORY_COLORS.get(str(graph.nodes[node].get("dominant_surface", "unknown")), CATEGORY_COLORS["unknown"])
        for node in graph.nodes()
    ]
    nx.draw_networkx_nodes(
        graph,
        pos,
        ax=ax,
        node_size=node_sizes,
        node_color=node_colors,
        linewidths=0.6,
        edgecolors="#111111",
        alpha=0.95,
    )

    labels: dict[str, str] = {}
    for node in graph.nodes():
        if label_attr:
            label = str(graph.nodes[node].get(label_attr, "")).strip()
            labels[node] = label or node.split(".")[-1]
        else:
            labels[node] = node.split(".")[-1]
    nx.draw_networkx_labels(graph, pos, ax=ax, labels=labels, font_size=6)

    from matplotlib.lines import Line2D

    legend_handles = [
        Line2D([0], [0], marker="o", color="w", label=label, markerfacecolor=color, markeredgecolor="#111111", markersize=8)
        for label, color in CATEGORY_COLORS.items()
    ]
    ax.legend(handles=legend_handles, title="Dominant theorem-surface category", loc="upper left", frameon=False)
    ax.set_title(title)

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(out_path, format="svg", bbox_inches="tight")
    plt.close(fig)


def write_hotspot_json(out_path: Path, hotspot_rows: list[dict[str, Any]], burn_down_rows_data: list[dict[str, Any]]) -> None:
    payload = {
        "hotspots": hotspot_rows,
        "burn_down_order": burn_down_rows_data,
        "formula": {
            "replaceable_surface_mass": {
                "surrogate_or_vacuous": BURN_DOWN_WEIGHTS["surrogate_or_vacuous"],
                "package_reprojection": BURN_DOWN_WEIGHTS["package_reprojection"],
                "hypothesis_bridge": BURN_DOWN_WEIGHTS["hypothesis_bridge"],
            },
            "support_pressure": "2 * in_weight + out_weight",
            "burn_down_score": "replaceable_surface_mass * log1p(support_pressure)",
            "scope": "strength-ranked top frontier hotspot modules only",
        },
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def render_burndown_markdown(rows: list[dict[str, Any]]) -> str:
    lines: list[str] = []
    lines.append("# Frontier Burn-Down Order")
    lines.append("")
    lines.append("Scope:")
    lines.append("- source set: top frontier hotspot modules selected from the theorem-surface frontier graph")
    lines.append("- hotspot selector: module strength (`in_weight + out_weight`) on the frontier module graph")
    lines.append("- burn-down selector: weighted replaceable surface mass biased toward downstream support pressure")
    lines.append("")
    lines.append("Formula:")
    lines.append(f"- `replaceable_surface_mass = {int(BURN_DOWN_WEIGHTS['surrogate_or_vacuous'])} * surrogate_or_vacuous + {int(BURN_DOWN_WEIGHTS['package_reprojection'])} * package_reprojection + {int(BURN_DOWN_WEIGHTS['hypothesis_bridge'])} * hypothesis_bridge`")
    lines.append("- `support_pressure = 2 * in_weight + out_weight`")
    lines.append("- `burn_down_score = replaceable_surface_mass * log1p(support_pressure)`")
    lines.append("")
    lines.append("## Order")
    lines.append("")
    lines.append("| Rank | Module | Score | Dominant Pressure | Mix (H/P/S) | Strength | Action |")
    lines.append("| --- | --- | ---: | --- | ---: | ---: | --- |")
    for row in rows:
        module = str(row["module"])
        score = float(row["burn_down_score"])
        mix = f"{int(row['hypothesis_bridge'])}/{int(row['package_reprojection'])}/{int(row['surrogate_or_vacuous'])}"
        lines.append(
            "| "
            f"{int(row['burn_down_rank'])} | `{module}` | {score:.3f} | {row['dominant_pressure']} | {mix} | {int(row['strength'])} | {row['primary_action']} |"
        )
    lines.append("")
    return "\n".join(lines) + "\n"


def write_burndown_reports(md_out: Path, json_out: Path, rows: list[dict[str, Any]]) -> None:
    payload = {
        "formula": {
            "replaceable_surface_mass": {
                "surrogate_or_vacuous": BURN_DOWN_WEIGHTS["surrogate_or_vacuous"],
                "package_reprojection": BURN_DOWN_WEIGHTS["package_reprojection"],
                "hypothesis_bridge": BURN_DOWN_WEIGHTS["hypothesis_bridge"],
            },
            "support_pressure": "2 * in_weight + out_weight",
            "burn_down_score": "replaceable_surface_mass * log1p(support_pressure)",
            "scope": "strength-ranked top frontier hotspot modules only",
        },
        "rows": rows,
    }
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(render_burndown_markdown(rows), encoding="utf-8")
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def write_summary(
    out_path: Path,
    decl_graph: nx.DiGraph,
    module_graph: nx.DiGraph,
    plotted_graph: nx.DiGraph,
    frontier_decl_graph: nx.DiGraph,
    frontier_module_graph: nx.DiGraph,
    frontier_plotted_graph: nx.DiGraph,
    frontier_hotspot_graph: nx.DiGraph,
    frontier_hotspot_rows: list[dict[str, Any]],
    frontier_burndown_rows: list[dict[str, Any]],
) -> None:
    category_counts = Counter(str(data.get("surface_category", "unknown")) for _, data in decl_graph.nodes(data=True))
    module_category_counts = Counter(str(data.get("dominant_surface", "unknown")) for _, data in module_graph.nodes(data=True))
    frontier_category_counts = Counter(
        str(data.get("surface_category", "unknown")) for _, data in frontier_decl_graph.nodes(data=True)
    )
    frontier_module_category_counts = Counter(
        str(data.get("dominant_surface", "unknown")) for _, data in frontier_module_graph.nodes(data=True)
    )
    payload = {
        "declaration_graph": {
            "nodes": decl_graph.number_of_nodes(),
            "edges": decl_graph.number_of_edges(),
            "weak_components": nx.number_weakly_connected_components(decl_graph),
        },
        "module_graph": {
            "nodes": module_graph.number_of_nodes(),
            "edges": module_graph.number_of_edges(),
            "weak_components": nx.number_weakly_connected_components(module_graph),
        },
        "plotted_module_slice": {
            "nodes": plotted_graph.number_of_nodes(),
            "edges": plotted_graph.number_of_edges(),
        },
        "frontier_declaration_graph": {
            "nodes": frontier_decl_graph.number_of_nodes(),
            "edges": frontier_decl_graph.number_of_edges(),
            "weak_components": nx.number_weakly_connected_components(frontier_decl_graph)
            if frontier_decl_graph.number_of_nodes()
            else 0,
        },
        "frontier_module_graph": {
            "nodes": frontier_module_graph.number_of_nodes(),
            "edges": frontier_module_graph.number_of_edges(),
            "weak_components": nx.number_weakly_connected_components(frontier_module_graph)
            if frontier_module_graph.number_of_nodes()
            else 0,
        },
        "plotted_frontier_module_slice": {
            "nodes": frontier_plotted_graph.number_of_nodes(),
            "edges": frontier_plotted_graph.number_of_edges(),
        },
        "frontier_hotspot_module_slice": {
            "nodes": frontier_hotspot_graph.number_of_nodes(),
            "edges": frontier_hotspot_graph.number_of_edges(),
        },
        "surface_category_counts": dict(sorted(category_counts.items())),
        "module_dominant_surface_counts": dict(sorted(module_category_counts.items())),
        "frontier_surface_category_counts": dict(sorted(frontier_category_counts.items())),
        "frontier_module_dominant_surface_counts": dict(sorted(frontier_module_category_counts.items())),
        "frontier_hotspots": frontier_hotspot_rows,
        "frontier_burndown_order": frontier_burndown_rows,
        "frontier_burndown_formula": {
            "replaceable_surface_mass": {
                "surrogate_or_vacuous": BURN_DOWN_WEIGHTS["surrogate_or_vacuous"],
                "package_reprojection": BURN_DOWN_WEIGHTS["package_reprojection"],
                "hypothesis_bridge": BURN_DOWN_WEIGHTS["hypothesis_bridge"],
            },
            "support_pressure": "2 * in_weight + out_weight",
            "burn_down_score": "replaceable_surface_mass * log1p(support_pressure)",
            "scope": "strength-ranked top frontier hotspot modules only",
        },
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def main() -> int:
    args = parse_args()
    root = repo_root()
    graph_path = normalize_user_path(args.graph, root)
    decls_path = normalize_user_path(args.decls, root)
    surface_index_path = normalize_user_path(args.surface_index, root)
    decl_graphml_out = normalize_user_path(args.decl_graphml_out, root)
    module_graphml_out = normalize_user_path(args.module_graphml_out, root)
    module_svg_out = normalize_user_path(args.module_svg_out, root)
    frontier_decl_graphml_out = normalize_user_path(args.frontier_decl_graphml_out, root)
    frontier_module_graphml_out = normalize_user_path(args.frontier_module_graphml_out, root)
    frontier_module_svg_out = normalize_user_path(args.frontier_module_svg_out, root)
    frontier_hotspot_graphml_out = normalize_user_path(args.frontier_hotspot_graphml_out, root)
    frontier_hotspot_svg_out = normalize_user_path(args.frontier_hotspot_svg_out, root)
    frontier_hotspot_json_out = normalize_user_path(args.frontier_hotspot_json_out, root)
    frontier_burndown_md_out = normalize_user_path(args.frontier_burndown_md_out, root)
    frontier_burndown_json_out = normalize_user_path(args.frontier_burndown_json_out, root)
    summary_out = normalize_user_path(args.summary_out, root)

    decl_meta = load_decl_meta(decls_path, root)
    surface_categories = load_surface_categories(surface_index_path, decl_meta)
    decl_graph = build_declaration_graph(graph_path, decl_meta, surface_categories)
    module_graph = build_module_graph(decl_graph)
    plotted_graph = select_plot_subgraph(module_graph, args.plot_top_modules)
    frontier_decl_graph = filter_declaration_graph_by_surface(decl_graph, FRONTIER_CATEGORIES)
    frontier_module_graph = build_module_graph(frontier_decl_graph)
    frontier_plotted_graph = select_plot_subgraph(frontier_module_graph, args.plot_top_frontier_modules)
    frontier_hotspot_rows = module_strength_rows(frontier_module_graph)[: max(args.frontier_hotspot_count, 1)]
    frontier_burndown_rows = burn_down_rows(frontier_hotspot_rows)
    frontier_hotspot_modules = [row["module"] for row in frontier_hotspot_rows]
    frontier_hotspot_graph = frontier_module_graph.subgraph(frontier_hotspot_modules).copy()
    annotate_hotspot_graph(frontier_hotspot_graph, frontier_burndown_rows)

    decl_graphml_out.parent.mkdir(parents=True, exist_ok=True)
    module_graphml_out.parent.mkdir(parents=True, exist_ok=True)
    frontier_decl_graphml_out.parent.mkdir(parents=True, exist_ok=True)
    frontier_module_graphml_out.parent.mkdir(parents=True, exist_ok=True)
    frontier_hotspot_graphml_out.parent.mkdir(parents=True, exist_ok=True)
    nx.write_graphml(decl_graph, decl_graphml_out)
    nx.write_graphml(module_graph, module_graphml_out)
    nx.write_graphml(frontier_decl_graph, frontier_decl_graphml_out)
    nx.write_graphml(frontier_module_graph, frontier_module_graphml_out)
    nx.write_graphml(frontier_hotspot_graph, frontier_hotspot_graphml_out)
    plot_module_graph(
        plotted_graph,
        module_svg_out,
        title="InfoGeometry module dependency graph (top readable slice)",
    )
    plot_module_graph(
        frontier_plotted_graph,
        frontier_module_svg_out,
        title="InfoGeometry theorem-surface frontier graph (hypothesis/package/surrogate)",
    )
    plot_module_graph(
        frontier_hotspot_graph,
        frontier_hotspot_svg_out,
        title=f"InfoGeometry theorem-surface frontier hotspots (top {len(frontier_hotspot_rows)}; burn-down order)",
        label_attr="hotspot_rank_label",
        size_attr="burn_down_score",
    )
    write_hotspot_json(frontier_hotspot_json_out, frontier_hotspot_rows, frontier_burndown_rows)
    write_burndown_reports(frontier_burndown_md_out, frontier_burndown_json_out, frontier_burndown_rows)
    write_summary(
        summary_out,
        decl_graph,
        module_graph,
        plotted_graph,
        frontier_decl_graph,
        frontier_module_graph,
        frontier_plotted_graph,
        frontier_hotspot_graph,
        frontier_hotspot_rows,
        frontier_burndown_rows,
    )

    print(f"[plot-decl-graph] wrote {decl_graphml_out}")
    print(f"[plot-decl-graph] wrote {module_graphml_out}")
    print(f"[plot-decl-graph] wrote {module_svg_out}")
    print(f"[plot-decl-graph] wrote {frontier_decl_graphml_out}")
    print(f"[plot-decl-graph] wrote {frontier_module_graphml_out}")
    print(f"[plot-decl-graph] wrote {frontier_module_svg_out}")
    print(f"[plot-decl-graph] wrote {frontier_hotspot_graphml_out}")
    print(f"[plot-decl-graph] wrote {frontier_hotspot_svg_out}")
    print(f"[plot-decl-graph] wrote {frontier_hotspot_json_out}")
    print(f"[plot-decl-graph] wrote {frontier_burndown_md_out}")
    print(f"[plot-decl-graph] wrote {frontier_burndown_json_out}")
    print(f"[plot-decl-graph] wrote {summary_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
