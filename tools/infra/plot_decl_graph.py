#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import sys
from collections import Counter
from pathlib import Path
from typing import Any

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import networkx as nx

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.decl_graph import (
        BURN_DOWN_WEIGHTS,
        FRONTIER_CATEGORIES,
        annotate_hotspot_graph,
        build_module_graph,
        burn_down_rows,
        load_decl_graph_bundle,
        module_strength_rows,
        select_plot_subgraph,
    )
    from tools.pathing import default_decl_graph_file, default_decl_metadata_file, normalize_user_path, repo_root
else:
    from tools.infra.decl_graph import (
        BURN_DOWN_WEIGHTS,
        FRONTIER_CATEGORIES,
        annotate_hotspot_graph,
        build_module_graph,
        burn_down_rows,
        load_decl_graph_bundle,
        module_strength_rows,
        select_plot_subgraph,
    )
    from tools.pathing import default_decl_graph_file, default_decl_metadata_file, normalize_user_path, repo_root


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
CATEGORY_COLORS = {
    "likely_constructive": "#2E8B57",
    "hypothesis_bridge": "#E69F00",
    "package_reprojection": "#CC79A7",
    "surrogate_or_vacuous": "#D55E00",
    "neutral_definition": "#7A7A7A",
    "unknown": "#4C78A8",
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

    graph_bundle = load_decl_graph_bundle(
        root=root,
        graph_path=graph_path,
        decls_path=decls_path,
        surface_index_path=surface_index_path,
        frontier_categories=FRONTIER_CATEGORIES,
    )
    decl_graph = graph_bundle["decl_graph"]
    module_graph = build_module_graph(decl_graph)
    plotted_graph = select_plot_subgraph(module_graph, args.plot_top_modules)
    frontier_decl_graph = graph_bundle["frontier_decl_graph"]
    frontier_module_graph = graph_bundle["frontier_module_graph"]
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
