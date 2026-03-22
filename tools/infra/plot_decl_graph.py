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
    ap.add_argument("--summary-out", default=DEFAULT_SUMMARY_OUT)
    ap.add_argument("--plot-top-modules", type=int, default=80, help="How many modules to include in the readable full-graph plot.")
    ap.add_argument(
        "--plot-top-frontier-modules",
        type=int,
        default=60,
        help="How many modules to include in the readable theorem-surface frontier plot.",
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


def module_strengths(graph: nx.DiGraph) -> Counter[str]:
    strengths: Counter[str] = Counter()
    for node in graph.nodes():
        strengths[node] = 0
    for src, tgt, data in graph.edges(data=True):
        weight = int(data.get("weight", 1))
        strengths[src] += weight
        strengths[tgt] += weight
    return strengths


def select_plot_subgraph(graph: nx.DiGraph, top_n: int) -> nx.DiGraph:
    strengths = module_strengths(graph)
    selected = [name for name, _ in strengths.most_common(max(top_n, 1))]
    if not selected:
        return graph.copy()
    return graph.subgraph(selected).copy()


def plot_module_graph(graph: nx.DiGraph, out_path: Path, *, title: str) -> None:
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

    node_sizes = [140 + 18 * math.sqrt(int(graph.nodes[node].get("decl_count", 1))) for node in graph.nodes()]
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

    labels = {node: node.split(".")[-1] for node in graph.nodes()}
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


def write_summary(
    out_path: Path,
    decl_graph: nx.DiGraph,
    module_graph: nx.DiGraph,
    plotted_graph: nx.DiGraph,
    frontier_decl_graph: nx.DiGraph,
    frontier_module_graph: nx.DiGraph,
    frontier_plotted_graph: nx.DiGraph,
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
        "surface_category_counts": dict(sorted(category_counts.items())),
        "module_dominant_surface_counts": dict(sorted(module_category_counts.items())),
        "frontier_surface_category_counts": dict(sorted(frontier_category_counts.items())),
        "frontier_module_dominant_surface_counts": dict(sorted(frontier_module_category_counts.items())),
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
    summary_out = normalize_user_path(args.summary_out, root)

    decl_meta = load_decl_meta(decls_path, root)
    surface_categories = load_surface_categories(surface_index_path, decl_meta)
    decl_graph = build_declaration_graph(graph_path, decl_meta, surface_categories)
    module_graph = build_module_graph(decl_graph)
    plotted_graph = select_plot_subgraph(module_graph, args.plot_top_modules)
    frontier_decl_graph = filter_declaration_graph_by_surface(decl_graph, FRONTIER_CATEGORIES)
    frontier_module_graph = build_module_graph(frontier_decl_graph)
    frontier_plotted_graph = select_plot_subgraph(frontier_module_graph, args.plot_top_frontier_modules)

    decl_graphml_out.parent.mkdir(parents=True, exist_ok=True)
    module_graphml_out.parent.mkdir(parents=True, exist_ok=True)
    frontier_decl_graphml_out.parent.mkdir(parents=True, exist_ok=True)
    frontier_module_graphml_out.parent.mkdir(parents=True, exist_ok=True)
    nx.write_graphml(decl_graph, decl_graphml_out)
    nx.write_graphml(module_graph, module_graphml_out)
    nx.write_graphml(frontier_decl_graph, frontier_decl_graphml_out)
    nx.write_graphml(frontier_module_graph, frontier_module_graphml_out)
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
    write_summary(
        summary_out,
        decl_graph,
        module_graph,
        plotted_graph,
        frontier_decl_graph,
        frontier_module_graph,
        frontier_plotted_graph,
    )

    print(f"[plot-decl-graph] wrote {decl_graphml_out}")
    print(f"[plot-decl-graph] wrote {module_graphml_out}")
    print(f"[plot-decl-graph] wrote {module_svg_out}")
    print(f"[plot-decl-graph] wrote {frontier_decl_graphml_out}")
    print(f"[plot-decl-graph] wrote {frontier_module_graphml_out}")
    print(f"[plot-decl-graph] wrote {frontier_module_svg_out}")
    print(f"[plot-decl-graph] wrote {summary_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
