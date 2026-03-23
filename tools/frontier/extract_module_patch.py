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
    from tools.pathing import default_decl_graph_file, default_decl_metadata_file, normalize_user_path, repo_root
else:
    from tools.pathing import default_decl_graph_file, default_decl_metadata_file, normalize_user_path, repo_root


DEFAULT_MODULE_GRAPH = "reports/dag/module-networkx.graphml"
DEFAULT_FRONTIER_MODULE_GRAPH = "reports/dag/module-networkx-frontier.graphml"
DEFAULT_SURFACE_INDEX = "reports/dag/theorem-surface-index.json"
DEFAULT_BURNDOWN = "reports/dag/frontier-burndown.json"
DEFAULT_SEED_MODULE = "InfoGeometry.Canonical.ConformalUnification"
CATEGORY_COLORS = {
    "likely_constructive": "#2E8B57",
    "hypothesis_bridge": "#E69F00",
    "package_reprojection": "#CC79A7",
    "surrogate_or_vacuous": "#D55E00",
    "neutral_definition": "#7A7A7A",
    "unknown": "#4C78A8",
}
SEED_DECL_LIMIT = 14
NEIGHBOR_DECL_LIMIT = 8
INTERFACE_EDGE_LIMIT = 8
NOISE_EXACT = {
    "eq_1",
    "inj",
    "sizeOf_spec",
    "noConfusionType",
    "noConfusion",
    "casesOn",
    "recOn",
    "brecOn",
    "rec",
    "ctorIdx",
}
NOISE_PREFIXES = ("_proof", "match_", "_match")


def is_noise_decl(short_name: str, line: int) -> bool:
    if short_name in NOISE_EXACT:
        return True
    if short_name.startswith(NOISE_PREFIXES):
        return True
    if line <= 0 and (short_name.startswith("eq_") or short_name.startswith("inj") or short_name.startswith("sizeOf")):
        return True
    return False


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Extract a prompt-ready local module patch around a seed hotspot from the authoritative declaration DAG."
    )
    ap.add_argument("--seed-module", default=DEFAULT_SEED_MODULE)
    ap.add_argument("--module-graph", default=DEFAULT_MODULE_GRAPH)
    ap.add_argument("--frontier-module-graph", default=DEFAULT_FRONTIER_MODULE_GRAPH)
    ap.add_argument("--graph", default=str(default_decl_graph_file().relative_to(repo_root())))
    ap.add_argument("--decls", default=str(default_decl_metadata_file().relative_to(repo_root())))
    ap.add_argument("--surface-index", default=DEFAULT_SURFACE_INDEX)
    ap.add_argument("--burndown", default=DEFAULT_BURNDOWN)
    ap.add_argument("--consumer-count", type=int, default=8)
    ap.add_argument("--support-count", type=int, default=8)
    ap.add_argument("--extra-frontier-count", type=int, default=4)
    ap.add_argument("--seed-decl-limit", type=int, default=SEED_DECL_LIMIT)
    ap.add_argument("--neighbor-decl-limit", type=int, default=NEIGHBOR_DECL_LIMIT)
    ap.add_argument("--interface-edge-limit", type=int, default=INTERFACE_EDGE_LIMIT)
    ap.add_argument("--json-out")
    ap.add_argument("--md-out")
    ap.add_argument("--graphml-out")
    ap.add_argument("--svg-out")
    return ap.parse_args()


def default_out_paths(root: Path, seed_module: str) -> dict[str, Path]:
    short = seed_module.split(".")[-1]
    base = root / "reports" / "dag" / f"{short}-topological-patch"
    return {
        "json": base.with_suffix(".json"),
        "md": base.with_suffix(".md"),
        "graphml": base.with_suffix(".graphml"),
        "svg": base.with_suffix(".svg"),
    }


def as_int(value: Any) -> int:
    try:
        return int(value)
    except Exception:
        return 0


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
        file_name = str(obj.get("file", "") or "").strip()
        if file_name.startswith("/"):
            try:
                file_name = str(Path(file_name).resolve().relative_to(root))
            except ValueError:
                pass
        elif file_name and not file_name.startswith("lean/"):
            candidate = root / "lean" / file_name
            if candidate.exists():
                file_name = str(Path("lean") / file_name)
        out[name] = {
            "module": str(obj.get("module", "")).strip() or name.rsplit(".", 1)[0],
            "file": file_name,
            "kind": str(obj.get("kind", "unknown")).strip() or "unknown",
            "line": as_int(obj.get("line")),
        }
    return out


def load_surface_rows(path: Path) -> list[dict[str, Any]]:
    payload = json.loads(path.read_text(encoding="utf-8")) if path.exists() else {"rows": []}
    rows = payload.get("rows", [])
    return [row for row in rows if isinstance(row, dict)]


def load_burndown(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {"rows": []}
    return json.loads(path.read_text(encoding="utf-8"))


def module_rows(surface_rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in surface_rows:
        module = str(row.get("module", "")).strip()
        if module:
            out[module].append(row)
    for module, rows in out.items():
        rows.sort(key=lambda row: (as_int(row.get("line")), str(row.get("name", ""))))
    return out


def row_priority(row: dict[str, Any], *, support_mode: bool) -> tuple[int, int, int, str]:
    kind = str(row.get("kind", ""))
    category = str(row.get("category", "unknown"))
    theorem_bias = 0 if kind == "theorem" else 1
    if support_mode:
        category_order = {
            "likely_constructive": 0,
            "neutral_definition": 1,
            "package_reprojection": 2,
            "hypothesis_bridge": 3,
            "surrogate_or_vacuous": 4,
            "unknown": 5,
        }
    else:
        category_order = {
            "surrogate_or_vacuous": 0,
            "package_reprojection": 1,
            "hypothesis_bridge": 2,
            "likely_constructive": 3,
            "neutral_definition": 4,
            "unknown": 5,
        }
    return (category_order.get(category, 9), theorem_bias, as_int(row.get("line")), str(row.get("name", "")))


def representative_rows(rows: list[dict[str, Any]], *, support_mode: bool, limit: int) -> list[dict[str, Any]]:
    filtered = [
        row
        for row in rows
        if not is_noise_decl(str(row.get("short_name", "")), as_int(row.get("line")))
    ]
    pool = filtered or rows
    return sorted(pool, key=lambda row: row_priority(row, support_mode=support_mode))[:limit]


def module_summary(graph: nx.DiGraph, module: str, surface_by_module: dict[str, list[dict[str, Any]]]) -> dict[str, Any]:
    data = dict(graph.nodes[module])
    rows = surface_by_module.get(module, [])
    counts = Counter(str(row.get("category", "unknown")) for row in rows)
    return {
        "module": module,
        "decl_count": as_int(data.get("decl_count")),
        "dominant_surface": str(data.get("dominant_surface", "unknown")),
        "frontier_decl_count": sum(counts[c] for c in ("hypothesis_bridge", "package_reprojection", "surrogate_or_vacuous")),
        "likely_constructive": counts.get("likely_constructive", 0),
        "hypothesis_bridge": counts.get("hypothesis_bridge", 0),
        "package_reprojection": counts.get("package_reprojection", 0),
        "surrogate_or_vacuous": counts.get("surrogate_or_vacuous", 0),
        "neutral_definition": counts.get("neutral_definition", 0),
    }


def neighbor_rows(graph: nx.DiGraph, seed: str, direction: str, limit: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    iterator = graph.predecessors(seed) if direction == "consumer" else graph.successors(seed)
    for neighbor in iterator:
        if neighbor == seed:
            continue
        edge = graph[neighbor][seed] if direction == "consumer" else graph[seed][neighbor]
        rows.append(
            {
                "module": neighbor,
                "edge_weight": as_int(edge.get("weight")),
                "direction": direction,
                "dominant_surface": str(graph.nodes[neighbor].get("dominant_surface", "unknown")),
                "decl_count": as_int(graph.nodes[neighbor].get("decl_count")),
            }
        )
    rows.sort(key=lambda row: (-row["edge_weight"], -row["decl_count"], row["module"]))
    return rows[:limit]


def extra_frontier_neighbors(full_graph: nx.DiGraph, frontier_graph: nx.DiGraph, seed: str, limit: int, existing: set[str]) -> list[dict[str, Any]]:
    if seed not in frontier_graph:
        return []
    rows: list[dict[str, Any]] = []
    for neighbor in set(frontier_graph.predecessors(seed)).union(frontier_graph.successors(seed)):
        if neighbor == seed or neighbor in existing:
            continue
        if neighbor in full_graph.predecessors(seed):
            direction = "consumer"
            edge_weight = as_int(full_graph[neighbor][seed].get("weight"))
        elif neighbor in full_graph.successors(seed):
            direction = "support"
            edge_weight = as_int(full_graph[seed][neighbor].get("weight"))
        else:
            direction = "frontier_only"
            edge_weight = 0
        rows.append(
            {
                "module": neighbor,
                "edge_weight": edge_weight,
                "direction": direction,
                "dominant_surface": str(full_graph.nodes[neighbor].get("dominant_surface", "unknown")),
                "decl_count": as_int(full_graph.nodes[neighbor].get("decl_count")),
            }
        )
    rows.sort(key=lambda row: (-row["edge_weight"], -row["decl_count"], row["module"]))
    return rows[:limit]


def seed_context_from_burndown(seed: str, burndown_payload: dict[str, Any]) -> dict[str, Any] | None:
    for row in burndown_payload.get("rows", []):
        if str(row.get("module", "")) == seed:
            return row
    return None


def interface_edges(
    graph_payload: dict[str, Any],
    decl_meta: dict[str, dict[str, Any]],
    seed_module: str,
    neighbor_module: str,
    limit: int,
) -> list[dict[str, Any]]:
    nodes = graph_payload["nodes"]
    forward = graph_payload["forward"]
    by_pair: dict[tuple[str, str, str, str], dict[str, Any]] = {}
    for src_idx, outgoing in enumerate(forward):
        src = nodes[src_idx]
        src_meta = decl_meta.get(src, {})
        src_module = str(src_meta.get("module", ""))
        if src_module not in {seed_module, neighbor_module}:
            continue
        for target_idx, edge_kind in outgoing:
            dst = nodes[int(target_idx)]
            dst_meta = decl_meta.get(dst, {})
            dst_module = str(dst_meta.get("module", ""))
            if {src_module, dst_module} != {seed_module, neighbor_module}:
                continue
            src_short = src.split(".")[-1]
            dst_short = dst.split(".")[-1]
            if is_noise_decl(src_short, as_int(src_meta.get("line"))) or is_noise_decl(dst_short, as_int(dst_meta.get("line"))):
                continue
            key = (src, dst, src_module, dst_module)
            row = by_pair.setdefault(
                key,
                {
                    "src": src,
                    "src_short": src_short,
                    "src_module": src_module,
                    "dst": dst,
                    "dst_short": dst_short,
                    "dst_module": dst_module,
                    "kinds": set(),
                    "src_line": as_int(src_meta.get("line")),
                    "dst_line": as_int(dst_meta.get("line")),
                },
            )
            row["kinds"].add(str(edge_kind))
    results = []
    for row in by_pair.values():
        row = dict(row)
        row["kind"] = ",".join(sorted(row.pop("kinds")))
        results.append(row)
    results.sort(
        key=lambda row: (
            0 if row["src_module"] == seed_module else 1,
            row["src_line"],
            row["dst_line"],
            row["src"],
            row["dst"],
        )
    )
    return results[:limit]


def build_patch_graph(full_graph: nx.DiGraph, modules: list[str], seed_module: str, burndown_row: dict[str, Any] | None) -> nx.DiGraph:
    patch = full_graph.subgraph(modules).copy()
    for node in patch.nodes():
        patch.nodes[node]["short_label"] = node.split(".")[-1]
        patch.nodes[node]["patch_role"] = "seed" if node == seed_module else "neighbor"
    if burndown_row and seed_module in patch:
        patch.nodes[seed_module]["burn_down_rank"] = as_int(burndown_row.get("burn_down_rank"))
        patch.nodes[seed_module]["burn_down_score"] = float(burndown_row.get("burn_down_score", 0.0))
    return patch


def plot_patch_graph(graph: nx.DiGraph, out_path: Path, seed_module: str) -> None:
    if graph.number_of_nodes() == 0:
        raise SystemExit("patch graph is empty")
    pos = nx.spring_layout(graph.to_undirected(), seed=11, k=1.8 / math.sqrt(max(graph.number_of_nodes(), 1)), iterations=200)
    fig, ax = plt.subplots(figsize=(16, 12))
    ax.set_axis_off()

    edge_widths = [0.8 + math.log1p(as_int(data.get("weight", 1))) for _, _, data in graph.edges(data=True)]
    nx.draw_networkx_edges(
        graph,
        pos,
        ax=ax,
        arrows=True,
        arrowstyle="-|>",
        arrowsize=12,
        width=edge_widths,
        alpha=0.22,
        edge_color="#555555",
        connectionstyle="arc3,rad=0.08",
    )

    node_sizes = []
    node_colors = []
    for node, data in graph.nodes(data=True):
        decl_count = as_int(data.get("decl_count"))
        base = 250 + 20 * math.sqrt(max(decl_count, 1))
        if node == seed_module:
            base *= 1.8
        node_sizes.append(base)
        node_colors.append(CATEGORY_COLORS.get(str(data.get("dominant_surface", "unknown")), CATEGORY_COLORS["unknown"]))

    nx.draw_networkx_nodes(
        graph,
        pos,
        ax=ax,
        node_size=node_sizes,
        node_color=node_colors,
        edgecolors="#111111",
        linewidths=0.8,
        alpha=0.96,
    )

    labels = {node: graph.nodes[node].get("short_label", node.split(".")[-1]) for node in graph.nodes()}
    nx.draw_networkx_labels(graph, pos, ax=ax, labels=labels, font_size=8)
    ax.set_title(f"{seed_module.split('.')[-1]} local module patch")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(out_path, format="svg", bbox_inches="tight")
    plt.close(fig)


def render_markdown(payload: dict[str, Any]) -> str:
    seed = payload["seed_module"]
    lines: list[str] = []
    lines.append(f"# {seed.split('.')[-1]} Topological Patch")
    lines.append("")
    lines.append("Purpose:")
    lines.append("- extract a clean local module manifold around the seed hotspot")
    lines.append("- separate constructive support modules from reverse consumer modules")
    lines.append("- provide exact cross-module declaration interfaces for LLM bridge generation")
    lines.append("")
    if payload.get("seed_burndown"):
        row = payload["seed_burndown"]
        lines.append("## Seed Pressure")
        lines.append(f"- seed module: `{seed}`")
        lines.append(f"- burn-down rank: **{row['burn_down_rank']}**")
        lines.append(f"- burn-down score: **{row['burn_down_score']}**")
        lines.append(f"- dominant pressure: `{row['dominant_pressure']}`")
        lines.append(f"- action: {row['primary_action']}")
        lines.append(f"- mix (H/P/S): `{row['hypothesis_bridge']}/{row['package_reprojection']}/{row['surrogate_or_vacuous']}`")
        lines.append("")
    lines.append("## Support Cone")
    for item in payload["support_modules"]:
        lines.append(f"- `{item['module']}` weight=`{item['edge_weight']}` dominant=`{item['dominant_surface']}`")
    lines.append("")
    lines.append("## Reverse Consumer Cone")
    for item in payload["consumer_modules"]:
        lines.append(f"- `{item['module']}` weight=`{item['edge_weight']}` dominant=`{item['dominant_surface']}`")
    if payload.get("extra_frontier_modules"):
        lines.append("")
        lines.append("## Extra Frontier Neighbors")
        for item in payload["extra_frontier_modules"]:
            lines.append(f"- `{item['module']}` weight=`{item['edge_weight']}` dominant=`{item['dominant_surface']}` direction=`{item['direction']}`")
    lines.append("")
    lines.append("## Exact Interfaces")
    for module, edges in payload["interfaces"].items():
        lines.append(f"### `{module}`")
        if not edges:
            lines.append("- no direct declaration edges captured")
        else:
            for edge in edges:
                lines.append(
                    f"- `{edge['src_short']}` -> `{edge['dst_short']}` `[{edge['kind']}]`"
                )
        lines.append("")
    lines.append("## Representative Seed Declarations")
    for row in payload["seed_declarations"]:
        lines.append(f"- `{row['short_name']}` `{row['category']}` `{row['kind']}` at `{row['file']}:{row['line']}`")
    lines.append("")
    lines.append("## Neighbor Declarations")
    for module, rows in payload["neighbor_declarations"].items():
        lines.append(f"### `{module}`")
        for row in rows:
            lines.append(f"- `{row['short_name']}` `{row['category']}` `{row['kind']}` at `{row['file']}:{row['line']}`")
        lines.append("")
    lines.append("## Prompt Packet")
    lines.append("")
    lines.append("```text")
    lines.append("You are helping close a local Lean 4 theorem frontier.")
    lines.append("")
    lines.append("Hard constraints:")
    lines.append("- Do not invent nonexistent theorems, defs, or imports.")
    lines.append("- Do not claim a proof exists unless it is directly implied by the context below.")
    lines.append("- Stay close to the current codebase vocabulary and theorem names.")
    lines.append("- Output candidate bridge statements and proof attack plans only.")
    lines.append("- Prefer Lean-style theorem signatures over prose.")
    lines.append("- Treat the support cone as constructive substrate and the consumer cone as obligations to discharge.")
    lines.append("")
    lines.append(f"Goal:")
    lines.append(f"Propose 3-5 small bridge statements that replace surrogate surfaces inside `{seed}` by using the exact support cone and reverse consumer cone below.")
    lines.append("")
    lines.append("Seed pressure:")
    if payload.get("seed_burndown"):
        row = payload["seed_burndown"]
        lines.append(f"- burn-down rank {row['burn_down_rank']}, score {row['burn_down_score']}, dominant pressure {row['dominant_pressure']}")
        lines.append(f"- mix (hypothesis/package/surrogate): {row['hypothesis_bridge']}/{row['package_reprojection']}/{row['surrogate_or_vacuous']}")
    lines.append("")
    lines.append("Support cone modules:")
    for item in payload["support_modules"]:
        lines.append(f"- {item['module']} (edge weight {item['edge_weight']}, dominant {item['dominant_surface']})")
    lines.append("")
    lines.append("Reverse consumer modules:")
    for item in payload["consumer_modules"]:
        lines.append(f"- {item['module']} (edge weight {item['edge_weight']}, dominant {item['dominant_surface']})")
    lines.append("")
    lines.append("Exact seed interfaces:")
    for module, edges in payload["interfaces"].items():
        lines.append(f"- {module}:")
        for edge in edges:
            lines.append(f"  - {edge['src_short']} -> {edge['dst_short']} [{edge['kind']}]")
    lines.append("")
    lines.append("Representative seed declarations:")
    for row in payload["seed_declarations"]:
        lines.append(f"- {row['name']} ({row['category']}, {row['kind']})")
    lines.append("")
    lines.append("Task:")
    lines.append("For each candidate, provide exactly:")
    lines.append("1. name")
    lines.append("2. Lean-style signature sketch")
    lines.append("3. which exact interface edge or module relation it closes")
    lines.append("4. likely proof ingredients already present in the support cone")
    lines.append("5. risk level (low / medium / high)")
    lines.append("")
    lines.append("Strong preference:")
    lines.append("- use constructive support modules before introducing any new abstractions")
    lines.append("- target declarations that would reduce surrogate load in the seed module")
    lines.append("- expose obligations needed by reverse consumers instead of inventing capstones")
    lines.append("")
    lines.append("Do not output proof scripts.")
    lines.append("Do not output more than 5 candidates.")
    lines.append("```")
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    root = repo_root()
    module_graph_path = normalize_user_path(args.module_graph, root / args.module_graph)
    frontier_module_graph_path = normalize_user_path(args.frontier_module_graph, root / args.frontier_module_graph)
    graph_path = normalize_user_path(args.graph, root / args.graph)
    decls_path = normalize_user_path(args.decls, root / args.decls)
    surface_index_path = normalize_user_path(args.surface_index, root / args.surface_index)
    burndown_path = normalize_user_path(args.burndown, root / args.burndown)
    outs = default_out_paths(root, args.seed_module)
    json_out = normalize_user_path(args.json_out, outs["json"])
    md_out = normalize_user_path(args.md_out, outs["md"])
    graphml_out = normalize_user_path(args.graphml_out, outs["graphml"])
    svg_out = normalize_user_path(args.svg_out, outs["svg"])

    full_module_graph = nx.read_graphml(module_graph_path)
    frontier_module_graph = nx.read_graphml(frontier_module_graph_path)
    if args.seed_module not in full_module_graph:
        raise SystemExit(f"seed module not found in module graph: {args.seed_module}")

    decl_meta = load_decl_meta(decls_path, root)
    graph_payload = json.loads(graph_path.read_text(encoding="utf-8"))
    surface_rows = load_surface_rows(surface_index_path)
    surface_by_module = module_rows(surface_rows)
    burndown_payload = load_burndown(burndown_path)
    seed_burndown = seed_context_from_burndown(args.seed_module, burndown_payload)

    consumers = neighbor_rows(full_module_graph, args.seed_module, "consumer", args.consumer_count)
    supports = neighbor_rows(full_module_graph, args.seed_module, "support", args.support_count)
    existing = {item["module"] for item in consumers + supports}
    extra = extra_frontier_neighbors(full_module_graph, frontier_module_graph, args.seed_module, args.extra_frontier_count, existing)

    patch_modules = [args.seed_module]
    for row in consumers + supports + extra:
        if row["module"] not in patch_modules:
            patch_modules.append(row["module"])

    patch_graph = build_patch_graph(full_module_graph, patch_modules, args.seed_module, seed_burndown)

    interfaces: dict[str, list[dict[str, Any]]] = {}
    neighbor_decl_sections: dict[str, list[dict[str, Any]]] = {}
    for row in consumers + supports + extra:
        module = row["module"]
        interfaces[module] = interface_edges(graph_payload, decl_meta, args.seed_module, module, args.interface_edge_limit)
        neighbor_decl_sections[module] = representative_rows(
            surface_by_module.get(module, []),
            support_mode=(row["direction"] == "support"),
            limit=args.neighbor_decl_limit,
        )

    seed_decl_rows = representative_rows(surface_by_module.get(args.seed_module, []), support_mode=False, limit=args.seed_decl_limit)

    payload = {
        "seed_module": args.seed_module,
        "seed_burndown": seed_burndown,
        "seed_summary": module_summary(full_module_graph, args.seed_module, surface_by_module),
        "consumer_modules": consumers,
        "support_modules": supports,
        "extra_frontier_modules": extra,
        "patch_modules": patch_modules,
        "patch_edges": [
            {
                "src": src,
                "dst": dst,
                "weight": as_int(data.get("weight")),
                "kinds": str(data.get("kinds", "")),
            }
            for src, dst, data in sorted(patch_graph.edges(data=True), key=lambda item: (-as_int(item[2].get("weight")), item[0], item[1]))
        ],
        "seed_declarations": seed_decl_rows,
        "neighbor_declarations": neighbor_decl_sections,
        "interfaces": interfaces,
    }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    graphml_out.parent.mkdir(parents=True, exist_ok=True)
    svg_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    md_out.write_text(render_markdown(payload), encoding="utf-8")
    nx.write_graphml(patch_graph, graphml_out)
    plot_patch_graph(patch_graph, svg_out, args.seed_module)

    print(f"[extract-module-patch] wrote {json_out}")
    print(f"[extract-module-patch] wrote {md_out}")
    print(f"[extract-module-patch] wrote {graphml_out}")
    print(f"[extract-module-patch] wrote {svg_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
