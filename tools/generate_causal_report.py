#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

import networkx as nx

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from tools.graph import ProjectGraph
    from tools.pathing import repo_root
else:
    from tools.graph import ProjectGraph
    from tools.pathing import repo_root


DEFAULT_GRAPH = "full_graph.json"
DEFAULT_DECLS = "index/decls.jsonl"
DEFAULT_THINNESS_INDEX = "BRIDGE_THINNESS_INDEX.md"
DEFAULT_VACUITY_INDEX = "VACUITY_INDEX.md"
DEFAULT_SURROGATE_INDEX = "SURROGATE_INDEX.md"
DEFAULT_OUT = "reports/dag/true-root-order.md"

QUEUE_HEADERS = {"## Queue", "## Aggressive Replacement Queue"}
QUEUE_RE = re.compile(
    r"^- `(?P<priority>[^`]+)` `(?P<category>[^`]+)` (?P<name>.+?) "
    r"at `(?P<file>[^`:]+)(?::(?P<line>\d+))?`$"
)

PRIORITY_WEIGHTS = {
    "critical": 4.0,
    "high": 3.0,
    "medium": 2.0,
    "low": 1.0,
}
INDEX_WEIGHTS = {
    "thinness": 1.0,
    "vacuity": 2.5,
    "surrogate": 3.0,
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate an absolute causal order report from a trusted full dependency graph, "
            "declaration metadata export, and current debt indices."
        )
    )
    parser.add_argument("--graph", default=DEFAULT_GRAPH, help="Trusted full_graph.json path.")
    parser.add_argument("--decls", default=DEFAULT_DECLS, help="Trusted decls.jsonl path.")
    parser.add_argument("--thinness-index", default=DEFAULT_THINNESS_INDEX)
    parser.add_argument("--vacuity-index", default=DEFAULT_VACUITY_INDEX)
    parser.add_argument("--surrogate-index", default=DEFAULT_SURROGATE_INDEX)
    parser.add_argument("--out", default=DEFAULT_OUT, help="Markdown report path to write.")
    parser.add_argument("--top-per-layer", type=int, default=12)
    parser.add_argument("--top-capstones", type=int, default=12)
    parser.add_argument("--top-roots", type=int, default=12)
    parser.add_argument("--top-modules", type=int, default=20)
    return parser.parse_args()


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
    return str(candidate)


def load_decl_metadata(path: Path, root: Path) -> dict[str, dict[str, Any]]:
    decl_meta: dict[str, dict[str, Any]] = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line:
            continue
        obj = json.loads(line)
        name = str(obj.get("name", "")).strip()
        if not name:
            continue
        decl_meta[name] = {
            "kind": str(obj.get("kind", "")),
            "module": str(obj.get("module", "")),
            "file": normalize_repo_relative(root, obj.get("file", "")),
            "line": obj.get("line"),
            "column": obj.get("column"),
        }
    return decl_meta


def load_queue(path: Path, index_name: str, root: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    findings: list[dict[str, Any]] = []
    active_queue = False
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        stripped = raw_line.strip()
        if stripped.startswith("## "):
            active_queue = stripped in QUEUE_HEADERS
            continue
        if not active_queue:
            continue
        match = QUEUE_RE.match(stripped)
        if not match:
            continue
        findings.append(
            {
                "index": index_name,
                "priority": match.group("priority"),
                "category": match.group("category"),
                "name": match.group("name"),
                "file": normalize_repo_relative(root, match.group("file")),
                "line": int(match.group("line")) if match.group("line") else None,
            }
        )
    return findings


def load_debt_scores(
    root: Path,
    thinness_path: Path,
    vacuity_path: Path,
    surrogate_path: Path,
) -> tuple[dict[str, float], dict[str, list[dict[str, Any]]], dict[str, int]]:
    findings_by_index = {
        "thinness": load_queue(thinness_path, "thinness", root),
        "vacuity": load_queue(vacuity_path, "vacuity", root),
        "surrogate": load_queue(surrogate_path, "surrogate", root),
    }

    file_debt: dict[str, float] = defaultdict(float)
    seen: set[tuple[str, str, str, str, str, int | None]] = set()
    for index_name, findings in findings_by_index.items():
        for finding in findings:
            key = (
                index_name,
                finding["priority"],
                finding["category"],
                finding["name"],
                finding["file"],
                finding["line"],
            )
            if key in seen:
                continue
            seen.add(key)
            file_name = str(finding["file"])
            if not file_name:
                continue
            priority_weight = PRIORITY_WEIGHTS.get(str(finding["priority"]).lower(), 1.0)
            index_weight = INDEX_WEIGHTS[index_name]
            file_debt[file_name] += priority_weight * index_weight

    audit_counts = {
        index_name: len(findings) for index_name, findings in findings_by_index.items()
    }
    return dict(file_debt), findings_by_index, audit_counts


def build_dependency_graph(graph_path: Path) -> tuple[ProjectGraph, nx.DiGraph]:
    project_graph = ProjectGraph(graph_path=graph_path)
    clean = project_graph.filter_noise().copy()
    dep_g = nx.DiGraph()
    dep_g.add_nodes_from(clean.nodes())
    for src, dst in clean.edges():
        if src != dst:
            dep_g.add_edge(src, dst)
    return project_graph, dep_g


def component_representative(members: set[str]) -> str:
    return min(members, key=lambda name: (name.count("."), len(name), name))


def scc_condensation(
    dep_g: nx.DiGraph,
) -> tuple[list[set[str]], dict[str, int], nx.DiGraph]:
    if dep_g.number_of_nodes() == 0:
        return [], {}, nx.DiGraph()

    raw_components = [set(component) for component in nx.strongly_connected_components(dep_g)]
    components = sorted(raw_components, key=component_representative)
    comp_of = {
        name: cid for cid, members in enumerate(components) for name in members
    }

    comp_g = nx.DiGraph()
    comp_g.add_nodes_from(range(len(components)))
    for src, dst in dep_g.edges():
        src_c = comp_of[src]
        dst_c = comp_of[dst]
        if src_c != dst_c:
            comp_g.add_edge(src_c, dst_c)
    return components, comp_of, comp_g


def compute_depths(causal_g: nx.DiGraph) -> tuple[list[int], list[int], list[int | None]]:
    if causal_g.number_of_nodes() == 0:
        return [], [], []

    inf = 10**9
    min_depth: dict[int, int] = {int(node): inf for node in causal_g.nodes()}
    max_depth: dict[int, int] = {int(node): 0 for node in causal_g.nodes()}
    best_pred: dict[int, int | None] = {int(node): None for node in causal_g.nodes()}

    roots = [int(node) for node in causal_g.nodes() if causal_g.in_degree(node) == 0]
    for node in roots:
        min_depth[node] = 0
        max_depth[node] = 0

    for node_raw in nx.topological_sort(causal_g):
        node = int(node_raw)
        if causal_g.in_degree(node) == 0 and min_depth[node] == inf:
            min_depth[node] = 0
        for succ_raw in causal_g.successors(node):
            succ = int(succ_raw)
            if min_depth[node] != inf and min_depth[node] + 1 < min_depth[succ]:
                min_depth[succ] = min_depth[node] + 1
            candidate_depth = max_depth[node] + 1
            if candidate_depth > max_depth[succ]:
                max_depth[succ] = candidate_depth
                best_pred[succ] = node

    ordered_min = [min_depth[int(node)] if min_depth[int(node)] != inf else -1 for node in causal_g.nodes()]
    ordered_max = [max_depth[int(node)] for node in causal_g.nodes()]
    ordered_pred = [best_pred[int(node)] for node in causal_g.nodes()]
    return ordered_min, ordered_max, ordered_pred


def reconstruct_chain(
    comp_id: int,
    best_pred: list[int | None],
) -> list[int]:
    chain: list[int] = []
    cur: int | None = comp_id
    while cur is not None:
        chain.append(cur)
        cur = best_pred[cur]
    chain.reverse()
    return chain


def summarize_component_label(
    cid: int,
    components: list[set[str]],
) -> str:
    members = components[cid]
    rep = component_representative(members)
    if len(members) == 1:
        return rep
    return f"{rep} (+{len(members) - 1} more)"


def component_file_set(
    cid: int,
    components: list[set[str]],
    decl_meta: dict[str, dict[str, Any]],
) -> list[str]:
    files = sorted(
        {
            str(decl_meta[name]["file"])
            for name in components[cid]
            if name in decl_meta and decl_meta[name].get("file")
        }
    )
    return files


def component_module_set(
    cid: int,
    components: list[set[str]],
    decl_meta: dict[str, dict[str, Any]],
) -> list[str]:
    modules = sorted(
        {
            str(decl_meta[name]["module"])
            for name in components[cid]
            if name in decl_meta and decl_meta[name].get("module")
        }
    )
    return modules


def render_report(
    *,
    out_path: Path,
    dep_g: nx.DiGraph,
    components: list[set[str]],
    comp_g: nx.DiGraph,
    causal_g: nx.DiGraph,
    decl_meta: dict[str, dict[str, Any]],
    file_debt: dict[str, float],
    audit_counts: dict[str, int],
    min_depth: list[int],
    max_depth: list[int],
    best_pred: list[int | None],
    top_per_layer: int,
    top_capstones: int,
    top_roots: int,
    top_modules: int,
) -> None:
    del comp_g
    roots = sorted([int(node) for node in causal_g.nodes() if causal_g.in_degree(node) == 0])
    capstones = sorted([int(node) for node in causal_g.nodes() if causal_g.out_degree(node) == 0])

    component_desc_count: dict[int, int] = {}
    component_capstone_support: dict[int, int] = {}
    component_debt: dict[int, float] = {}
    component_load: dict[int, float] = {}
    component_inertia: dict[int, float] = {}
    component_notes: dict[int, str] = {}

    for cid in causal_g.nodes():
        descendants = nx.descendants(causal_g, cid)
        supported_capstones = descendants.intersection(capstones)
        if cid in capstones:
            supported_capstones = set(supported_capstones)
            supported_capstones.add(cid)

        files = component_file_set(cid, components, decl_meta)
        debt = sum(file_debt.get(path, 0.0) for path in files)
        load = float(len(descendants) + 2 * len(supported_capstones))
        inertia = load / (1.0 + debt)

        component_desc_count[cid] = len(descendants)
        component_capstone_support[cid] = len(supported_capstones)
        component_debt[cid] = debt
        component_load[cid] = load
        component_inertia[cid] = inertia

        if cid in roots:
            component_notes[cid] = "Bedrock" if debt == 0.0 else "Soft bedrock"
        elif cid in capstones:
            component_notes[cid] = "Capstone"
        else:
            component_notes[cid] = "-"

    by_layer: dict[int, list[int]] = defaultdict(list)
    for cid in causal_g.nodes():
        by_layer[max_depth[cid]].append(cid)

    max_layer = max(max_depth) if max_depth else 0

    root_impact: dict[int, int] = defaultdict(int)
    capstone_root_cones: list[tuple[int, list[int]]] = []
    for cap in capstones:
        support_roots = sorted(nx.ancestors(causal_g, cap).intersection(roots))
        if cap in roots:
            support_roots = sorted(set(support_roots + [cap]))
        for root_id in support_roots:
            root_impact[root_id] += 1
        capstone_root_cones.append((cap, support_roots))

    module_rows: dict[str, dict[str, Any]] = {}
    for cid in causal_g.nodes():
        modules = component_module_set(cid, components, decl_meta)
        files = component_file_set(cid, components, decl_meta)
        for module in modules:
            row = module_rows.setdefault(
                module,
                {
                    "module": module,
                    "files": set(),
                    "components": set(),
                    "age": 0,
                    "min_depth": 10**9,
                    "load": 0.0,
                    "debt": 0.0,
                    "has_root": False,
                    "has_capstone": False,
                },
            )
            row["files"].update(files)
            row["components"].add(cid)
            row["age"] = max(row["age"], max_depth[cid])
            row["min_depth"] = min(row["min_depth"], min_depth[cid])
            row["load"] = max(row["load"], component_load[cid])
            row["has_root"] = row["has_root"] or (cid in roots)
            row["has_capstone"] = row["has_capstone"] or (cid in capstones)

    for row in module_rows.values():
        row["debt"] = sum(file_debt.get(path, 0.0) for path in row["files"])
        row["inertia"] = row["load"] / (1.0 + row["debt"])
        if row["has_root"]:
            row["note"] = "Bedrock module" if row["debt"] == 0.0 else "Soft bedrock module"
        elif row["has_capstone"]:
            row["note"] = "Capstone module"
        else:
            row["note"] = "-"

    sorted_modules = sorted(
        module_rows.values(),
        key=lambda row: (-row["age"], -row["load"], row["module"]),
    )

    deepest_capstones = sorted(
        capstones,
        key=lambda cid: (-max_depth[cid], -component_load[cid], summarize_component_label(cid, components)),
    )[:top_capstones]

    dominant_roots = sorted(
        roots,
        key=lambda cid: (-root_impact.get(cid, 0), -component_load[cid], summarize_component_label(cid, components)),
    )[:top_roots]

    total_edges = dep_g.number_of_edges()
    total_components = len(components)

    lines: list[str] = []
    lines.append("# Absolute Causal Order Report")
    lines.append("")
    lines.append("This report gives the global causal stratigraphy of the theory.")
    lines.append("")
    lines.append("It is computed on the SCC-condensed declaration DAG, with the existing project")
    lines.append("edge orientation interpreted correctly as:")
    lines.append("")
    lines.append("- declaration -> dependency")
    lines.append("")
    lines.append("So:")
    lines.append("")
    lines.append("- **roots** are components with no outgoing internal dependencies")
    lines.append("- **capstones** are components with no incoming internal dependents")
    lines.append("- **theoretical age** is the maximal depth from the root set on the reversed causal DAG")
    lines.append("- **inertia** is reverse structural load penalized by weighted debt")
    lines.append("")
    lines.append("## Structural Summary")
    lines.append(f"- declaration nodes: `{dep_g.number_of_nodes()}`")
    lines.append(f"- declaration edges: `{total_edges}`")
    lines.append(f"- SCC components: `{total_components}`")
    lines.append(f"- total layers: `{max_layer + 1}`")
    lines.append(f"- root components: `{len(roots)}`")
    lines.append(f"- capstone components: `{len(capstones)}`")
    lines.append(f"- thinness findings: `{audit_counts.get('thinness', 0)}`")
    lines.append(f"- vacuity findings: `{audit_counts.get('vacuity', 0)}`")
    lines.append(f"- surrogate findings: `{audit_counts.get('surrogate', 0)}`")
    lines.append("")
    lines.append("## Root Set")
    if roots:
        for cid in dominant_roots:
            label = summarize_component_label(cid, components)
            files = component_file_set(cid, components, decl_meta)
            file_display = ", ".join(f"`{path}`" for path in files[:3]) if files else "-"
            if len(files) > 3:
                file_display += f", ... (+{len(files) - 3} more)"
            lines.append(
                f"- `{label}` | load `{component_load[cid]:.2f}` | inertia `{component_inertia[cid]:.2f}` | "
                f"supports `{root_impact.get(cid, 0)}` capstones | files: {file_display}"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Layer Stratigraphy (SCC-condensed declarations)")
    lines.append("")
    lines.append("| Layer | Representative SCC | Size | Min depth | Max depth | Reverse load | Debt | Inertia | Notes |")
    lines.append("| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | :--- |")
    for level in range(max_layer + 1):
        rows = sorted(
            by_layer.get(level, []),
            key=lambda cid: (-component_load[cid], -component_inertia[cid], summarize_component_label(cid, components)),
        )[:top_per_layer]
        if not rows:
            continue
        for cid in rows:
            label = summarize_component_label(cid, components)
            lines.append(
                f"| {level} | `{label}` | {len(components[cid])} | "
                f"{min_depth[cid]} | {max_depth[cid]} | "
                f"{component_load[cid]:.2f} | {component_debt[cid]:.2f} | {component_inertia[cid]:.2f} | "
                f"{component_notes[cid]} |"
            )
    lines.append("")
    lines.append("## Deepest Capstones")
    if deepest_capstones:
        for cid in deepest_capstones:
            label = summarize_component_label(cid, components)
            chain = reconstruct_chain(cid, best_pred)
            chain_labels = " -> ".join(f"`{summarize_component_label(node, components)}`" for node in chain)
            lines.append(
                f"- `{label}` | layer `{max_depth[cid]}` | reverse load `{component_load[cid]:.2f}` | "
                f"inertia `{component_inertia[cid]:.2f}`"
            )
            lines.append(f"  longest causal chain: {chain_labels}")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Dominant Roots By Capstone Support")
    if dominant_roots:
        for cid in dominant_roots:
            label = summarize_component_label(cid, components)
            lines.append(
                f"- `{label}` supports `{root_impact.get(cid, 0)}` capstones "
                f"(load `{component_load[cid]:.2f}`, inertia `{component_inertia[cid]:.2f}`)"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Capstone Root Cones")
    if capstone_root_cones:
        for cap, support_roots in sorted(
            capstone_root_cones,
            key=lambda item: (-max_depth[item[0]], summarize_component_label(item[0], components)),
        )[:top_capstones]:
            label = summarize_component_label(cap, components)
            if support_roots:
                support_labels = ", ".join(
                    f"`{summarize_component_label(root_id, components)}`" for root_id in support_roots[:10]
                )
                if len(support_roots) > 10:
                    support_labels += f", ... (+{len(support_roots) - 10} more)"
            else:
                support_labels = "-"
            lines.append(f"- `{label}` <- {support_labels}")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Module Rollup")
    lines.append("")
    lines.append("| Module | Age | Min depth | Load | Debt | Inertia | Notes |")
    lines.append("| :--- | ---: | ---: | ---: | ---: | ---: | :--- |")
    for row in sorted_modules[:top_modules]:
        min_depth_value = row["min_depth"] if row["min_depth"] != 10**9 else -1
        lines.append(
            f"| `{row['module']}` | {row['age']} | {min_depth_value} | "
            f"{row['load']:.2f} | {row['debt']:.2f} | {row['inertia']:.2f} | {row['note']} |"
        )
    lines.append("")
    lines.append("## Interpretation")
    lines.append("- `Min depth` is the shortest causal distance from the root set.")
    lines.append("- `Max depth` is the deepest causal distance from the root set; this is the **theoretical age**.")
    lines.append("- `Reverse load` measures how much later theory depends on the node/component.")
    lines.append("- `Debt` is weighted from the tracked thinness/vacuity/surrogate queues.")
    lines.append("- `Inertia = reverse load / (1 + debt)`.")
    lines.append("- Vacuity and surrogate debt are penalized more heavily than thinness.")
    lines.append("")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    root = repo_root()

    graph_path = normalize_user_path(args.graph, root)
    decls_path = normalize_user_path(args.decls, root)
    thinness_path = normalize_user_path(args.thinness_index, root)
    vacuity_path = normalize_user_path(args.vacuity_index, root)
    surrogate_path = normalize_user_path(args.surrogate_index, root)
    out_path = normalize_user_path(args.out, root)

    if not graph_path.exists():
        raise SystemExit(f"missing required graph artifact: {graph_path}")
    if not decls_path.exists():
        raise SystemExit(f"missing required declaration metadata artifact: {decls_path}")

    decl_meta = load_decl_metadata(decls_path, root)
    file_debt, _findings_by_index, audit_counts = load_debt_scores(
        root,
        thinness_path,
        vacuity_path,
        surrogate_path,
    )

    _project_graph, dep_g = build_dependency_graph(graph_path)
    components, _comp_of, dep_comp_g = scc_condensation(dep_g)

    # Reverse orientation for causal reading: dependency -> dependent.
    causal_g = dep_comp_g.reverse(copy=True)

    min_depth, max_depth, best_pred = compute_depths(causal_g)

    render_report(
        out_path=out_path,
        dep_g=dep_g,
        components=components,
        comp_g=dep_comp_g,
        causal_g=causal_g,
        decl_meta=decl_meta,
        file_debt=file_debt,
        audit_counts=audit_counts,
        min_depth=min_depth,
        max_depth=max_depth,
        best_pred=best_pred,
        top_per_layer=args.top_per_layer,
        top_capstones=args.top_capstones,
        top_roots=args.top_roots,
        top_modules=args.top_modules,
    )

    print(f"[causal-report] wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
