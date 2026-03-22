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
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import default_decl_graph_file, default_decl_metadata_file, repo_root
else:
    from tools.pathing import default_decl_graph_file, default_decl_metadata_file, repo_root


DEFAULT_GRAPH = str(default_decl_graph_file().relative_to(repo_root()))
DEFAULT_DECLS = str(default_decl_metadata_file().relative_to(repo_root()))
DEFAULT_THINNESS_INDEX = "BRIDGE_THINNESS_INDEX.md"
DEFAULT_VACUITY_INDEX = "VACUITY_INDEX.md"
DEFAULT_SURROGATE_INDEX = "SURROGATE_INDEX.md"
DEFAULT_OUT = "reports/dag/true-root-order.md"
DEFAULT_JSON_OUT = "reports/dag/true-root-order.json"

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

NOISE_LABEL_PATTERNS = (
    '._',
    '.match_',
    '.proof_',
    '.brecOn',
    '.below',
    '.injEq',
    '.sizeOf_spec',
)


def is_noise_label(name: str) -> bool:
    return any(pattern in name for pattern in NOISE_LABEL_PATTERNS)


DECLARATION_SURFACE_RE = re.compile(
    r"(?m)^[ \t]*(?:@[^\n]*\n[ \t]*)*(?:(?:protected|private|noncomputable|unsafe|partial|scoped)\s+)*(?:theorem|lemma|def|abbrev|inductive|structure|class|instance|axiom|opaque|syntax|macro_rules|macro|elab|declare_syntax_cat|notation|infixl|infixr|infix|prefix|postfix|mixfix)\b"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate absolute causal-order reports from the trusted declaration graph, "
            "declaration metadata export, and current debt indices."
        )
    )
    parser.add_argument("--graph", default=DEFAULT_GRAPH, help="Trusted full_graph.json path.")
    parser.add_argument("--decls", default=DEFAULT_DECLS, help="Trusted decls.jsonl path.")
    parser.add_argument("--thinness-index", default=DEFAULT_THINNESS_INDEX)
    parser.add_argument("--vacuity-index", default=DEFAULT_VACUITY_INDEX)
    parser.add_argument("--surrogate-index", default=DEFAULT_SURROGATE_INDEX)
    parser.add_argument("--out", default=DEFAULT_OUT, help="Markdown report path to write.")
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT, help="JSON report path to write.")
    parser.add_argument("--top-per-layer", type=int, default=12)
    parser.add_argument("--top-capstones", type=int, default=12)
    parser.add_argument("--top-roots", type=int, default=12)
    parser.add_argument("--top-modules", type=int, default=20)
    parser.add_argument(
        "--allow-partial-coverage",
        action="store_true",
        help="Do not fail when the declaration graph misses live lean/InfoGeometry files.",
    )
    parser.add_argument(
        "--allow-uncovered-debt",
        action="store_true",
        help="Do not fail when audited debt files are outside declaration-graph coverage.",
    )
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
    if not candidate.parts:
        return str(candidate)
    if str(candidate).startswith("lean/"):
        return str(candidate)
    lean_candidate = root / "lean" / candidate
    if lean_candidate.exists():
        return str(Path("lean") / candidate)
    return str(candidate)


def collect_repo_lean_files(root: Path) -> list[str]:
    base = root / "lean" / "InfoGeometry"
    if not base.exists():
        return []
    return sorted(str(path.relative_to(root)) for path in base.rglob("*.lean"))


def strip_lean_comments(source: str) -> str:
    out: list[str] = []
    i = 0
    n = len(source)
    block_depth = 0
    while i < n:
        if block_depth > 0:
            if source.startswith("/-", i):
                block_depth += 1
                i += 2
                continue
            if source.startswith("-/", i):
                block_depth -= 1
                i += 2
                continue
            if source[i] == "\n":
                out.append("\n")
            i += 1
            continue

        if source.startswith("--", i):
            j = source.find("\n", i)
            if j == -1:
                break
            out.append("\n")
            i = j + 1
            continue
        if source.startswith("/-", i):
            block_depth = 1
            i += 2
            continue

        out.append(source[i])
        i += 1

    return "".join(out)


def file_has_declaration_surface(path: Path) -> bool:
    try:
        source = path.read_text(encoding="utf-8")
    except OSError:
        return False
    stripped = strip_lean_comments(source)
    return bool(DECLARATION_SURFACE_RE.search(stripped))


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


def compute_graph_coverage(
    *,
    root: Path,
    decl_meta: dict[str, dict[str, Any]],
    findings_by_index: dict[str, list[dict[str, Any]]],
    file_debt: dict[str, float],
) -> dict[str, Any]:
    covered_decl_files = sorted(
        {
            str(meta.get("file", "")).strip()
            for meta in decl_meta.values()
            if str(meta.get("file", "")).strip()
        }
    )
    covered_decl_file_set = set(covered_decl_files)
    repo_files = collect_repo_lean_files(root)

    decl_bearing_files: list[str] = []
    import_only_files: list[str] = []
    for rel_path in repo_files:
        if file_has_declaration_surface(root / rel_path):
            decl_bearing_files.append(rel_path)
        else:
            import_only_files.append(rel_path)

    missing_decl_files = sorted(path for path in decl_bearing_files if path not in covered_decl_file_set)

    uncovered_debt_by_file: dict[str, dict[str, Any]] = {}
    for index_name, findings in findings_by_index.items():
        for finding in findings:
            file_name = str(finding.get("file", "")).strip()
            if not file_name or file_name in covered_decl_file_set:
                continue
            entry = uncovered_debt_by_file.setdefault(
                file_name,
                {
                    "file": file_name,
                    "score": float(file_debt.get(file_name, 0.0)),
                    "indices": set(),
                    "categories": set(),
                    "priorities": set(),
                    "lines": set(),
                    "finding_count": 0,
                },
            )
            entry["indices"].add(index_name)
            entry["categories"].add(str(finding.get("category", "")))
            entry["priorities"].add(str(finding.get("priority", "")))
            if finding.get("line") is not None:
                entry["lines"].add(int(finding["line"]))
            entry["finding_count"] += 1

    uncovered_debt_files = sorted(
        (
            {
                "file": file_name,
                "score": data["score"],
                "indices": sorted(data["indices"]),
                "categories": sorted(category for category in data["categories"] if category),
                "priorities": sorted(priority for priority in data["priorities"] if priority),
                "lines": sorted(data["lines"]),
                "finding_count": data["finding_count"],
            }
            for file_name, data in uncovered_debt_by_file.items()
        ),
        key=lambda row: (-float(row["score"]), -int(row["finding_count"]), str(row["file"])),
    )

    return {
        "repo_lean_files": len(repo_files),
        "repo_decl_files": len(decl_bearing_files),
        "decl_index_files": len(covered_decl_files),
        "import_only_files_count": len(import_only_files),
        "import_only_files": import_only_files,
        "missing_decl_files_count": len(missing_decl_files),
        "missing_decl_files": missing_decl_files,
        "missing_repo_files_count": len(missing_decl_files),
        "missing_repo_files": missing_decl_files,
        "is_partial": len(missing_decl_files) > 0,
        "uncovered_debt_files": uncovered_debt_files,
        "uncovered_debt_file_count": len(uncovered_debt_files),
    }


def build_dependency_graph(graph_path: Path) -> nx.DiGraph:
    obj = json.loads(graph_path.read_text(encoding="utf-8"))
    raw_nodes = [str(name) for name in obj.get("nodes", [])]
    keep = {name for name in raw_nodes if not is_noise_label(name)}

    dep_g = nx.DiGraph()
    dep_g.add_nodes_from(sorted(keep))

    forward = obj.get("forward", [])
    for src_idx, adj in enumerate(forward):
        if src_idx >= len(raw_nodes):
            continue
        src = raw_nodes[src_idx]
        if src not in keep or not isinstance(adj, list):
            continue
        for item in adj:
            if not isinstance(item, list) or len(item) != 2:
                continue
            dst_idx, _kind = item
            if not isinstance(dst_idx, int) or dst_idx < 0 or dst_idx >= len(raw_nodes):
                continue
            dst = raw_nodes[dst_idx]
            if dst in keep and src != dst:
                dep_g.add_edge(src, dst)
    return dep_g


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


def reconstruct_chain(comp_id: int, best_pred: list[int | None]) -> list[int]:
    chain: list[int] = []
    cur: int | None = comp_id
    while cur is not None:
        chain.append(cur)
        cur = best_pred[cur]
    chain.reverse()
    return chain


def summarize_component_label(cid: int, components: list[set[str]]) -> str:
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
    return sorted(
        {
            str(decl_meta[name]["file"])
            for name in components[cid]
            if name in decl_meta and decl_meta[name].get("file")
        }
    )


def component_module_set(
    cid: int,
    components: list[set[str]],
    decl_meta: dict[str, dict[str, Any]],
) -> list[str]:
    return sorted(
        {
            str(decl_meta[name]["module"])
            for name in components[cid]
            if name in decl_meta and decl_meta[name].get("module")
        }
    )


def component_payload(
    *,
    cid: int,
    components: list[set[str]],
    decl_meta: dict[str, dict[str, Any]],
    min_depth: list[int],
    max_depth: list[int],
    component_debt: dict[int, float],
    component_load: dict[int, float],
    component_inertia: dict[int, float],
    component_notes: dict[int, str],
    component_capstone_support: dict[int, int],
    best_pred: list[int | None] | None = None,
    include_extras: bool = False,
    include_longest_chain: bool = False,
) -> dict[str, Any]:
    payload = {
        "id": cid,
        "label": summarize_component_label(cid, components),
        "size": len(components[cid]),
        "depth_min": min_depth[cid],
        "depth_max": max_depth[cid],
        "debt": component_debt[cid],
        "load": component_load[cid],
        "inertia": component_inertia[cid],
        "note": component_notes[cid],
        "members": sorted(components[cid]),
    }
    if include_extras:
        payload["capstones_supported"] = component_capstone_support[cid]
        payload["files"] = component_file_set(cid, components, decl_meta)
        payload["modules"] = component_module_set(cid, components, decl_meta)
    if include_longest_chain and best_pred is not None:
        payload["longest_chain"] = [
            summarize_component_label(node, components) for node in reconstruct_chain(cid, best_pred)
        ]
    return payload


def build_report_payload(
    *,
    root: Path,
    dep_g: nx.DiGraph,
    components: list[set[str]],
    causal_g: nx.DiGraph,
    decl_meta: dict[str, dict[str, Any]],
    file_debt: dict[str, float],
    findings_by_index: dict[str, list[dict[str, Any]]],
    audit_counts: dict[str, int],
    min_depth: list[int],
    max_depth: list[int],
    best_pred: list[int | None],
    top_per_layer: int,
    top_capstones: int,
    top_roots: int,
    top_modules: int,
) -> dict[str, Any]:
    roots = sorted(int(node) for node in causal_g.nodes() if causal_g.in_degree(node) == 0)
    capstones = sorted(int(node) for node in causal_g.nodes() if causal_g.out_degree(node) == 0)

    component_debt: dict[int, float] = {}
    component_load: dict[int, float] = {}
    component_inertia: dict[int, float] = {}
    component_notes: dict[int, str] = {}
    component_capstone_support: dict[int, int] = {}

    for node in causal_g.nodes():
        cid = int(node)
        descendants = nx.descendants(causal_g, cid)
        supported_capstones = descendants.intersection(capstones)
        if cid in capstones:
            supported_capstones = set(supported_capstones)
            supported_capstones.add(cid)

        files = component_file_set(cid, components, decl_meta)
        debt = sum(file_debt.get(path, 0.0) for path in files)
        load = float(len(descendants) + 2 * len(supported_capstones))
        inertia = load / (1.0 + debt)

        component_debt[cid] = debt
        component_load[cid] = load
        component_inertia[cid] = inertia
        component_capstone_support[cid] = len(supported_capstones)
        if cid in roots:
            component_notes[cid] = "Bedrock" if debt == 0.0 else "Soft bedrock"
        elif cid in capstones:
            component_notes[cid] = "Capstone"
        else:
            component_notes[cid] = "-"

    by_layer: dict[int, list[int]] = defaultdict(list)
    for node in causal_g.nodes():
        cid = int(node)
        by_layer[max_depth[cid]].append(cid)

    root_impact: dict[int, int] = defaultdict(int)
    capstone_root_cones: list[dict[str, Any]] = []
    for cap in capstones:
        support_roots = sorted(nx.ancestors(causal_g, cap).intersection(roots))
        if cap in roots:
            support_roots = sorted(set(support_roots + [cap]))
        for root_id in support_roots:
            root_impact[root_id] += 1
        capstone_root_cones.append(
            {
                "capstone": summarize_component_label(cap, components),
                "roots": [summarize_component_label(root_id, components) for root_id in support_roots],
            }
        )

    dominant_roots = sorted(
        roots,
        key=lambda cid: (-root_impact.get(cid, 0), -component_load[cid], summarize_component_label(cid, components)),
    )[:top_roots]

    deepest_capstones = sorted(
        capstones,
        key=lambda cid: (-max_depth[cid], -component_load[cid], summarize_component_label(cid, components)),
    )[:top_capstones]

    layers: list[dict[str, Any]] = []
    max_layer = max(max_depth) if max_depth else 0
    for level in range(max_layer + 1):
        rows = sorted(
            by_layer.get(level, []),
            key=lambda cid: (-component_load[cid], -component_inertia[cid], summarize_component_label(cid, components)),
        )[:top_per_layer]
        layers.append(
            {
                "depth": level,
                "components": [
                    component_payload(
                        cid=cid,
                        components=components,
                        decl_meta=decl_meta,
                        min_depth=min_depth,
                        max_depth=max_depth,
                        component_debt=component_debt,
                        component_load=component_load,
                        component_inertia=component_inertia,
                        component_notes=component_notes,
                        component_capstone_support=component_capstone_support,
                    )
                    for cid in rows
                ],
            }
        )

    module_rows: dict[str, dict[str, Any]] = {}
    for node in causal_g.nodes():
        cid = int(node)
        files = component_file_set(cid, components, decl_meta)
        modules = component_module_set(cid, components, decl_meta)
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

    modules_payload: list[dict[str, Any]] = []
    for module, row in sorted(module_rows.items(), key=lambda item: (-item[1]["age"], -item[1]["load"], item[0]))[:top_modules]:
        debt = sum(file_debt.get(path, 0.0) for path in row["files"])
        inertia = row["load"] / (1.0 + debt)
        note = "-"
        if row["has_root"]:
            note = "Bedrock module" if debt == 0.0 else "Soft bedrock module"
        elif row["has_capstone"]:
            note = "Capstone module"
        modules_payload.append(
            {
                "module": module,
                "age": row["age"],
                "min_depth": row["min_depth"] if row["min_depth"] != 10**9 else -1,
                "load": row["load"],
                "debt": debt,
                "inertia": inertia,
                "note": note,
                "file_count": len(row["files"]),
                "component_count": len(row["components"]),
            }
        )

    coverage = compute_graph_coverage(
        root=root,
        decl_meta=decl_meta,
        findings_by_index=findings_by_index,
        file_debt=file_debt,
    )

    payload = {
        "summary": {
            "declaration_nodes": dep_g.number_of_nodes(),
            "declaration_edges": dep_g.number_of_edges(),
            "scc_components": len(components),
            "layers": max_layer + 1,
            "roots": len(roots),
            "capstones": len(capstones),
            "audit_counts": audit_counts,
            "graph_coverage": {
                "repo_lean_files": coverage["repo_lean_files"],
                "repo_decl_files": coverage["repo_decl_files"],
                "decl_index_files": coverage["decl_index_files"],
                "import_only_files_count": coverage["import_only_files_count"],
                "missing_decl_files_count": coverage["missing_decl_files_count"],
                "is_partial": coverage["is_partial"],
                "uncovered_debt_file_count": coverage["uncovered_debt_file_count"],
            },
        },
        "orientation": {
            "raw_graph": "declaration -> dependency",
            "causal_graph": "dependency -> dependent (SCC-condensed reverse DAG)",
            "root_definition": "components with no outgoing internal dependencies in the raw declaration DAG",
            "capstone_definition": "components with no incoming internal dependents in the raw declaration DAG",
        },
        "coverage": coverage,
        "roots": [
            component_payload(
                cid=cid,
                components=components,
                decl_meta=decl_meta,
                min_depth=min_depth,
                max_depth=max_depth,
                component_debt=component_debt,
                component_load=component_load,
                component_inertia=component_inertia,
                component_notes=component_notes,
                component_capstone_support=component_capstone_support,
                include_extras=True,
            )
            for cid in dominant_roots
        ],
        "layers": layers,
        "deepest_capstones": [
            component_payload(
                cid=cid,
                components=components,
                decl_meta=decl_meta,
                min_depth=min_depth,
                max_depth=max_depth,
                component_debt=component_debt,
                component_load=component_load,
                component_inertia=component_inertia,
                component_notes=component_notes,
                component_capstone_support=component_capstone_support,
                best_pred=best_pred,
                include_longest_chain=True,
            )
            for cid in deepest_capstones
        ],
        "modules": modules_payload,
        "capstone_root_cones": sorted(capstone_root_cones, key=lambda row: row["capstone"])[:top_capstones],
    }
    return payload


def render_markdown(payload: dict[str, Any]) -> str:
    summary = payload["summary"]
    audit_counts = summary.get("audit_counts", {})
    coverage = payload.get("coverage", {})
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
    lines.append("Trusted inputs and outputs are split intentionally:")
    lines.append("")
    lines.append("- `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl` are the public authoritative declaration-graph inputs")
    lines.append("- `.build/` remains a transient Lean build cache and compatibility fallback, not the documented public DAG surface")
    lines.append("- `reports/dag/true-root-order.{md,json}` are derived causal-order reports")
    lines.append("- `reports/dag/openclaw-targets.{md,json}` are derived operational rankings on top of that causal report")
    lines.append("")
    lines.append("So:")
    lines.append("")
    lines.append("- **roots** are components with no outgoing internal dependencies")
    lines.append("- **capstones** are components with no incoming internal dependents")
    lines.append("- **theoretical age** is the maximal depth from the root set on the reversed causal DAG")
    lines.append("- **inertia** is reverse structural load penalized by weighted debt")
    lines.append("")
    lines.append("## Structural Summary")
    lines.append(f"- declaration nodes: `{summary.get('declaration_nodes', 0)}`")
    lines.append(f"- declaration edges: `{summary.get('declaration_edges', 0)}`")
    lines.append(f"- SCC components: `{summary.get('scc_components', 0)}`")
    lines.append(f"- total layers: `{summary.get('layers', 0)}`")
    lines.append(f"- root components: `{summary.get('roots', 0)}`")
    lines.append(f"- capstone components: `{summary.get('capstones', 0)}`")
    lines.append(f"- thinness findings: `{audit_counts.get('thinness', 0)}`")
    lines.append(f"- vacuity findings: `{audit_counts.get('vacuity', 0)}`")
    lines.append(f"- surrogate findings: `{audit_counts.get('surrogate', 0)}`")
    lines.append(f"- repo Lean files under `lean/InfoGeometry`: `{coverage.get('repo_lean_files', 0)}`")
    lines.append(f"- declaration-bearing source files under `lean/InfoGeometry`: `{coverage.get('repo_decl_files', 0)}`")
    lines.append(f"- import-only / umbrella Lean files: `{coverage.get('import_only_files_count', 0)}`")
    lines.append(f"- declaration-index files in current `.build` graph: `{coverage.get('decl_index_files', 0)}`")
    lines.append(f"- missing declaration-bearing files from graph coverage: `{coverage.get('missing_decl_files_count', 0)}`")
    lines.append(f"- debt files currently outside graph coverage: `{coverage.get('uncovered_debt_file_count', 0)}`")
    lines.append("")
    lines.append("## Coverage Warning")
    if coverage.get("is_partial"):
        lines.append(
            "- The current `.build` declaration graph is partial relative to the live declaration-bearing `lean/InfoGeometry` files."
        )
        lines.append(
            "- Import-only and umbrella files are counted separately and do not trigger this coverage gate."
        )
        lines.append(
            "- Any debt file listed below is invisible to the current graph-based inertia ranking and must not be treated as resolved."
        )
    else:
        lines.append(
            "- The current `.build` declaration graph covers the live declaration-bearing `lean/InfoGeometry` files."
        )
        lines.append(
            "- Import-only and umbrella files are counted separately and do not trigger the coverage gate."
        )
    uncovered_debt_files = coverage.get("uncovered_debt_files", [])
    if uncovered_debt_files:
        lines.append("")
        lines.append("### Debt Outside Graph Coverage")
        for row in uncovered_debt_files:
            line_suffix = f":{row['lines'][0]}" if row.get("lines") else ""
            lines.append(
                f"- `{row.get('file')}{line_suffix}` | score `{row.get('score', 0.0):.2f}` | "
                f"indices `{', '.join(row.get('indices', [])) or '-'}` | priorities `{', '.join(row.get('priorities', [])) or '-'}`"
            )
    if coverage.get("missing_decl_files"):
        lines.append("")
        lines.append("### First Missing Declaration-Bearing Lean Files")
        for file_name in coverage["missing_decl_files"][:20]:
            lines.append(f"- `{file_name}`")
    lines.append("")
    lines.append("## Root Set")
    roots = payload.get("roots", [])
    if roots:
        for row in roots:
            file_display = ", ".join(f"`{path}`" for path in row.get("files", [])[:3]) if row.get("files") else "-"
            if len(row.get("files", [])) > 3:
                file_display += f", ... (+{len(row['files']) - 3} more)"
            lines.append(
                f"- `{row.get('label')}` | load `{row.get('load', 0.0):.2f}` | inertia `{row.get('inertia', 0.0):.2f}` | "
                f"supports `{row.get('capstones_supported', 0)}` capstones | files: {file_display}"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Layer Stratigraphy (SCC-condensed declarations)")
    lines.append("")
    lines.append("| Layer | Representative SCC | Size | Min depth | Max depth | Reverse load | Debt | Inertia | Notes |")
    lines.append("| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | :--- |")
    for layer in payload.get("layers", []):
        depth = layer.get("depth", 0)
        for row in layer.get("components", []):
            lines.append(
                f"| {depth} | `{row.get('label')}` | {row.get('size', 0)} | {row.get('depth_min', -1)} | "
                f"{row.get('depth_max', -1)} | {row.get('load', 0.0):.2f} | {row.get('debt', 0.0):.2f} | "
                f"{row.get('inertia', 0.0):.2f} | {row.get('note', '-')} |"
            )
    lines.append("")
    lines.append("## Deepest Capstones")
    deepest_capstones = payload.get("deepest_capstones", [])
    if deepest_capstones:
        for row in deepest_capstones:
            lines.append(
                f"- `{row.get('label')}` | layer `{row.get('depth_max', -1)}` | reverse load `{row.get('load', 0.0):.2f}` | "
                f"inertia `{row.get('inertia', 0.0):.2f}`"
            )
            chain = " -> ".join(f"`{name}`" for name in row.get("longest_chain", []))
            lines.append(f"  longest causal chain: {chain or '-'}")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Dominant Roots By Capstone Support")
    if roots:
        for row in roots:
            lines.append(
                f"- `{row.get('label')}` supports `{row.get('capstones_supported', 0)}` capstones "
                f"(load `{row.get('load', 0.0):.2f}`, inertia `{row.get('inertia', 0.0):.2f}`)"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Capstone Root Cones")
    if payload.get("capstone_root_cones"):
        for row in payload["capstone_root_cones"]:
            roots_display = ", ".join(f"`{name}`" for name in row.get("roots", [])[:10]) if row.get("roots") else "-"
            if len(row.get("roots", [])) > 10:
                roots_display += f", ... (+{len(row['roots']) - 10} more)"
            lines.append(f"- `{row.get('capstone')}` <- {roots_display}")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Module Rollup")
    lines.append("")
    lines.append("| Module | Age | Min depth | Load | Debt | Inertia | Notes |")
    lines.append("| :--- | ---: | ---: | ---: | ---: | ---: | :--- |")
    for row in payload.get("modules", []):
        lines.append(
            f"| `{row.get('module')}` | {row.get('age', 0)} | {row.get('min_depth', -1)} | "
            f"{row.get('load', 0.0):.2f} | {row.get('debt', 0.0):.2f} | {row.get('inertia', 0.0):.2f} | {row.get('note', '-')} |"
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
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    root = repo_root()

    graph_path = normalize_user_path(args.graph, root)
    decls_path = normalize_user_path(args.decls, root)
    thinness_path = normalize_user_path(args.thinness_index, root)
    vacuity_path = normalize_user_path(args.vacuity_index, root)
    surrogate_path = normalize_user_path(args.surrogate_index, root)
    out_path = normalize_user_path(args.out, root)
    json_out_path = normalize_user_path(args.json_out, root)

    if not graph_path.exists():
        raise SystemExit(f"missing required graph artifact: {graph_path}")
    if not decls_path.exists():
        raise SystemExit(f"missing required declaration metadata artifact: {decls_path}")

    decl_meta = load_decl_metadata(decls_path, root)
    file_debt, findings_by_index, audit_counts = load_debt_scores(
        root,
        thinness_path,
        vacuity_path,
        surrogate_path,
    )

    dep_g = build_dependency_graph(graph_path)
    components, _comp_of, dep_comp_g = scc_condensation(dep_g)
    causal_g = dep_comp_g.reverse(copy=True)
    min_depth, max_depth, best_pred = compute_depths(causal_g)

    payload = build_report_payload(
        root=root,
        dep_g=dep_g,
        components=components,
        causal_g=causal_g,
        decl_meta=decl_meta,
        file_debt=file_debt,
        findings_by_index=findings_by_index,
        audit_counts=audit_counts,
        min_depth=min_depth,
        max_depth=max_depth,
        best_pred=best_pred,
        top_per_layer=args.top_per_layer,
        top_capstones=args.top_capstones,
        top_roots=args.top_roots,
        top_modules=args.top_modules,
    )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    json_out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(render_markdown(payload) + "\n", encoding="utf-8")
    json_out_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    print(f"[causal-report] wrote {out_path}")
    print(f"[causal-report] wrote {json_out_path}")
    coverage = payload.get("coverage", {})
    errors: list[str] = []
    if coverage.get("is_partial") and not args.allow_partial_coverage:
        errors.append(
            "declaration graph coverage is partial "
            f"({coverage.get('decl_index_files', 0)} / {coverage.get('repo_decl_files', 0)} declaration-bearing files)"
        )
    if coverage.get("uncovered_debt_file_count", 0) and not args.allow_uncovered_debt:
        errors.append(
            "audited debt files lie outside declaration graph coverage "
            f"({coverage.get('uncovered_debt_file_count', 0)} files)"
        )
    if errors:
        raise SystemExit("[causal-report] coverage gate failed: " + " | ".join(errors))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
