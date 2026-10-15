#!/usr/bin/env python3
"""
AST AQL Graph Analysis: Cliques, Hashes, and Conductive Wires.
Adapts older DAG graph-theoretic algorithms to the new AST AQL workflow.
"""

from __future__ import annotations
import argparse
import hashlib
import json
import re
import sys
from collections import defaultdict, deque
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple

REPO_ROOT = Path(__file__).resolve().parents[2]
if __package__ in (None, ""):
    sys.path.insert(0, str(REPO_ROOT))

from tools.quality.semantic_vacuity_gate import strip_comments

def stable_hash(obj: Any) -> str:
    payload = json.dumps(obj, sort_keys=True)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]

def load_graph(path: Path) -> Dict[str, Any]:
    print(f"Loading graph from {path}...")
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def inspect_node_sources(nodes: List[Dict[str, Any]], repo_root: Path) -> Dict[str, Any]:
    """Inspect full lexical declaration spans; missing/stale sources stay unknown."""
    cache = {}
    hashes = {}
    contaminated, unknown = set(), set()
    failures = []
    for node in nodes:
        label = node.get("file")
        nid = node["id"]
        if not label:
            unknown.add(nid)
            continue
        if label not in cache:
            path = Path(label)
            candidates = [path] if path.is_absolute() else [repo_root / path, repo_root / "lean" / path, repo_root / "proofs" / path]
            existing = list(dict.fromkeys(p.resolve() for p in candidates if p.is_file()))
            if len(existing) != 1:
                cache[label] = None
                failures.append({"file": label, "error": "missing or ambiguous source path"})
            else:
                try:
                    raw = existing[0].read_text(encoding="utf-8")
                    hashes[label] = hashlib.sha256(raw.encode("utf-8")).hexdigest()
                    cache[label] = strip_comments(raw, mask_literals=True)
                except (OSError, UnicodeError) as exc:
                    cache[label] = None
                    failures.append({"file": label, "error": str(exc)})
        text = cache[label]
        if text is None:
            unknown.add(nid)
            continue
        if node.get("kind") == "Axiom":
            contaminated.add(nid)
        span = node.get("span")
        if (node.get("source_sha256") == hashes.get(label)
                and node.get("span_unit") == "unicode_codepoint" and isinstance(span, list)
                and len(span) == 2 and all(isinstance(x, int) for x in span)
                and 0 <= span[0] <= span[1] <= len(text)):
            body = text[span[0]:span[1]]
        else:
            # Legacy exports lack a validated span. Do not certify them clean.
            unknown.add(nid)
            body = text
        if re.search(r"\b(sorry|admit)\b", body):
            contaminated.add(nid)
    return {"contaminated": contaminated, "unknown": unknown, "read_failures": failures,
            "files_selected": len(cache), "files_read": sum(v is not None for v in cache.values())}


def find_sorries_for_nodes(nodes: List[Dict[str, Any]], repo_root: Path) -> Set[str]:
    """Compatibility API, conservatively includes unknown source declarations."""
    result = inspect_node_sources(nodes, repo_root)
    return result["contaminated"] | result["unknown"]

def propagate_contamination(
    edges: List[Dict[str, Any]],
    initial_contaminated: Set[str],
) -> Set[str]:
    print("Propagating contamination upstream through dependency graph...")
    in_edges = defaultdict(list)
    for edge in edges:
        src = edge["source"]
        dst = edge["target"]
        in_edges[dst].append(src)
        
    contaminated = set(initial_contaminated)
    queue = deque(initial_contaminated)
    while queue:
        curr = queue.popleft()
        for parent in in_edges[curr]:
            if parent not in contaminated:
                contaminated.add(parent)
                queue.append(parent)
    return contaminated

def compute_wl_hashes(
    nodes: List[Dict[str, Any]],
    edges: List[Dict[str, Any]],
    rounds: int = 3,
) -> Dict[str, str]:
    print(f"Computing Weisfeiler-Lehman (WL) hashes (rounds={rounds})...")
    out_edges = defaultdict(list)
    in_edges = defaultdict(list)
    for edge in edges:
        src = edge["source"]
        dst = edge["target"]
        out_edges[src].append(dst)
        in_edges[dst].append(src)
        
    labels = {
        n["id"]: stable_hash({
            "kind": n.get("kind", "unknown"),
            "module": n.get("module", "unknown"),
        })
        for n in nodes
    }
    
    for _ in range(rounds):
        next_labels = {}
        for nid in labels:
            curr = labels[nid]
            neigh_out = sorted((labels[nxt], "out") for nxt in out_edges[nid])
            neigh_in = sorted((labels[src], "in") for src in in_edges[nid])
            next_labels[nid] = stable_hash({
                "self": curr,
                "neighbors": neigh_out + neigh_in,
            })
        labels = next_labels
    return labels

def find_longest_clean_chains(
    nodes: List[Dict[str, Any]],
    edges: List[Dict[str, Any]],
    contaminated: Set[str],
    limit: int = 10,
) -> List[List[str]]:
    print("Extracting longest clean conductive wires...")
    clean_nodes = {n["id"] for n in nodes if n["id"] not in contaminated}
    clean_edges = defaultdict(list)
    in_degree = defaultdict(int)
    
    for nid in clean_nodes:
        in_degree[nid] = 0
        
    for edge in edges:
        src = edge["source"]
        dst = edge["target"]
        if src in clean_nodes and dst in clean_nodes:
            clean_edges[src].append(dst)
            in_degree[dst] += 1
            
    topo_order = []
    zero_in = deque([nid for nid in clean_nodes if in_degree[nid] == 0])
    in_degree_temp = in_degree.copy()
    
    while zero_in:
        curr = zero_in.popleft()
        topo_order.append(curr)
        for nxt in clean_edges[curr]:
            in_degree_temp[nxt] -= 1
            if in_degree_temp[nxt] == 0:
                zero_in.append(nxt)
                
    dp: Dict[str, Tuple[int, str | None]] = {nid: (1, None) for nid in clean_nodes}
    for curr in topo_order:
        curr_len, _ = dp[curr]
        for nxt in clean_edges[curr]:
            nxt_len, _ = dp[nxt]
            if curr_len + 1 > nxt_len:
                dp[nxt] = (curr_len + 1, curr)
                
    longest = sorted(dp.items(), key=lambda x: -x[1][0])
    
    paths = []
    for end_node, (length, _) in longest:
        if len(paths) >= limit:
            break
        path = []
        curr = end_node
        while curr is not None:
            path.append(curr)
            curr = dp[curr][1]
        path.reverse()
        
        is_subpath = False
        for p in paths:
            if all(node in p for node in path):
                is_subpath = True
                break
        if not is_subpath:
            paths.append(path)
            
    return paths

def bron_kerbosch(
    R: Set[str],
    P: Set[str],
    X: Set[str],
    cliques: List[Set[str]],
    adj: Dict[str, Set[str]],
    limit: int = 100,
) -> None:
    if not P and not X:
        cliques.append(R)
        return
    if len(cliques) >= limit:
        return
    pivot = next(iter(P | X))
    for v in list(P - adj[pivot]):
        if len(cliques) >= limit:
            return
        bron_kerbosch(
            R | {v},
            P & adj[v],
            X & adj[v],
            cliques,
            adj,
            limit,
        )
        P.remove(v)
        X.add(v)

def find_namespace_cliques(
    nodes: List[Dict[str, Any]],
    edges: List[Dict[str, Any]],
    limit_per_namespace: int = 3,
) -> Dict[str, List[List[str]]]:
    print("Finding maximal cliques in namespace subgraphs...")
    module_nodes = defaultdict(list)
    for n in nodes:
        module = n.get("module")
        if module:
            module_nodes[module].append(n["id"])
            
    undirected = defaultdict(set)
    for edge in edges:
        src = edge["source"]
        dst = edge["target"]
        undirected[src].add(dst)
        undirected[dst].add(src)
        
    module_cliques = {}
    for module, nids in module_nodes.items():
        if len(nids) < 3:
            continue
        sub_adj = {}
        nid_set = set(nids)
        for nid in nids:
            sub_adj[nid] = undirected[nid] & nid_set
            
        cliques = []
        bron_kerbosch(set(), set(nids), set(), cliques, sub_adj, limit=50)
        cliques = [list(c) for c in cliques if len(c) >= 3]
        cliques.sort(key=len, reverse=True)
        if cliques:
            module_cliques[module] = cliques[:limit_per_namespace]
            
    return module_cliques

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Adapt older DAG analysis tools to the AST AQL workflow"
    )
    parser.add_argument(
        "--graph",
        default="artifacts/leantrail/lean_ast_graph.json",
        help="Input JSON graph path",
    )
    parser.add_argument(
        "--rounds",
        type=int,
        default=3,
        help="Number of WL rounds",
    )
    parser.add_argument(
        "--report-md",
        default="reports/ast_graph_analysis.md",
        help="Markdown report output path",
    )
    parser.add_argument(
        "--report-json",
        default="reports/ast_graph_analysis.json",
        help="JSON report output path",
    )
    args = parser.parse_args()
    
    repo_root = Path(__file__).resolve().parents[2]
    graph_path = Path(args.graph)
    if not graph_path.exists():
        print(f"Error: graph file not found at {graph_path}", file=sys.stderr)
        return 1
        
    graph = load_graph(graph_path)
    nodes = graph["nodes"]
    edges = graph["edges"]
    
    print(f"Loaded {len(nodes)} nodes, {len(edges)} edges.")
    
    extraction_coverage = graph.get("meta", {})
    extraction_complete = extraction_coverage.get("coverage_complete") is True
    source_scan = inspect_node_sources(nodes, repo_root)
    initial_contaminated = source_scan["contaminated"]
    unknown = propagate_contamination(edges, source_scan["unknown"])
    print(f"Initial contaminated declarations: {len(initial_contaminated)}")
    
    contaminated = propagate_contamination(edges, initial_contaminated)
    print(f"Total contaminated declarations (transitive): {len(contaminated)}")
    
    wl_hashes = compute_wl_hashes(nodes, edges, rounds=args.rounds)
    
    longest_chains = find_longest_clean_chains(nodes, edges, contaminated | unknown)
    
    cliques = find_namespace_cliques(nodes, edges)
    
    # Save JSON report
    report_json_path = Path(args.report_json)
    report_json_path.parent.mkdir(parents=True, exist_ok=True)
    report_data = {
        "authority": "lexical reference graph heuristics; no kernel verification or nonvacuity claim",
        "extraction_coverage": extraction_coverage,
        "source_coverage": {k: v for k, v in source_scan.items() if k not in {"contaminated", "unknown"}},
        "unknown_nodes": sorted(unknown),
        "summary": {
            "total_nodes": len(nodes),
            "total_edges": len(edges),
            "lexical_hole_free_candidates": len(nodes) - len(contaminated | unknown),
            "contaminated_nodes": len(contaminated),
            "lexical_hole_free_percentage": round(100 * (len(nodes) - len(contaminated | unknown)) / len(nodes), 2)
            if len(nodes) else 0,
        },
        "longest_clean_chains": longest_chains,
        "wl_hashes": {nid: wl_hashes[nid] for nid in sorted(wl_hashes.keys())[:100]},
        "cliques": {mod: clq[:3] for mod, clq in sorted(cliques.items())[:50]},
    }
    
    with open(report_json_path, "w", encoding="utf-8") as f:
        json.dump(report_data, f, indent=2, ensure_ascii=False)
    print(f"✓ Saved JSON report to {report_json_path}")
    
    # Save Markdown report
    report_md_path = Path(args.report_md)
    report_md_path.parent.mkdir(parents=True, exist_ok=True)
    with open(report_md_path, "w", encoding="utf-8") as f:
        f.write("# AST AQL Graph Analysis Report\n\n")
        f.write("## Graph Metrics\n\n")
        f.write(f"- **Total Nodes:** {len(nodes)}\n")
        f.write(f"- **Total Edges:** {len(edges)}\n")
        f.write(f"- **Nodes without detected lexical holes (not verified):** {len(nodes) - len(contaminated | unknown)}\n")
        f.write(f"- **Contaminated Nodes:** {len(contaminated)}\n")
        f.write(f"- **Lexical hole-free candidate ratio:** {report_data['summary']['lexical_hole_free_percentage']}%\n\n")
        
        f.write("## Longest candidate chains excluding holes and unknown sources\n\n")
        for i, path in enumerate(longest_chains, start=1):
            f.write(f"### Wire #{i} (Length: {len(path)})\n\n")
            for node in path:
                f.write(f"- `{node}`\n")
            f.write("\n")
            
        f.write("## Representative Weisfeiler-Lehman (WL) Hashes (Sample)\n\n")
        f.write("| Node ID | WL Hash |\n")
        f.write("| --- | --- |\n")
        for nid, whash in list(wl_hashes.items())[:20]:
            f.write(f"| `{nid}` | `{whash}` |\n")
        f.write("\n")
        
        f.write("## Namespace Cliques (Sample)\n\n")
        for mod, clqs in list(cliques.items())[:15]:
            f.write(f"### Module: `{mod}`\n\n")
            for j, clq in enumerate(clqs, start=1):
                f.write(f"**Clique #{j} (Size: {len(clq)}):**\n")
                for node in clq:
                    f.write(f"- `{node}`\n")
                f.write("\n")
                
    print(f"✓ Saved Markdown report to {report_md_path}")
    return 2 if not extraction_complete or unknown or source_scan["read_failures"] else 0

if __name__ == "__main__":
    sys.exit(main())
