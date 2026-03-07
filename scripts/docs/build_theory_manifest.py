#!/usr/bin/env python3
# scripts/build_theory_manifest.py (patched: merges decls+morphisms+topology+clusters, validates completeness)

import argparse
import json
from pathlib import Path
from collections import defaultdict


def load_json(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def load_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    out = []
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                out.append(json.loads(line))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".", help="Project root (contains index/ and full_graph.json)")
    ap.add_argument("--out", default="theory_manifest.json", help="Output manifest path")
    ap.add_argument("--strict", action="store_true", help="Fail on validation warnings")
    args = ap.parse_args()

    root = Path(args.root)
    index_dir = root / "index"

    full_graph_path = root / "full_graph.json"
    theory_toc_path = root / "theory_toc.json"
    metrics_path = root / "topological_metrics.json"

    decls_path = index_dir / "decls.jsonl"
    morphisms_path = index_dir / "morphisms.jsonl"

    required = [full_graph_path, theory_toc_path, metrics_path, decls_path, morphisms_path]
    missing = [p for p in required if not p.exists()]
    if missing:
        raise SystemExit(f"Error: Missing required files: {[str(p) for p in missing]}")

    graph_data = load_json(full_graph_path)
    toc_data = load_json(theory_toc_path)
    metrics_data = load_json(metrics_path)

    decls_list = load_jsonl(decls_path)
    morphisms_list = load_jsonl(morphisms_path)

    all_graph_nodes: list[str] = graph_data["nodes"]
    graph_node_set = set(all_graph_nodes)

    warnings = []

    # --- Index auxiliary metadata ---
    decls_by_name = {d["name"]: d for d in decls_list}
    metrics_by_name = {m["name"]: m for m in metrics_data.get("metrics", [])}

    morphisms_by_decl: dict[str, list[dict]] = defaultdict(list)
    for m in morphisms_list:
        morphisms_by_decl[m["declName"]].append(m)

    # --- Cluster membership map (full membership required) ---
    node_to_cluster: dict[str, int] = {}
    cluster_nodes_seen = set()

    for c in toc_data:
        if "members" not in c:
            raise SystemExit("Error: theory_toc.json clusters must contain a 'members' field (full membership).")

        cid = c["cluster_id"]
        for n in c["members"]:
            if n in node_to_cluster:
                warnings.append(f"Node assigned to multiple clusters: {n} ({node_to_cluster[n]} and {cid})")
            node_to_cluster[n] = cid
            cluster_nodes_seen.add(n)

    # Validate: cluster nodes exist in graph
    cluster_not_in_graph = sorted([n for n in cluster_nodes_seen if n not in graph_node_set])
    if cluster_not_in_graph:
        warnings.append(f"{len(cluster_not_in_graph)} clustered nodes are missing from full_graph.json (name drift).")

    # Validate: graph nodes missing from decls
    missing_decls = sorted([n for n in all_graph_nodes if n not in decls_by_name])
    if missing_decls:
        warnings.append(f"{len(missing_decls)} graph nodes have no decl metadata in index/decls.jsonl.")

    # Validate: metrics coverage
    missing_metrics = sorted([n for n in all_graph_nodes if n not in metrics_by_name])
    if missing_metrics:
        warnings.append(f"{len(missing_metrics)} graph nodes have no metrics entry in topological_metrics.json.")

    # --- Build clusters registry (JSON-friendly keys) ---
    clusters_registry = {}
    for c in toc_data:
        cid = c["cluster_id"]
        clusters_registry[str(cid)] = c

    # --- Build node registry ---
    nodes_registry = {}
    for node_name in all_graph_nodes:
        decl = decls_by_name.get(node_name, {})
        met = metrics_by_name.get(node_name, {"reach": 0, "paths": 0, "triangles": 0})
        cid = node_to_cluster.get(node_name)

        nodes_registry[node_name] = {
            "name": node_name,
            "kind": decl.get("kind", "unknown"),
            "module": decl.get("module", "unknown"),
            "location": {
                "file": decl.get("file", "unknown"),
                "line": decl.get("line", 0),
                "column": decl.get("column", 0),
            },
            "metrics": met,
            "cluster_id": cid,
            "is_hub": False,  # filled below
            "morphisms": morphisms_by_decl.get(node_name, []),  # LIST, not single (avoids overwrite)
        }

    # Mark hubs
    for c in toc_data:
        hub = c.get("hub")
        if hub in nodes_registry:
            nodes_registry[hub]["is_hub"] = True

    # Validation: unclustered nodes
    unclustered = [n for n in all_graph_nodes if nodes_registry[n]["cluster_id"] is None]
    if unclustered:
        warnings.append(f"{len(unclustered)} nodes are unclustered (not present in any cluster members list).")

    # Validation: metadata count consistency
    computed_total_nodes = len(all_graph_nodes)
    computed_total_edges = sum(len(adj) for adj in graph_data.get("forward", []))
    analyzer_nodes = metrics_data.get("nodes")
    analyzer_edges = metrics_data.get("edges")

    if isinstance(analyzer_nodes, int) and analyzer_nodes != computed_total_nodes:
        warnings.append(f"Analyzer nodes={analyzer_nodes} != graph nodes={computed_total_nodes}.")
    if isinstance(analyzer_edges, int) and analyzer_edges != computed_total_edges:
        warnings.append(f"Analyzer edges={analyzer_edges} != graph edges={computed_total_edges}.")

    # --- Assemble manifest ---
    manifest = {
        "metadata": {
            "graph_total_nodes": computed_total_nodes,
            "graph_total_edges": computed_total_edges,
            "total_faces": metrics_data.get("faces", 0),
            "euler_characteristic": metrics_data.get("chi", 0),
            "connected_components": metrics_data.get("b0", 0),
            "total_clusters": len(toc_data),
            "warnings": warnings,
        },
        "clusters": clusters_registry,
        "nodes": nodes_registry,
        "edges": graph_data["forward"],
    }

    if warnings:
        msg = "\n".join([f"- {w}" for w in warnings])
        print("Validation warnings:\n" + msg)
        if args.strict:
            raise SystemExit("Strict mode: failing due to validation warnings.")

    out_path = root / args.out
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, ensure_ascii=False)

    print(f"Successfully built {out_path} with {len(nodes_registry)} nodes and {len(clusters_registry)} clusters.")
    print("Artifacts merged: Decls, Morphisms, Topology, Clusters.")


if __name__ == "__main__":
    main()
