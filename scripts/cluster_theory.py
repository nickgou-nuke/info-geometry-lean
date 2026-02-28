#!/usr/bin/env python3
# scripts/cluster_theory.py  (patched: outputs full membership + stable hub + keeps samples)

import argparse
import json
import random
from collections import defaultdict
from pathlib import Path

import igraph as ig
import leidenalg as la


def load_full_graph(path: Path) -> tuple[list[str], list[list[list]]]:
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    return data["nodes"], data["forward"]


def build_igraph(nodes: list[str], forward) -> ig.Graph:
    g = ig.Graph(directed=True)
    g.add_vertices(len(nodes))
    g.vs["name"] = nodes

    edges = []
    for u, adj in enumerate(forward):
        for item in adj:
            # item is [v, kind] from the Lean-exported JSON
            v = item[0]
            edges.append((u, v))
    if edges:
        g.add_edges(edges)

    return g


def choose_hub(g: ig.Graph, member_idxs: list[int]) -> str:
    # Robust hub heuristic: highest (in+out) degree in induced subgraph.
    sub = g.subgraph(member_idxs)
    deg = sub.degree(mode="all")
    hub_local = max(range(len(deg)), key=lambda i: deg[i])
    hub_global = member_idxs[hub_local]
    return g.vs[hub_global]["name"]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph", default="full_graph.json", help="Path to full_graph.json")
    ap.add_argument("--out", default="theory_toc.json", help="Output path for clusters")
    ap.add_argument(
        "--objective",
        default="modularity",
        choices=["modularity", "rbconfig"],
        help="Leiden objective",
    )
    ap.add_argument(
        "--toc-min_size",
        type=int,
        default=5,
        help="Clusters smaller than this are marked include_in_toc=false (but still exported).",
    )
    ap.add_argument(
        "--seed",
        type=int,
        default=0,
        help="Random seed (0 means random; set for reproducibility).",
    )
    args = ap.parse_args()

    graph_path = Path(args.graph)
    if not graph_path.exists():
        raise SystemExit(f"Error: {graph_path} not found.")

    nodes, forward = load_full_graph(graph_path)
    g = build_igraph(nodes, forward)

    if args.seed != 0:
        random.seed(args.seed)

    print(f"Clustering {g.vcount()} nodes, {g.ecount()} edges using Leiden ({args.objective})...")

    if args.objective == "modularity":
        partition = la.find_partition(g, la.ModularityVertexPartition, seed=args.seed if args.seed != 0 else None)
    else:
        partition = la.find_partition(g, la.RBConfigurationVertexPartition, seed=args.seed if args.seed != 0 else None)

    members_by_cluster: dict[int, list[int]] = defaultdict(list)
    for vidx, cid in enumerate(partition.membership):
        members_by_cluster[cid].append(vidx)

    clusters = []
    for cid, member_idxs in sorted(members_by_cluster.items(), key=lambda kv: len(kv[1]), reverse=True):
        member_names = [nodes[i] for i in member_idxs]
        hub = choose_hub(g, member_idxs)

        clusters.append(
            {
                "cluster_id": cid,
                "size": len(member_names),
                "hub": hub,
                "members": member_names,          # FULL membership (critical)
                "samples": member_names[:10],     # convenience/UI
                "include_in_toc": len(member_names) >= args.toc_min_size,
            }
        )

    out_path = Path(args.out)
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(clusters, f, indent=2, ensure_ascii=False)

    print(f"Found {len(clusters)} clusters. Wrote {out_path}")
    print("\n--- Theory TOC (Top 10 clusters by size) ---")
    for i, c in enumerate(clusters[:10], start=1):
        print(f"{i:>2}. cluster={c['cluster_id']} size={c['size']} hub={c['hub']} toc={c['include_in_toc']}")
        samp = ", ".join(c["samples"][:3])
        print(f"    samples: {samp}{'...' if len(c['samples']) > 3 else ''}")


if __name__ == "__main__":
    main()
