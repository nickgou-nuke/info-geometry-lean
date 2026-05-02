#!/usr/bin/env python3
"""Generate a Spire-layered SVG visualization of the theory graph.

Implements a Molecular Dynamics-style relaxation (Gradient Descent) while 
snapping to Spire layers. Uses meaningful Lean declaration names for labels.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

import matplotlib.pyplot as plt
import networkx as nx

_REPO_ROOT = Path(__file__).resolve().parents[2]
if __package__ in (None, ""):
    sys.path.insert(0, str(_REPO_ROOT))
    from tools.infra.arango_raw_infotree_ingest import ArangoTarget, db_url, request_json
else:
    from tools.infra.arango_raw_infotree_ingest import ArangoTarget, db_url, request_json

REP_LAYERS = [
    "L0_Count",
    "L1_Projective",
    "L2_Operator",
    "L3_Krein",
    "L4_ModularTransport",
    "L5_ThermodynamicClosure",
]

def run_aql(target: ArangoTarget, query: str, bind_vars: dict[str, Any] | None = None) -> list[Any]:
    payload = {"query": query, "bindVars": bind_vars or {}}
    out = request_json("POST", db_url(target, "/_api/cursor"), username=target.username, password=target.password, payload=payload)
    return list(out.get("result", []))

def compute_layout(G: nx.DiGraph) -> dict[str, tuple[float, float]]:
    # 1. High-Iteration Molecular Relaxation
    # We use a very high k and many iterations to simulate gradient descent
    pos = nx.spring_layout(
        G, 
        k=8.0 / math.sqrt(len(G.nodes) or 1), 
        iterations=500, # Deep relaxation
        threshold=1e-5,
        seed=42
    )
    
    # 2. Rescale, Center, and Layer-Snap
    max_rank = max((data.get("topo_rank", 0) for _, data in G.nodes(data=True)), default=30000)
    xs = [p[0] for p in pos.values()]
    avg_x = sum(xs) / len(xs) if xs else 0
    
    relaxed_pos = {}
    for n_id, (x, _) in pos.items():
        data = G.nodes[n_id]
        depth = data.get("dominant_rep_depth")
        
        # Vertical: Spire snap or Normalized Rank distribution
        if depth is not None:
            y = -depth * 1000
        else:
            rank = data.get("topo_rank", 0)
            y = -(rank / max_rank) * (5 * 1000)
            
        # Horizontal: Significant centering and spreading
        relaxed_pos[n_id] = ((x - avg_x) * 6000, y)
        
    return relaxed_pos

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default="http://127.0.0.1:8530")
    parser.add_argument("--database", default="infogeometry")
    parser.add_argument("--username", default="root")
    parser.add_argument("--password", default="")
    parser.add_argument("--out", type=Path, default=Path("reports/dag/theory_spire.svg"))
    parser.add_argument("--max-nodes", type=int, default=800)
    args = parser.parse_args()

    target = ArangoTarget(endpoint=str(args.endpoint).rstrip("/"), database=str(args.database), username=str(args.username), password=str(args.password))

    # Fetch components with meaningful metadata
    nodes = run_aql(target, """
        FOR n IN arango_dag_components
          SORT n.member_count DESC
          LIMIT @max_nodes
          RETURN n
    """, {"max_nodes": args.max_nodes})

    if not nodes:
        print("No nodes found. Run algorithms first.")
        return 1

    node_ids = {n["_id"] for n in nodes}
    edges = run_aql(target, """
        FOR e IN arango_dag_component_edges
          FILTER e._from IN @node_ids && e._to IN @node_ids
          RETURN e
    """, {"node_ids": list(node_ids)})

    G = nx.DiGraph()
    for n in nodes: G.add_node(n["_id"], **n)
    for e in edges: G.add_edge(e["_from"], e["_to"], **e)

    pos = compute_layout(G)
    
    # Render settings
    fig, ax = plt.subplots(figsize=(28, 22))
    fig.patch.set_alpha(0.0)
    ax.patch.set_alpha(0.0)
    ax.set_axis_off()
    
    # Symbols based on layer depth
    markers = ['o', 's', 'd', '^', 'v', 'p', 'h'] # Standard NetworkX node shapes
    def get_shape(d):
        return markers[min(d or 6, 6)]

    # Draw nodes per-layer to allow different symbols
    for d in range(7):
        layer_nodes = [n for n in G.nodes if (G.nodes[n].get("dominant_rep_depth") == d or (d == 6 and G.nodes[n].get("dominant_rep_depth") is None))]
        if not layer_nodes: continue
        
        color_val = d / 6.0
        nx.draw_networkx_nodes(
            G, pos, nodelist=layer_nodes, ax=ax,
            node_size=180,
            node_color=[plt.cm.plasma(color_val)] * len(layer_nodes),
            node_shape=get_shape(d),
            edgecolors="black", linewidths=0.6, alpha=0.9
        )

    # Clean straight edges
    nx.draw_networkx_edges(G, pos, ax=ax, alpha=0.15, edge_color="#333333", arrows=True, arrowsize=10, connectionstyle="arc3,rad=0.0")

    # Meaningful Labels: Use representative Lean names
    labels = {}
    # Filter for nodes that are significant (high degree or representative)
    ranked_nodes = sorted(G.nodes, key=lambda n: G.degree(n), reverse=True)
    for n_id in ranked_nodes[:80]: # More labels
        data = G.nodes[n_id]
        rep = data.get("representative")
        if not rep or rep.startswith("scc_"):
            # If representative is meaningless, try to find a sample member that is not internal
            members = data.get("sample_members") or []
            useful = [m for m in members if isinstance(m, str) and "." in m and not m.startswith("_")]
            rep = useful[0] if useful else rep
            
        if rep:
            labels[n_id] = str(rep).split(".")[-1]
    
    nx.draw_networkx_labels(G, pos, ax=ax, labels=labels, font_size=8, font_weight="bold", alpha=0.9)

    # Layer Markers
    min_x = min(p[0] for p in pos.values())
    for depth, name in enumerate(REP_LAYERS):
        ax.text(
            min_x - 1200, -depth * 1000, name, 
            fontsize=20, fontweight='bold', color='white',
            va='center', ha='right',
            bbox=dict(facecolor='#000000', alpha=0.7, edgecolor='none', boxstyle='round,pad=0.5')
        )

    plt.tight_layout(pad=5.0)
    plt.savefig(args.out, format="svg", bbox_inches="tight", transparent=True)
    plt.savefig(args.out.with_suffix(".png"), format="png", dpi=180, bbox_inches="tight", transparent=True)
    print(f"Molecular Theory Spire (Meaningful & Relaxed) saved to: {args.out}")
    
    return 0

if __name__ == "__main__": sys.exit(main())
