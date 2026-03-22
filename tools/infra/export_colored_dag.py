#!/usr/bin/env python3
import json
import networkx as nx
from pathlib import Path
import sys

def main():
    # Load nodes and edges from full_graph.json
    graph_path = Path("artifacts/dag/full_graph.json")
    if not graph_path.exists():
        print(f"Error: {graph_path} not found.")
        return 1
    
    with open(graph_path, "r") as f:
        graph_data = json.load(f)
    
    nodes_list = graph_data["nodes"]
    edges_list = graph_data["forward"]
    
    # Load categories from theorem-surface-index.json
    index_path = Path("reports/dag/theorem-surface-index.json")
    if not index_path.exists():
        print(f"Error: {index_path} not found. Run tools/infra/generate_theorem_surface_index.py first.")
        return 1
    
    with open(index_path, "r") as f:
        index_data = json.load(f)
    
    # Map node name to category
    name_to_category = {row["name"]: row["category"] for row in index_data["rows"]}
    
    # Define colors
    category_colors = {
        "likely_constructive": "green",
        "hypothesis_bridge": "blue",
        "package_reprojection": "orange",
        "surrogate_or_vacuous": "red",
        "neutral_definition": "grey"
    }
    
    # Create NetworkX graph
    G = nx.DiGraph()
    
    # Add nodes with attributes
    for i, name in enumerate(nodes_list):
        category = name_to_category.get(name, "unknown")
        color = category_colors.get(category, "black")
        # Extract module from name (assuming it's the prefix)
        module = ".".join(name.split(".")[:-1])
        G.add_node(i, name=name, category=category, color=color, module=module)
    
    # Add edges
    for source_idx, source_edges in enumerate(edges_list):
        for target_idx, edge_type in source_edges:
            G.add_edge(source_idx, target_idx, type=edge_type)
    
    # Print some stats
    print(f"Graph loaded: {G.number_of_nodes()} nodes, {G.number_of_edges()} edges")
    
    # Identify specific "trunks" for detailed analysis
    trunks = {
        "Primitive Split-Krein": [
            "InfoGeometry.Krein.KreinGradedModule",
            "InfoGeometry.Quantum.RealSplitCl11Action",
            "InfoGeometry.KK.RealSplitKreinKasparovCycle",
            "InfoGeometry.KK.RealSplitKreinUnboundedCycle"
        ],
        "KK / Analytical Index": [
            "InfoGeometry.KK.KasparovCycle.analyticalIndex",
            "InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex",
            "InfoGeometry.Canonical.GrandSynthesis.grandSynthesis"
        ],
        "Modular / Rosetta": [
            "InfoGeometry.Canonical.Rosetta.source_tension_rosetta_three_presentations",
            "InfoGeometry.Quantum.ModularAnomaly.unified_anomaly_bridge",
            "InfoGeometry.Canonical.TomitaTakesaki.relativeTomitaTakesakiOp"
        ],
        "Discrete Phase / RG": [
            "InfoGeometry.Quantum.HurwitzShellAction",
            "InfoGeometry.Quantum.HurwitzRGFlow.betaFunction_eq_zero_of_invariantAtScale",
            "InfoGeometry.Canonical.RGFlow.existsUnique_fixedPoint_of_contracting"
        ],
        "Topological / Kitaev": [
            "InfoGeometry.Quantum.KitaevChain.index_change_forces_defect_crossing"
        ],
        "Analytic / Softmax": [
            "InfoGeometry.Analytic.deriv2_logSumExp_eq_softmaxVariance",
            "InfoGeometry.Analytic.deriv_logSumExp_eq_firstMoment_div_partition"
        ]
    }
    
    # Reverse mapping for nodes to indices
    name_to_idx = {name: i for i, name in enumerate(nodes_list)}
    
    print("\nTrunk Connectivity and Classification:")
    for trunk_name, seeds in trunks.items():
        print(f"--- {trunk_name} ---")
        for seed in seeds:
            if seed not in name_to_idx:
                print(f"  [Not Found] {seed}")
                continue
            idx = name_to_idx[seed]
            node_data = G.nodes[idx]
            deps = list(G.successors(idx))
            rev_deps = list(G.predecessors(idx))
            print(f"  Node: {seed} ({node_data['category']}, {node_data['color']})")
            print(f"    Dependencies: {len(deps)} | Dependent on: {len(rev_deps)}")
            
            # Print a few immediate dependencies classifications
            dep_cats = Counter([G.nodes[d]["category"] for d in deps])
            print(f"    Dep Category mix: {dict(dep_cats)}")
    
    # Export GraphML for external viewing
    output_path = Path("reports/dag/theory_dag.graphml")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    nx.write_graphml(G, output_path)
    print(f"\nGraphML exported to {output_path}")

from collections import Counter
if __name__ == "__main__":
    main()
