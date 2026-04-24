#!/usr/bin/env python3
"""
⚖️ THE PAULI CAUSAL AUDITOR (ArangoDB SCC-Grounded)
Truth lives in Lean; structure lives in the graph.

This script replaces legacy networkx topological sorts with formal 
Causal Stratification from the ArangoDB SCC topology overlay.

The 'True Root Order' is defined by the DAG depth and transitive reach
of the Strongly Connected Components (SCCs).
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent / "tools" / "infra"))
    from tools.infra.decl_graph_support import load_decl_graph
    from tools.pathing import repo_root
else:
    from tools.infra.decl_graph_support import load_decl_graph
    from tools.pathing import repo_root

def main() -> int:
    root = repo_root()
    
    ap = argparse.ArgumentParser(description="Pauli-Authority Causal Report")
    ap.add_argument("--md-out", type=Path, default=root / "reports" / "dag" / "true-root-order.md")
    ap.add_argument("--json-out", type=Path, default=root / "reports" / "dag" / "true-root-order.json")
    args = ap.parse_args()

    # 1. Load ground truth from Pauli Authority (ArangoDB SCCs)
    print("[pauli-causal] Loading formal topology from ArangoDB authority...")
    decl_key_to_full, profiles = load_decl_graph(root)
    
    if not profiles:
        print("[pauli-causal] ERROR: Pauli Authority is unreachable.")
        return 1

    # 2. Extract and Sort Causal Strata
    # We sort by Depth (L0 -> L5) then by Transitive Reach (Causal Mass)
    backbone = [p for p in profiles.values() if p.structural_role == "load_bearing"]
    backbone.sort(key=lambda x: (x.depth, -x.transitive_reverse_reach))

    # 3. Identify Foundations (L0-L1 Roots)
    foundations = [p for p in backbone if p.depth <= 2][:50]
    
    # 4. Identify Capstones (Top of the Spire)
    capstones = [p for p in profiles.values() if p.structural_role == "capstone_endpoint"]
    capstones.sort(key=lambda x: x.depth, reverse=True)

    # 5. Render Report
    md_lines = [
        "# ⚖️ Pauli Authority Audit: True Root Order (Causal Backbone)",
        "",
        "> **Protocol:** Truth lives in Lean; structure lives in the graph.",
        "> **Source:** ArangoDB SCC Topology Overlay.",
        "",
        "## 🏗️ Causal Foundations (The Bedrock)",
        "| Foundation | Depth | Transitive Reach | Location |",
        "| :--- | :---: | :---: | :--- |"
    ]
    
    for f in foundations:
        md_lines.append(f"| `{f.name}` | {f.depth} | {f.transitive_reverse_reach} | `{f.file}:{f.line}` |")

    md_lines.extend([
        "",
        "## 🏹 The Causal Path (L2 -> L4 Propagation)",
        "| Theorem | Depth | Downstream Mass | Role |",
        "| :--- | :---: | :---: | :--- |"
    ])
    
    mid_strata = [p for p in backbone if 2 < p.depth < 8][:50]
    for m in mid_strata:
        md_lines.append(f"| `{m.name}` | {m.depth} | {m.descendant_mass} | `{m.structural_role}` |")

    md_lines.extend([
        "",
        "## 🏔️ Capstone Surfaces (The Spire's Summit)",
        "| Capstone | Peak Depth | Upstream Roots | Location |",
        "| :--- | :---: | :---: | :--- |"
    ])
    
    for c in capstones[:30]:
        md_lines.append(f"| `{c.name}` | {c.depth} | {c.transitive_reverse_reach} | `{c.file}:{c.line}` |")

    args.md_out.write_text("\n".join(md_lines))
    
    # Save formal JSON causal order
    json_out = [
        {"name": p.name, "depth": p.depth, "mass": p.descendant_mass, "reach": p.transitive_reverse_reach}
        for p in backbone
    ]
    args.json_out.write_text(json.dumps(json_out, indent=2))

    print(f"[pauli-causal] Wrote causal backbone to {args.md_out.relative_to(root)}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
