#!/usr/bin/env python3
"""
⚖️ THE PAULI REPLACEMENT FRONTIER (Authority-Grounded)
Truth lives in Lean; structure lives in the graph.

This script identifies 'Replacement Frontier' candidates—theorems that claim
significant physical results but lack formal 'Causal Mass' in the ArangoDB DAG.

A theorem is a high-priority replacement candidate if:
1. It has High Symbolic Debt (complex hypotheses/name).
2. It has Low Causal Mass (zero or few downstream theorem dependents).
3. It is not an intentional Capstone (checked via Depth and @[capstone]).
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from collections import Counter, defaultdict
from dataclasses import asdict
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.decl_graph_support import GraphProfile, load_decl_graph
    from tools.pathing import repo_root
else:
    from tools.infra.decl_graph_support import GraphProfile, load_decl_graph
    from tools.pathing import repo_root

def calculate_replacement_priority(p: GraphProfile) -> float:
    # ⚖️ PAULI RULE: Priority = (Symbolic Debt + Fragility) / Causal Mass
    
    # Base debt from kind and role
    debt = 1.0
    if p.kind in ("theorem", "lemma"):
        debt += 2.0
    
    # Isolated theorems are high priority (they don't support anything)
    if p.structural_role == "isolated_theorem":
        debt += 10.0
    elif p.structural_role == "type_only_theorem":
        debt += 5.0
    
    # Capstone exemption: intentional endpoints have low replacement priority
    if p.structural_role == "capstone_endpoint" or p.rep_depth == 5:
        debt -= 8.0
        
    # Mass damping: things with massive downstream use are low priority for replacement
    mass = float(p.descendant_mass)
    damping = 1.0 + math.log1p(mass)
    
    # Linkage depth: deeper things are harder to replace, thus lower priority
    damping += 0.2 * float(p.depth)
    
    return round(debt / max(damping, 0.1), 3)

def main() -> int:
    ap = argparse.ArgumentParser(description="Pauli-Authority Replacement Frontier")
    ap.add_argument("--json-out", type=Path, default=repo_root() / "reports" / "dag" / "replacement-frontier.json")
    ap.add_argument("--md-out", type=Path, default=repo_root() / "reports" / "dag" / "replacement-frontier.md")
    ap.add_argument("--top", type=int, default=50)
    args = ap.parse_args()

    # 1. Load the ground truth from Pauli Authority
    print("[pauli-frontier] Loading truthful graph mass from Pauli Authority...")
    decl_key_to_full, profile_map = load_decl_graph(repo_root())
    
    if not profile_map:
        print("[pauli-frontier] ERROR: Pauli Authority is unreachable.")
        return 1

    candidates = []
    for name, p in profile_map.items():
        if p.kind not in ("theorem", "lemma"):
            continue
            
        priority = calculate_replacement_priority(p)
        if priority > 1.0:
            candidates.append({
                "name": name,
                "priority": priority,
                "file": p.file,
                "line": p.line,
                "role": p.structural_role,
                "mass": p.descendant_mass,
                "depth": p.depth
            })

    candidates.sort(key=lambda x: x["priority"], reverse=True)
    top = candidates[:args.top]

    # 2. Render the Report
    md_lines = [
        "# ⚖️ Pauli Authority Audit: Replacement Frontier",
        "",
        "> **Protocol:** Truth lives in Lean; structure lives in the graph.",
        "> **Metric:** High priority = Low Causal Mass / High Symbolic Debt.",
        "",
        "## 🛠️ High-Priority Replacements (Pruning Candidates)",
        "| Priority | Theorem | Causal Mass | Depth | Role | Location |",
        "| :---: | :--- | :---: | :---: | :--- | :--- |"
    ]
    
    for c in top:
        md_lines.append(
            f"| **{c['priority']:.3f}** | `{c['name']}` | {c['mass']} | {c['depth']} | `{c['role']}` | `{c['file']}:{c['line']}` |"
        )

    md_lines.extend([
        "",
        "## Interpretation",
        "",
        "- **Priority > 5.0:** Likely isolated 'Hallucinations' or legacy placeholders.",
        "- **Causal Mass:** Number of downstream theorems supported. Higher mass = safer theorem.",
        "- **Role:** Isolated theorems are the primary targets for consolidation or removal."
    ])

    args.md_out.write_text("\n".join(md_lines))
    args.json_out.write_text(json.dumps(candidates, indent=2))
    
    print(f"[pauli-frontier] Wrote truthful frontier to {args.md_out.relative_to(repo_root())}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
