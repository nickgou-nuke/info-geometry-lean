#!/usr/bin/env python3
"""
⚖️ THE PAULI SIGNIFICANCE AUDITOR (Authority-Grounded)
Truth lives in Lean; structure lives in the graph.

This script replaces legacy lexical heuristics with formal topological evidence.
A theorem is considered significant if it possesses 'Causal Mass'—defined by
transitive downstream support and depth in the formal dependency DAG.
"""

from __future__ import annotations

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
    
    # 1. Load the ground truth from Pauli Authority (ArangoDB or local artifacts)
    print("[pauli-audit] Loading truthful graph mass from Pauli Authority...")
    decl_key_to_full, profiles = load_decl_graph(root)
    
    if not profiles:
        print("[pauli-audit] ERROR: Pauli Authority is unreachable or graph is empty.")
        return 1

    print(f"[pauli-audit] Analysing {len(profiles)} declarations for formal significance...")

    significant: list[dict] = []
    vacuous: list[dict] = []
    deep_identifications: list[dict] = []

    for name, p in profiles.items():
        # Heuristic exclusion: noise labels (match_, proof_, etc)
        if any(x in name for x in [".match_", ".proof_", "._"]):
            continue

        # SIGNANCE METRIC 1: Causal Mass (Transitive Downstream Support)
        mass = p.descendant_mass
        
        # SIGNANCE METRIC 2: Linkage Depth
        depth = p.depth

        # JUDGMENT: Deep Identification
        if p.structural_role in ("supported_theorem", "load_bearing") and depth > 5:
            deep_identifications.append({
                "name": name,
                "mass": mass,
                "depth": depth,
                "role": p.structural_role
            })

        # JUDGMENT: Actual Vacuity
        if mass == 0 and p.reverse_value_users == 0 and p.structural_role == "isolated_theorem":
            vacuous.append({
                "name": name,
                "file": p.file,
                "line": p.line
            })
        elif mass > 10 or p.reverse_public_fan_in > 5:
            significant.append({
                "name": name,
                "mass": mass,
                "depth": depth,
                "fan_in": p.reverse_public_fan_in
            })

    # 2. Render the Truthful Verdict
    md_lines = [
        "# ⚖️ Pauli Authority Audit: Truthful Significance Index",
        "",
        "> **Protocol:** Truth lives in Lean; structure lives in the graph.",
        f"> **Snapshot:** {len(profiles)} declarations analysed via Pauli Authority.",
        "",
        "## 💎 High Causal Mass (The Spire's Pillars)",
        "| Declaration | Causal Mass | Depth | Fan-In |",
        "| :--- | :---: | :---: | :---: |"
    ]
    
    significant.sort(key=lambda x: x["mass"], reverse=True)
    for s in significant[:50]:
        md_lines.append(f"| `{s['name']}` | {s['mass']} | {s['depth']} | {s['fan_in']} |")

    md_lines.extend([
        "",
        "## 🧬 Deep Identifications (Algebraic Unifications)",
        "| Milestone | Mass | Depth |",
        "| :--- | :---: | :---: |"
    ])
    
    deep_identifications.sort(key=lambda x: x["depth"], reverse=True)
    for d in deep_identifications[:20]:
        md_lines.append(f"| `{d['name']}` | {d['mass']} | {d['depth']} |")

    md_lines.extend([
        "",
        "## 🗑️ Confirmed Vacuity (Pruning Candidates)",
        "| Vacuous Declaration | Location |",
        "| :--- | :--- |"
    ])
    
    for v in vacuous[:30]:
        md_lines.append(f"| `{v['name']}` | `{v['file']}:{v['line']}` |")

    report_path = root / "reports" / "theorem-significance.md"
    report_path.write_text("\n".join(md_lines))
    
    print(f"[pauli-audit] Formal audit complete. Wrote {report_path.relative_to(root)}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
