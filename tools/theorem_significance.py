#!/usr/bin/env python3
"""
⚖️ THE PAULI SIGNIFICANCE AUDITOR (graph-index grounded)
Truth lives in Lean; structure lives in the declaration graph.

This script replaces legacy lexical heuristics with graph-topology evidence
from local DAG index artifacts under artifacts/dag/index.
A theorem is considered significant if it has strong downstream support and depth.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from tools.infra.decl_graph_support import load_decl_graph
    from tools.pathing import repo_root
else:
    from tools.infra.decl_graph_support import load_decl_graph
    from tools.pathing import repo_root

def main() -> int:
    root = repo_root()
    
    # 1. Load graph evidence from local DAG index artifacts
    print("[pauli-audit] Loading graph evidence from local DAG index artifacts...")
    decl_key_to_full, profiles = load_decl_graph(root)
    
    if not profiles:
        print("[pauli-audit] ERROR: graph index is missing or empty.")
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
        # This is the number of theorems that formally depend on this vertex.
        mass = p.descendant_mass
        
        # SIGNANCE METRIC 2: Linkage Depth
        # How far from the L0 axioms is this theorem?
        depth = p.depth

        # JUDGMENT: Deep Identification
        # Theorems that are 'rfl' but have high depth and mass.
        # Legacy scripts flagged these as trivial; we flag them as milestones.
        if p.structural_role in ("supported_theorem", "load_bearing") and depth > 5:
            deep_identifications.append({
                "name": name,
                "mass": mass,
                "depth": depth,
                "role": p.structural_role
            })

        # JUDGMENT: Actual Vacuity
        # Only vacuous if it has ZERO mass, ZERO upstream support, AND is an isolated_theorem.
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
        "> **Snapshot:** {len(profiles)} declarations analysed via local DAG index artifacts.",
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
