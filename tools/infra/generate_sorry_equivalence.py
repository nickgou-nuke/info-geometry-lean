#!/usr/bin/env python3
"""
⚖️ THE PAULI VACUITY STRATIFIER (Authority-Grounded)
Truth lives in Lean; structure lives in the graph.

This script replaces legacy heuristics with formal topological stratification.
It classifies theorems into evidence-based risk classes using the Pauli Authority
(ArangoDB Live DAG or Local Artifacts).

Classes (from weakest to strongest graph integrity):

  isolated_theorem  — zero transitive downstream reach (confirmed by DAG)
  type_only_theorem — no value-position users (statement scaffolding)
  thin_forwarder    — belongs to a thin bridge in the formal topology
  supported_theorem — receives value-position downstream usage
  capstone_endpoint — deep theorems (Depth > 4) with zero users (intentional)
  load_bearing      — robust transitive reach and causal mass
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from dataclasses import asdict
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    # Insert repository root for `tools.*` imports when executed as a script.
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.decl_graph_support import GraphProfile, load_decl_graph
    from tools.pathing import repo_root
else:
    from tools.infra.decl_graph_support import GraphProfile, load_decl_graph
    from tools.pathing import repo_root

def generate_md(profiles: list[GraphProfile]) -> str:
    counts = Counter(p.structural_role for p in profiles)
    total = len(profiles)
    denom = max(total, 1)

    lines = [
        "# ⚖️ Pauli Authority Audit: Graph Vacuity Stratification",
        "",
        "> **Protocol:** Truth lives in Lean; structure lives in the graph.",
        f"> **Snapshot:** {total} theorems analysed via graph-topology evidence.",
        "> **Authority order:** Lean kernel truth > DAG topology > heuristic telemetry.",
        "",
        "## Classification Summary",
        "",
        "| Class | Count | % |",
        "| :--- | ---: | ---: |",
    ]
    
    roles = ["isolated_theorem", "type_only_theorem", "thin_forwarder", "supported_theorem", "capstone_endpoint", "load_bearing"]
    for role in roles:
        n = counts.get(role, 0)
        lines.append(f"| {role} | {n} | {100*n/denom:.1f}% |")

    weak = (
        counts.get("isolated_theorem", 0)
        + counts.get("type_only_theorem", 0)
        + counts.get("thin_forwarder", 0)
    )
    lines += [
        "",
        f"**Topology-weak surfaces (isolated + type-only + thin-forwarder):** {weak} ({100*weak/denom:.1f}%)",
        "",
        "## 🗑️ Isolated Theorems (Highest Pruning Priority)",
        "| Theorem | SCC Mass | Depth | File |",
        "| :--- | :---: | :---: | :--- |"
    ]
    
    isolated = sorted([p for p in profiles if p.structural_role == "isolated_theorem"], key=lambda x: (x.depth, x.name))
    for p in isolated[:30]:
        lines.append(f"| `{p.name}` | {p.descendant_mass} | {p.depth} | `{p.file}:{p.line}` |")

    lines += [
        "",
        "## 💎 Load-Bearing Spire (The Spire's Backbone)",
        "| Theorem | Downstream Mass | Transitive Reach | Depth |",
        "| :--- | :---: | :---: | :---: |"
    ]
    
    live = sorted([p for p in profiles if p.structural_role == "load_bearing"], key=lambda x: x.descendant_mass, reverse=True)
    for p in live[:30]:
        lines.append(f"| `{p.name}` | {p.descendant_mass} | {p.transitive_reverse_reach} | {p.depth} |")

    lines += [
        "",
        "## Interpretation",
        "",
        "- **isolated_theorem:** Zero transitive downstream reach. Formal vacuity confirmed.",
        "- **load_bearing:** High causal mass. Removal would collapse significant theory volume.",
        "- **capstone_endpoint:** Deep theorems (Depth > 4) with zero users. Intentional milestones.",
    ]

    return "\n".join(lines) + "\n"


def display_path(path: Path) -> str:
    root = repo_root()
    try:
        return str(path.resolve().relative_to(root))
    except ValueError:
        return str(path)

def main() -> int:
    ap = argparse.ArgumentParser(description="Graph vacuity stratification (topology-only)")
    ap.add_argument("--json-out", type=Path, default=repo_root() / "reports" / "dag" / "sorry-equivalence.json")
    ap.add_argument("--md-out", type=Path, default=repo_root() / "reports" / "dag" / "sorry-equivalence.md")
    args = ap.parse_args()

    # 1. Load the ground truth from Pauli Authority
    print("[pauli-vacuity] Loading truthful graph topology from Pauli Authority...")
    decl_key_to_full, profile_map = load_decl_graph(repo_root())
    
    if not profile_map:
        print("[pauli-vacuity] ERROR: Pauli Authority is unreachable or graph is empty.")
        return 1

    # Filter for theorems and lemmas only
    profiles = [p for p in profile_map.values() if p.kind in ("theorem", "lemma")]
    
    # 2. Write artifacts
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.md_out.parent.mkdir(parents=True, exist_ok=True)

    json_data: list[dict[str, Any]] = []
    for p in profiles:
        row = asdict(p)
        row["classification_basis"] = "graph-topology"
        row["authority_tier"] = "graph-structural"
        row["graph_grounded_signal"] = True
        row["heuristic_signal"] = False
        row["hard_verdict_allowed"] = True
        json_data.append(row)
    args.json_out.write_text(json.dumps(json_data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    args.md_out.write_text(generate_md(profiles), encoding="utf-8")

    # 3. Print Summary
    counts = Counter(p.structural_role for p in profiles)
    total = len(profiles)
    weak = (
        counts.get("isolated_theorem", 0)
        + counts.get("type_only_theorem", 0)
        + counts.get("thin_forwarder", 0)
    )
    denom = max(total, 1)
    
    print(f"[pauli-vacuity] {total} theorems analysed")
    print(f"[pauli-vacuity] topology-weak (isolated + type-only + thin-forwarder): {weak} ({100*weak/denom:.1f}%)")
    print(f"[pauli-vacuity] load-bearing (backbone): {counts.get('load_bearing', 0)} ({100*counts.get('load_bearing', 0)/denom:.1f}%)")
    print(f"[pauli-vacuity] wrote {display_path(args.md_out)}")
    print(f"[pauli-vacuity] wrote {display_path(args.json_out)}")
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
