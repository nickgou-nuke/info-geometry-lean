#!/usr/bin/env python3
"""
Closure Debt Auditor: Identifies unanchored Lean declarations, theory islands, and holes in the dependency graph.
UPGRADED: Uses ArangoDB Authority Bridge for zero-false-positive audit.
"""
import argparse
import json
import os
import re
import math
from pathlib import Path
from collections import defaultdict, deque
from tools.infra.pauli_authority_bridge import get_authority_data
from tools.infra.decl_graph_support import resolve_decl_full_name, GraphProfile

# --- Lean Declaration Parsing ---
LEAN_DECL_RE = re.compile(r"^\s*(theorem|def|lemma)\s+([A-Za-z0-9_']+)")

def parse_lean_decls(lean_root):
    decls = []
    for lean_file in Path(lean_root).rglob("*.lean"):
        if ".agents" in str(lean_file) or "lake-packages" in str(lean_file):
            continue
        ns = []
        with open(lean_file, encoding="utf-8") as f:
            for i, line in enumerate(f):
                clean = line.strip()
                if clean.startswith("namespace "):
                    ns.append(clean.split()[1])
                elif clean.startswith("end") and ns:
                    ns.pop()
                m = LEAN_DECL_RE.match(line)
                if m:
                    # We store name, file, and line for fuzzy matching
                    decls.append({
                        "name": m.group(2),
                        "file": str(lean_file),
                        "line": i + 1,
                        "kind": m.group(1)
                    })
    return decls

# --- ArangoDB Graph Analysis ---
def get_arango_edges():
    # We could extend pauli_authority_bridge to return edges, 
    # but for now we'll assume the local edges.jsonl is a good enough mirror 
    # IF the names match.
    # Actually, let's just use the ArangoDB authority for nodes and local for edges.
    pass

def find_theory_islands(anchored_names, edges):
    reverse_edges = defaultdict(set)
    for src, dsts in edges.items():
        for dst in dsts:
            reverse_edges[dst].add(src)

    visited = set()
    islands = []
    # We only care about islands among our anchored local declarations
    for decl in anchored_names:
        if decl not in visited:
            island = set()
            queue = deque([decl])
            while queue:
                node = queue.popleft()
                if node in visited:
                    continue
                visited.add(node)
                island.add(node)
                for neighbor in edges.get(node, []):
                    if neighbor not in visited:
                        queue.append(neighbor)
                for neighbor in reverse_edges.get(node, []):
                    if neighbor not in visited:
                        queue.append(neighbor)
            islands.append(island)
    return islands

def main():
    root = Path(os.getcwd())
    ap = argparse.ArgumentParser(description="Pauli Closure Debt Auditor")
    ap.add_argument("--lean-root", default="lean", help="Root directory of Lean source files")
    ap.add_argument("--out", default="reports/closure_debt_audit.md", help="Output Markdown report path")
    args = ap.parse_args()

    print("[pauli-auditor] Connecting to ArangoDB authority...")
    arango_data = get_authority_data(root)
    if not arango_data:
        print("[pauli-auditor] FAILED: ArangoDB unreachable. Falling back to local index is not supported for this high-fidelity audit.")
        return

    # Convert arango_data to GraphProfiles for resolve_decl_full_name
    profiles = {}
    for name, a in arango_data.items():
        # Normalize file path in profile
        f = a.get("file")
        if f:
            try: f = str(Path(f).resolve().relative_to(root))
            except ValueError: pass
        profiles[name] = GraphProfile(
            name=name, file=f, line=a.get("line"),
            kind=a.get("kind", ""), module=a.get("module", ""),
            reverse_theorem_users=a.get("rth", 0),
            reverse_value_users=a.get("rv", 0),
            reverse_type_users=a.get("rt", 0),
            reverse_public_fan_in=a.get("reverse_public_fan_in", 0),
            descendant_mass=a.get("descendant_mass", 0),
            transitive_reverse_reach=a.get("transitive_reverse_reach", 0),
            depth=a.get("depth", 0),
            scc_size=a.get("scc_size", 1),
            is_sink=a.get("is_sink", True),
            significance_present=a.get("significance_present", False),
            forward_value_theorems=(),
            forward_value_defs=(),
            graph_load_bearing_score=0.0,
            rep_layer=None, rep_depth=None,
            structural_role="unknown"
        )

    print(f"[pauli-auditor] Parsing local Lean declarations in {args.lean_root}...")
    local_decls = parse_lean_decls(args.lean_root)
    
    # ⚓ ANCHORING
    anchored_map = {} # local_idx -> full_name
    unanchored = []
    
    # Pre-build lookup for exact matches
    decl_key_to_full = {}
    for name, p in profiles.items():
        if p.file and p.line:
            leaf = name.rsplit(".", 1)[-1]
            decl_key_to_full[(p.file, p.line, leaf)] = name

    print(f"[pauli-auditor] Anchoring {len(local_decls)} declarations against ArangoDB...")
    for i, row in enumerate(local_decls):
        # Normalize row file
        row_rel_file = str(Path(row["file"]).resolve().relative_to(root))
        row_copy = {**row, "file": row_rel_file}
        
        full_name = resolve_decl_full_name(type('obj', (object,), row_copy), decl_key_to_full, profiles)
        if full_name:
            anchored_map[i] = full_name
        else:
            unanchored.append(row)

    # 🕸️ EDGES (from local mirror for now, as Arango edge fetch is heavy)
    edge_path = root / "artifacts/dag/index/edges.jsonl"
    edges = defaultdict(set)
    if edge_path.exists():
        print(f"[pauli-auditor] Loading local edges for island analysis...")
        with open(edge_path, encoding="utf-8") as f:
            for line in f:
                obj = json.loads(line)
                edges[obj["src"]].add(obj["dst"])

    anchored_names = set(anchored_map.values())
    islands = find_theory_islands(anchored_names, edges)
    
    # Filtering islands: an island is only "problematic" if it's small or disconnected from 'main'
    # For now, just report all disjoint components.
    
    with open(args.out, "w", encoding="utf-8") as out:
        out.write(f"# Pauli Closure Debt Audit\n\n")
        out.write(f"- Authority: `ArangoDB (Primary Authoritative Lane)`\n")
        out.write(f"- Declarations Audited: `{len(local_decls)}`\n")
        out.write(f"- Anchored: `{len(anchored_map)}`\n")
        out.write(f"- Unanchored (Closure Debt): `{len(unanchored)}`\n\n")
        
        out.write(f"## 🛑 Closure Debts (Unanchored Declarations)\n\n")
        if not unanchored:
            out.write("✨ No unanchored declarations found in local source.\n")
        else:
            out.write("| kind | name | location |\n")
            out.write("| --- | --- | --- |\n")
            for d in unanchored:
                out.write(f"| `{d['kind']}` | `{d['name']}` | `{d['file']}:{d['line']}` |\n")

        out.write(f"\n## 🏝️ Theory Islands (Disjoint Components)\n\n")
        # Filter for islands that are entirely within our local namespace to avoid reporting mathlib as islands
        local_islands = []
        for island in islands:
            if any(name.startswith("InfoGeometry") for name in island):
                local_islands.append(island)
        
        local_islands.sort(key=len, reverse=True)
        for i, island in enumerate(local_islands, 1):
            out.write(f"### Island {i} ({len(island)} decls)\n")
            # Only show first 10 decls to keep report sane
            sorted_island = sorted(list(island))
            for decl in sorted_island[:20]:
                out.write(f"  - `{decl}`\n")
            if len(sorted_island) > 20:
                out.write(f"  - ... and {len(sorted_island)-20} more\n")

    print(f"[pauli-auditor] Audit complete. High-fidelity report written to {args.out}")

if __name__ == "__main__":
    main()
