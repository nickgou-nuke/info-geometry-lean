#!/usr/bin/env python3
"""
Bridge: join DumpLeanGraph syntax records (Layer 1) with
ExtractGraph environment records (Layer 2).

Produces enriched JSON with:
  - source positions (from syntax)
  - tactic/atom tokens (extracted from syntax atoms)
  - dependencies (from environment)
  - type signatures (from environment)

Usage:
  lake env lean --run tools/lean_graph/DumpLeanGraph.lean <files...> > syntax.jsonl
  lake env lean tools/ExtractGraph.lean   # -> proof_graph.json
  python3 tools/lean_graph/bridge_syntax_env.py syntax.jsonl proof_graph.json
"""

import json
import sys
from collections import defaultdict


def extract_atoms(syntax_node, found=None):
    """Recursively extract atom values from a syntax tree."""
    if found is None:
        found = set()
    if not isinstance(syntax_node, dict):
        return found
    kind = syntax_node.get("kind")
    if kind == "atom":
        val = syntax_node.get("value", "")
        if val:
            found.add(val)
    elif kind in ("node", "ident"):
        for child in syntax_node.get("children", []):
            extract_atoms(child, found)
    return found


def extract_syntax_kinds(syntax_node, found=None):
    """Recursively extract syntaxKind values from a syntax tree."""
    if found is None:
        found = set()
    if not isinstance(syntax_node, dict):
        return found
    sk = syntax_node.get("syntaxKind", "")
    if sk and sk != "null":
        found.add(sk)
    for child in syntax_node.get("children", []):
        extract_syntax_kinds(child, found)
    return found


def extract_proof_style(atoms, syntax_kinds):
    """Heuristic proof style classification based on atoms and syntaxKinds."""
    tactics = {"simp", "rw", "calc", "apply", "exact", "refine", "intro", "intros",
               "have", "rcases", "unfold", "dsimp", "noncomm_ring", "abel",
               "norm_num", "ext", "fin_cases", "native_decide", "nlinarith"}

    used_tactics = atoms & tactics
    has_by = "by" in atoms
    has_calc = "calc" in atoms
    has_match = "match" in atoms
    has_fun = "fun" in atoms

    # Check syntaxKinds for tactic blocks
    tactic_kinds = {k for k in syntax_kinds if "Tactic" in k or "tactic" in k}

    if tactic_kinds or used_tactics:
        return "tactic"
    elif has_calc:
        return "calc"
    elif has_match:
        return "pattern_match"
    elif has_fun:
        return "lambda"
    elif has_by:
        return "tactic"  # `by` implies tactic block
    else:
        return "term"  # direct term-style proof


def load_syntax(path):
    """Load JSONL syntax records, indexed by fully qualified name."""
    records = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            name = rec.get("name")
            if name:
                records[name] = rec
    return records


def load_env(path):
    """Load JSON environment records, indexed by name."""
    with open(path) as f:
        data = json.load(f)
    records = {}
    for rec in data:
        name = rec.get("name")
        if name:
            records[name] = rec
    return records


def bridge(syntax_records, env_records):
    """Join syntax + environment records by name."""
    bridged = []
    syntax_only = []
    env_only = []

    all_names = set(syntax_records.keys()) | set(env_records.keys())

    for name in sorted(all_names):
        syn = syntax_records.get(name)
        env = env_records.get(name)

        if syn and env:
            syntax_node = syn.get("syntax", {})
            atoms = extract_atoms(syntax_node)
            syntax_kinds = extract_syntax_kinds(syntax_node)
            proof_style = extract_proof_style(atoms, syntax_kinds)
            module = name.split(".")[0]
            src_range = syntax_node.get("range")
            syntax_kind = syntax_node.get("syntaxKind", "")

            bridged.append({
                "name": name,
                "kind": syn.get("keyword", env.get("kind", "unknown")),
                "module": module,
                "syntaxKind": syntax_kind,
                "proofStyle": proof_style,
                "atoms": sorted(atoms),
                "sourceRange": src_range,
                "type": env.get("type", ""),
                "hasValue": env.get("hasValue", False),
                "isUnsafe": env.get("isUnsafe", False),
                "isAxiom": env.get("isAxiom", False),
                "deps": env.get("deps", []),
            })
        elif syn and not env:
            syntax_only.append(name)
        elif env and not syn:
            env_only.append(name)

    return bridged, syntax_only, env_only


def main():
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <syntax.jsonl> <env.json>", file=sys.stderr)
        sys.exit(1)

    syntax_path = sys.argv[1]
    env_path = sys.argv[2]

    print(f"Loading syntax from {syntax_path}...", file=sys.stderr)
    syntax_records = load_syntax(syntax_path)

    print(f"Loading env from {env_path}...", file=sys.stderr)
    env_records = load_env(env_path)

    print(f"Bridging {len(syntax_records)} syntax + {len(env_records)} env records...",
          file=sys.stderr)

    bridged, syntax_only, env_only = bridge(syntax_records, env_records)

    # Output as JSON array
    json.dump(bridged, sys.stdout, indent=2)
    sys.stdout.write("\n")

    print(f"Bridged: {len(bridged)} records", file=sys.stderr)
    print(f"  Syntax-only (no env match): {len(syntax_only)}", file=sys.stderr)
    print(f"  Env-only (no syntax match): {len(env_only)}", file=sys.stderr)

    # Proof style statistics
    style_counts = defaultdict(int)
    for rec in bridged:
        style_counts[rec.get("proofStyle", "unknown")] += 1
    print("\nProof styles:", file=sys.stderr)
    for style, count in sorted(style_counts.items(), key=lambda x: -x[1]):
        print(f"  {style}: {count}", file=sys.stderr)

    # Atom statistics
    atom_counts = defaultdict(int)
    for rec in bridged:
        for a in rec.get("atoms", []):
            atom_counts[a] += 1
    print("\nTop atoms:", file=sys.stderr)
    for atom, count in sorted(atom_counts.items(), key=lambda x: -x[1])[:20]:
        print(f"  {atom}: {count}", file=sys.stderr)


if __name__ == "__main__":
    main()
