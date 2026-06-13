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
import re
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.decl_graph_support import load_decl_graph
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.infra.decl_graph_support import load_decl_graph
    from tools.pathing import normalize_user_path, repo_root


DECLARATION_RE = re.compile(
    r"(?m)^\s*(def|theorem|lemma|structure|class|inductive|axiom|opaque|abbrev|instance)\b"
)

QUALIFIED_DECL_RE = re.compile(
    r"(?m)^\s*(def|theorem|lemma|structure|class|inductive|axiom|opaque|abbrev|instance)\s+InfoGeometry(\.|$)"
)

INFOGEOMETRY_NAMESPACE_RE = re.compile(r"(?m)^\s*namespace\s+InfoGeometry(\.|\b)")

DAG_EXCLUDED_PREFIXES = (
    "lean/InfoGeometry/External/",
)

DAG_DUPLICATE_OWNER_FILES = {
    # `InfoGeometry.Clifford.All` owns the anticommutator version; this sibling
    # exports the same public constant `InfoGeometry.Clifford.polarFromQuadratic`.
    "lean/InfoGeometry/Clifford/QuadraticPolarBridge.lean",
    # `InfoGeometry.Projective.All` owns `PolarConcrete`; these siblings export
    # the same public `ZornCell.polarZ3` surface.
    "lean/InfoGeometry/Projective/SplitOctonions/PolarIncidenceConcrete.lean",
    "lean/InfoGeometry/Projective/SplitOctonions/ProjectiveZornPolarIncidence.lean",
    # These are kept outside the DAG root because they duplicate Causal/Audit
    # owner declarations already imported through the stable DAG lane.
    "lean/InfoGeometry/Causal/Algebra.lean",
    "lean/InfoGeometry/Causal/TriFacetInstantiation.lean",
    # `InfoGeometry.Categorical.Gromov` owns this public Gromov declaration.
    "lean/InfoGeometry/Categorical/GromovPositiveCone.lean",
}


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if not depth and text.startswith("--", i):
            newline = text.find("\n", i)
            if newline == -1:
                break
            i = newline
            continue
        if not depth:
            out.append(text[i])
        i += 1
    return "".join(out)


def declaration_bearing_files(root: Path) -> set[str]:
    files: set[str] = set()
    for path in (root / "lean" / "InfoGeometry").rglob("*.lean"):
        rel = path.relative_to(root).as_posix()
        if rel in DAG_DUPLICATE_OWNER_FILES or rel.startswith(DAG_EXCLUDED_PREFIXES):
            continue
        text = strip_lean_comments(path.read_text(encoding="utf-8", errors="ignore"))
        if not DECLARATION_RE.search(text):
            continue
        if INFOGEOMETRY_NAMESPACE_RE.search(text) or QUALIFIED_DECL_RE.search(text):
            files.add(rel)
    return files


def indexed_files(root: Path, profiles: dict[str, Any]) -> set[str]:
    files: set[str] = set()
    info_root = (root / "lean" / "InfoGeometry").resolve()
    for profile in profiles.values():
        raw_file = getattr(profile, "file", None)
        if not raw_file:
            continue
        path = Path(str(raw_file))
        try:
            resolved = path.resolve() if path.is_absolute() else (root / path).resolve()
            if not resolved.is_file() or not resolved.is_relative_to(info_root):
                continue
            files.add(resolved.relative_to(root).as_posix())
        except (OSError, ValueError):
            continue
    return files


def graph_coverage(root: Path, profiles: dict[str, Any]) -> dict[str, Any]:
    repo_files = declaration_bearing_files(root)
    covered_files = indexed_files(root, profiles)
    missing = sorted(repo_files - covered_files)
    all_decl_files: set[str] = set()
    excluded_external: list[str] = []
    excluded_duplicate_owner: list[str] = []
    excluded_namespace_mismatch: list[str] = []
    for path in (root / "lean" / "InfoGeometry").rglob("*.lean"):
        rel = path.relative_to(root).as_posix()
        text = strip_lean_comments(path.read_text(encoding="utf-8", errors="ignore"))
        if not DECLARATION_RE.search(text):
            continue
        all_decl_files.add(rel)
        if rel.startswith(DAG_EXCLUDED_PREFIXES):
            excluded_external.append(rel)
        elif rel in DAG_DUPLICATE_OWNER_FILES:
            excluded_duplicate_owner.append(rel)
        elif rel not in repo_files and rel not in covered_files:
            excluded_namespace_mismatch.append(rel)
    import_only = sorted(
        path.relative_to(root).as_posix()
        for path in (root / "lean" / "InfoGeometry").rglob("*.lean")
        if path.relative_to(root).as_posix() not in all_decl_files
    )
    return {
        "repo_decl_files": len(repo_files),
        "decl_index_files": len(covered_files),
        "missing_decl_files_count": len(missing),
        "missing_decl_files": missing,
        "excluded_decl_files_count": (
            len(excluded_external) + len(excluded_duplicate_owner) + len(excluded_namespace_mismatch)
        ),
        "excluded_external_decl_files_count": len(excluded_external),
        "excluded_external_decl_files": sorted(excluded_external),
        "excluded_duplicate_owner_files_count": len(excluded_duplicate_owner),
        "excluded_duplicate_owner_files": sorted(excluded_duplicate_owner),
        "excluded_namespace_mismatch_files_count": len(excluded_namespace_mismatch),
        "excluded_namespace_mismatch_files": sorted(excluded_namespace_mismatch),
        "import_only_files_count": len(import_only),
        "import_only_files": import_only,
        "is_partial": bool(missing),
    }


def main() -> int:
    root = repo_root()

    ap = argparse.ArgumentParser(description="Pauli-Authority Causal Report")
    ap.add_argument("--md-out", type=Path, default=root / "reports" / "dag" / "true-root-order.md")
    ap.add_argument("--json-out", type=Path, default=root / "reports" / "dag" / "true-root-order.json")
    args = ap.parse_args()
    md_out = normalize_user_path(args.md_out, root / "reports" / "dag" / "true-root-order.md")
    json_out_path = normalize_user_path(args.json_out, root / "reports" / "dag" / "true-root-order.json")

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

    md_out.write_text("\n".join(md_lines))

    # Save formal JSON causal order together with the coverage payload consumed by doctor/status tools.
    causal_order = [
        {"name": p.name, "depth": p.depth, "mass": p.descendant_mass, "reach": p.transitive_reverse_reach}
        for p in backbone
    ]
    coverage = graph_coverage(root, profiles)
    json_out = {
        "summary": {
            "declaration_nodes": len(profiles),
            "backbone_nodes": len(backbone),
            "roots": len(foundations),
            "capstones": len(capstones),
            "graph_coverage": coverage,
        },
        "coverage": coverage,
        "causal_order": causal_order,
    }
    json_out_path.write_text(json.dumps(json_out, indent=2))

    print(f"[pauli-causal] Wrote causal backbone to {md_out.relative_to(root)}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
