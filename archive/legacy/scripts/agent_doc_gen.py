#!/usr/bin/env python3
"""LEGACY compatibility generator for local declaration-neighborhood LaTeX stubs.

This script still depends on `tools.graph` and the older graph wrapper lane.
Prefer the authoritative blueprint workflow centered on `InfoGeometry.BlueprintTags`
and LeanArchitect outputs.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

if __package__ is None or __package__ == "":
    # Support direct execution: `python3 scripts/agent_doc_gen.py ...`
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from tools.graph import ProjectGraph


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate LaTeX for a Lean declaration and its dependencies."
    )
    parser.add_argument("decl", help="Full Lean declaration name (e.g., InfoGeometry.klDiv)")
    parser.add_argument("--depth", type=int, default=1, help="Dependency depth to include")
    parser.add_argument(
        "--out",
        help="Output .tex file name (written under blueprint/src/generated/)",
    )
    args = parser.parse_args()

    pg = ProjectGraph()
    if args.decl not in pg.g:
        print(f"Error: declaration '{args.decl}' not found in the graph.")
        return 1

    to_document = [args.decl]
    current_layer = [args.decl]
    for _ in range(max(0, args.depth)):
        next_layer: list[str] = []
        for node in sorted(current_layer):
            deps = pg.get_neighbors(node, direction="out")
            deps = [d for d in deps if not any(p in d for p in ["._", ".match_", ".proof_"])]
            next_layer.extend(sorted(deps))
        for node in next_layer:
            if node not in to_document:
                to_document.append(node)
        current_layer = next_layer

    lines = [f"% Documentation for {args.decl} and its dependencies\n\n"]
    for node in to_document:
        lines.append(f"\\subsection*{{{node}}}\n\n")
        lines.append(pg.generate_latex_stub(node))
        file_path = pg.get_file_path(node)
        if file_path:
            lines.append(f"% Source: {file_path}\n\n")

    content = "".join(lines)
    if args.out:
        out_path = Path("blueprint/src/generated") / args.out
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(content, encoding="utf-8")
        print(f"Wrote documentation to {out_path}")
    else:
        print(content)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
