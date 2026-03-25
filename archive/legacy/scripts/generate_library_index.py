#!/usr/bin/env python3
"""LEGACY compatibility generator for the exhaustive LaTeX library index.

This script still depends on `tools.graph` and the older graph wrapper surface.
Prefer the dedicated `InfoGeometry.BlueprintTags` LeanArchitect lane for exact
formal extraction, with curated narrative assembled under `blueprint/README.md`.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

if __package__ is None or __package__ == "":
    # Support direct execution: `python3 scripts/generate_library_index.py`
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from tools.graph import ProjectGraph
from tools.pathing import default_docs_map_root, normalize_user_path


def module_region(mod: str) -> str:
    if mod == "InfoGeometry":
        return "Root"
    parts = mod.split(".")
    if len(parts) >= 2 and parts[0] == "InfoGeometry":
        return parts[1]
    return "Other"


def region_sort_key(region: str) -> tuple[int, str]:
    # Put canonical first; keep the rest deterministic.
    if region == "Canonical":
        return (0, region)
    if region == "Root":
        return (1, region)
    return (2, region)


def _load_module_graph(path: Path) -> dict[str, dict[str, Any]]:
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    out: dict[str, dict[str, Any]] = {}
    for node in data.get("nodes", []):
        if isinstance(node, dict) and "id" in node:
            out[str(node["id"])] = node
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--module-graph",
        default=None,
        help="Optional module graph JSON (default: docs-map/module_graph.json)",
    )
    args = ap.parse_args()

    docs_root = default_docs_map_root()
    module_graph_path = normalize_user_path(args.module_graph, docs_root / "module_graph.json")
    module_meta = _load_module_graph(module_graph_path)

    pg = ProjectGraph()
    clean_g = pg.filter_noise()

    modules: dict[str, list[str]] = defaultdict(list)
    for node in sorted(clean_g.nodes):
        mod = pg.get_module_of(node)
        if not mod or not mod.startswith("InfoGeometry"):
            continue
        if mod.endswith(".mk"):
            continue
        modules[mod].append(node)

    # Ensure all discovered modules from module_graph are indexed,
    # even if they currently have zero exported declaration nodes.
    for mod in module_meta:
        if mod == "InfoGeometry" or mod.startswith("InfoGeometry."):
            modules.setdefault(mod, [])

    region_to_modules: dict[str, list[str]] = defaultdict(list)
    for mod in sorted(modules):
        region_to_modules[module_region(mod)].append(mod)

    lines: list[str] = ["% AUTOMATICALLY GENERATED LIBRARY INDEX\n\n"]
    for region in sorted(region_to_modules, key=region_sort_key):
        lines.append(f"\\chapter{{{region} Modules}}\n\n")
        for mod in sorted(region_to_modules[region]):
            lines.append(f"\\section{{{mod}}}\n\n")
            meta = module_meta.get(mod, {})
            if "buildable" in meta:
                status = "yes" if meta.get("buildable") is True else "no"
                lines.append(f"\\noindent\\textbf{{Buildable}}: {status}\n\n")
            decls = sorted(modules[mod])
            if not decls:
                lines.append("\\noindent\\emph{No exported declarations in the current declaration graph.}\n\n")
                continue
            for decl in decls:
                short_name = decl.split(".")[-1]
                lines.append(f"\\subsection*{{{short_name}}}\n\n")
                lines.append(pg.generate_latex_stub(decl))
                lines.append("\n")

    out_path = Path("blueprint/src/generated/library_index.tex")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("".join(lines), encoding="utf-8")
    print(f"Generated library index at {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
