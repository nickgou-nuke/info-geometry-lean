#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from tools.pathing import default_docs_map_root, normalize_user_path
from scripts.utils import load_json




def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--resolved", default=None)
    ap.add_argument("--coverage", default=None)
    ap.add_argument("--out", default=None, help="Defaults to resolved.paths.markdownIndex")
    args = ap.parse_args()

    docs_root = default_docs_map_root()
    resolved_path = normalize_user_path(args.resolved, docs_root / "resolved.json")
    coverage_path = normalize_user_path(args.coverage, docs_root / "coverage.json")
    resolved = load_json(resolved_path)
    coverage = load_json(coverage_path)
    out_path = normalize_user_path(args.out or resolved["paths"]["markdownIndex"], docs_root / resolved["paths"]["markdownIndex"])
    out_path.parent.mkdir(parents=True, exist_ok=True)

    lines: list[str] = []
    lines.append(f"# {resolved['project']['name']} Documentation Crosswalk")
    lines.append("")
    lines.append("This file is generated. It maps thesis chapters/sections/nodes to compiled Lean declarations.")
    lines.append("")
    lines.append("## Coverage Summary")
    lines.append("")
    lines.append(f"- Total declarations: **{coverage['totalDeclarations']}**")
    lines.append(f"- Explicitly mapped declarations: **{coverage['explicitMappedDeclarations']}**")
    lines.append(f"- Auto-mapped coverage declarations: **{coverage['autoMappedDeclarations']}**")
    lines.append(f"- Total mapped declarations: **{coverage['mappedDeclarations']}**")
    lines.append(f"- Unmapped declarations: **{coverage['unmappedDeclarations']}**")
    lines.append(f"- Unresolved explicit nodes: **{coverage['unresolvedExplicitNodes']}**")
    lines.append("")

    if coverage["unresolvedNodes"]:
        lines.append("## Unresolved Explicit Nodes")
        lines.append("")
        for u in coverage["unresolvedNodes"]:
            lines.append(f"- `{u['label']}` ({u['chapter']}/{u['section']}): missing {', '.join(f'`{x}`' for x in u['missingLean'])}")
        lines.append("")

    for ch in resolved["chapters"]:
        ch_num = ch.get("number")
        heading = f"Chapter {ch_num}. {ch['title']}" if ch_num is not None else ch["title"]
        lines.append(f"## {heading}")
        lines.append("")
        lines.append("**Module prefixes**")
        for p in ch.get("modulePrefixes", []):
            lines.append(f"- `{p}`")
        lines.append("")

        for sec in ch.get("sections", []):
            lines.append(f"### {sec['title']}")
            lines.append("")
            for node in sec.get("nodes", []):
                lines.append(f"- **{node['label']}** — {node.get('title', '')}")
                if node.get("resolvedLean"):
                    for nm in node["resolvedLean"]:
                        lines.append(f"  - Lean: `{nm}`")
                else:
                    lines.append("  - Lean: *(unresolved)*")
                if node.get("resolvedModules"):
                    for mod in node["resolvedModules"]:
                        lines.append(f"  - Module: `{mod}`")
                if node.get("uses"):
                    lines.append(f"  - Uses: {', '.join(f'`{u}`' for u in node['uses'])}")
                if node.get("milestone"):
                    lines.append("  - Milestone: yes")
            lines.append("")

        auto_nodes = ch.get("autoNodes", [])
        if auto_nodes:
            lines.append(f"### Auto-generated coverage nodes ({len(auto_nodes)})")
            lines.append("")
            for n in auto_nodes:
                nm = n["resolvedLean"][0] if n.get("resolvedLean") else "(unresolved)"
                mod = n["resolvedModules"][0] if n.get("resolvedModules") else "(unknown)"
                lines.append(f"- `{nm}`  \\n  Module: `{mod}`")
            lines.append("")

    out_path.write_text("\n".join(lines), encoding="utf-8")
    print(f"[emit_markdown_index] wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())