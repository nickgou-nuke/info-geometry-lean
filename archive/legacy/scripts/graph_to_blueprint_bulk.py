#!/usr/bin/env python3
"""LEGACY graph-only generator for bulk `[blueprint]` tags.

This script reads `docs-map/graph.json` from the older declaration-graph lane.
The supported current workflow is `tools/infra/refresh_blueprint_tags.py` backed by
`artifacts/dag/index/decls.jsonl` and the dedicated `InfoGeometry.BlueprintTags`
LeanArchitect surface. This file is kept for compatibility and archaeology.

This script optionally
filters declarations by module prefixes and/or connected-component membership,
and emits a Lean file containing `attribute [blueprint] ...` lines.

Unlike LaTeX-based conversion workflows, this is graph-only bootstrapping.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any
import sys

if __package__ is None or __package__ == "":
    # Support direct execution: `python3 scripts/docs/graph_to_blueprint.py ...`
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

if __package__ is None or __package__ == "":
    # Support direct execution: `python3 scripts/graph_to_blueprint.py ...`
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from tools.pathing import default_docs_map_root, default_blueprint_tags_file, normalize_user_path


def _normalize_graph_nodes(raw_nodes: list[Any]) -> list[str]:
    """Extract declaration ids from mixed graph node encodings."""
    out: list[str] = []
    for n in raw_nodes:
        if isinstance(n, str):
            out.append(n)
            continue
        if isinstance(n, dict):
            for key in ("name", "id"):
                if isinstance(n.get(key), str):
                    out.append(n[key])
                    break
    return out


def _component_node_names(component: Any) -> list[str]:
    if isinstance(component, list):
        return _normalize_graph_nodes(component)
    if isinstance(component, dict):
        members = component.get("nodes", [])
        if isinstance(members, list):
            return _normalize_graph_nodes(members)
    return []


def _load_graph(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _select_nodes(
    graph: dict[str, Any],
    modules: list[str],
    clusters: list[int],
) -> tuple[list[str], Counter]:
    stats = Counter()

    names = _normalize_graph_nodes(graph.get("nodes", []))
    stats["nodes_raw"] = len(names)

    if clusters:
        components = graph.get("connected_components", [])
        selected_from_components: set[str] = set()
        for index in clusters:
            if index < 0 or index >= len(components):
                stats["skip_missing_cluster"] += 1
                continue
            selected_from_components.update(_component_node_names(components[index]))
        names = [n for n in names if n in selected_from_components]
        stats["nodes_after_cluster_filter"] = len(names)

    if modules:
        names = [n for n in names if any(n.startswith(m) for m in modules)]
        stats["nodes_after_module_filter"] = len(names)

    names = sorted(set(names))
    stats["nodes_selected"] = len(names)
    return names, stats


def _decl_to_path_map(graph: dict[str, Any]) -> dict[str, str]:
    """Map decl identifiers to paths, indexing by both `id` and `name` when present."""
    out: dict[str, str] = {}
    for n in graph.get("nodes", []):
        if not isinstance(n, dict):
            continue
        path = n.get("path")
        if not isinstance(path, str):
            continue
        for k in ("id", "name"):
            v = n.get(k)
            if isinstance(v, str):
                out[v] = path
    return out


def _path_to_module(path_str: str) -> str | None:
    """Heuristic conversion: `Foo/Bar.lean` -> `Foo.Bar`."""
    p = Path(path_str)
    if p.suffix != ".lean":
        return None
    p = p.with_suffix("")
    # normalize ./Foo/Bar -> Foo/Bar
    parts = [x for x in p.parts if x not in (".", "")]
    if not parts:
        return None
    return ".".join(parts)


def _imports_for_decls(graph: dict[str, Any], decls: list[str]) -> list[str]:
    """Compute Lean imports so `attribute [blueprint] decl` resolves."""
    decl2path = _decl_to_path_map(graph)
    imports: set[str] = set()

    for d in decls:
        path_str = decl2path.get(d)
        if path_str:
            m = _path_to_module(path_str)
            if m:
                imports.add(m)
                continue
        # fallback: guess module is prefix before last dot
        if "." in d:
            imports.add(d.rsplit(".", 1)[0])

    return sorted(imports)


def _emit_blueprint_file(
    target: Path,
    namespace_name: str,
    names: list[str],
    source_graph: Path,
    graph: dict[str, Any],
) -> None:
    imports = _imports_for_decls(graph, names)

    lines: list[str] = [
        "import Architect",
    ]
    for m in imports:
        lines.append(f"import {m}")

    lines += [
        "",
        "/-!",
        "AUTO-GENERATED FILE. DO NOT EDIT BY HAND.",
        "",
        "Generated by scripts/graph_to_blueprint.py from a dependency graph.",
        f"Source graph: {source_graph}",
        "-/",
        "",
    ]
    lines += [f"namespace {namespace_name}", "", "-- auto-generated blueprint annotations"]
    for name in names:
        lines.append(f"attribute [blueprint] {name}")
    lines += ["", f"end {namespace_name}", ""]

    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("\n".join(lines), encoding="utf-8")


def _apply_patch(graph: dict[str, Any], names: list[str], out_root: str | None) -> None:
    """Copy and patch original Lean sources for selected declarations.

    We append `attribute [blueprint] ...` at the end of each file, so the
    declaration is already defined (Lean requires the constant to exist).
    """
    from tools import pathing

    repo = pathing.repo_root()
    decl2path = _decl_to_path_map(graph)

    # group decls by source file
    file_to_decls: dict[Path, list[str]] = {}
    for decl in names:
        path_str = decl2path.get(decl)
        if not path_str:
            print(f"[graph_to_blueprint] warning: no path for {decl}, skipping")
            continue
        src = Path(path_str)
        if not src.is_absolute():
            src = repo / src
        file_to_decls.setdefault(src, []).append(decl)

    def ensure_architect_import(lines: list[str]) -> None:
        if any(l.strip().startswith("import Architect") for l in lines):
            return
        idx = 0
        for i, l in enumerate(lines):
            if l.strip().startswith(("import ", "public import")):
                idx = i + 1
        lines.insert(idx, "import Architect\n")

    for src, decls in file_to_decls.items():
        if not src.exists():
            print(f"[graph_to_blueprint] warning: file {src} does not exist, skipping")
            continue

        text = src.read_text(encoding="utf-8")
        lines = text.splitlines(keepends=True)
        ensure_architect_import(lines)

        # append a block at end, idempotently
        existing = set(lines)
        block: list[str] = ["\n-- auto-generated blueprint annotations\n"]
        for d in sorted(set(decls)):
            attr = f"attribute [blueprint] {d}\n"
            if attr not in existing:
                block.append(attr)

        if len(block) > 1:
            if not lines or not lines[-1].endswith("\n"):
                lines.append("\n")
            lines.extend(block)

        if out_root:
            dest = Path(out_root) / src.relative_to(repo)
            dest.parent.mkdir(parents=True, exist_ok=True)
        else:
            dest = src

        dest.write_text("".join(lines), encoding="utf-8")
        print(f"[graph_to_blueprint] patched {dest} ({len(set(decls))} decls)")


def main() -> int:
    ap = argparse.ArgumentParser(description="Generate blueprint tags from graph.json")
    ap.add_argument("--graph", default=None, help="Path to graph.json (default docs-map/graph.json)")
    ap.add_argument("--modules", nargs="*", default=[], help="Only include nodes starting with these prefixes")
    ap.add_argument(
        "--clusters",
        nargs="*",
        type=int,
        default=[],
        help="Only include nodes in selected connected-component indices",
    )
    ap.add_argument("--target", default=None, help="Lean output path")
    ap.add_argument(
        "--module",
        default="InfoGeometry.BlueprintTags",
        help="Namespace wrapper for generated output file (not a Lean `module` command)",
    )
    ap.add_argument("--dry-run", action="store_true", help="Print summary only; do not write output")
    ap.add_argument(
        "--patch",
        action="store_true",
        help="Modify Lean source files (copying them under --out-root if given) by appending attributes",
    )
    ap.add_argument(
        "--out-root",
        default=None,
        help="Directory under which patched Lean files will be written. Defaults to in-place when --patch is set.",
    )

    args = ap.parse_args()

    docs_root = default_docs_map_root()
    graph_path = normalize_user_path(args.graph, docs_root / "graph.json")
    target_path = normalize_user_path(args.target, default_blueprint_tags_file())

    graph = _load_graph(graph_path)
    names, stats = _select_nodes(graph, args.modules, args.clusters)

    if not names:
        print("[graph_to_blueprint] no nodes selected, nothing to write")
        print(f"[graph_to_blueprint] stats: {dict(stats)}")
        return 0

    if args.dry_run:
        if args.patch:
            print(f"[graph_to_blueprint] would patch {len(names)} declarations")
        else:
            print(f"[graph_to_blueprint] would write {len(names)} attributes to {target_path}")
        print(f"[graph_to_blueprint] stats: {dict(stats)}")
        return 0

    if args.patch:
        _apply_patch(graph, names, args.out_root)
    else:
        _emit_blueprint_file(target_path, args.module, names, graph_path, graph)
        print(f"[graph_to_blueprint] wrote {target_path} ({len(names)} attributes)")

    print(f"[graph_to_blueprint] stats: {dict(stats)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
