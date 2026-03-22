#!/usr/bin/env python3
"""LEGACY bootstrap tool for annotating Lean source with `@[blueprint]` tags from `docs-map/graph.json`.

This script belongs to the older graph-only blueprint lane. The supported current
workflow is:
- `python3 tools/infra/refresh_decl_graph.py`
- `python3 tools/infra/refresh_blueprint_tags.py`
- `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprint`

Keep this script for archaeology or one-off conversions only. It can:
- select declarations from the graph (optionally by module prefix / component),
- resolve declarations to source files,
- insert inline `@[blueprint ...]` attributes at declaration positions,
- emit a JSON position map for frontend/indexing workflows.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

if __package__ is None or __package__ == "":
    # Support direct execution: `python3 scripts/graph_to_blueprint.py ...`
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from tools.pathing import default_docs_map_root, normalize_user_path, lean_root

_DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|axiom|inductive|structure|class)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)


def _normalize_graph_nodes(raw_nodes: list[Any]) -> list[str]:
    """Extract declaration/module ids from mixed graph node encodings."""
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
        return [x for x in component if isinstance(x, str)]
    if isinstance(component, dict):
        members = component.get("nodes", [])
        if isinstance(members, list):
            return [x for x in members if isinstance(x, str)]
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


def _ensure_declarations_json(path: Path, import_module: str, namespace: str) -> Path | None:
    if path.exists():
        return path
    path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        "lake",
        "env",
        "lean",
        "--run",
        "lean/DAG/ExportDecls.lean",
        import_module,
        namespace,
        str(path),
        namespace,
    ]
    print(f"[graph_to_blueprint] declarations map missing; generating via: {' '.join(cmd)}")
    try:
        subprocess.run(cmd, check=True)
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None
    return path


def _load_decl_module_map(declarations_path: Path) -> dict[str, str]:
    data = json.loads(declarations_path.read_text(encoding="utf-8"))
    raw = data["declarations"] if isinstance(data, dict) and "declarations" in data else data
    out: dict[str, str] = {}
    for d in raw:
        if isinstance(d, dict) and isinstance(d.get("name"), str):
            out[d["name"]] = str(d.get("module", ""))
    return out




def _infer_module_from_name(full_name: str) -> str:
    parts = full_name.split(".")
    root = lean_root()
    for i in range(len(parts) - 1, 0, -1):
        mod = ".".join(parts[:i])
        if (root / Path(*mod.split(".")).with_suffix(".lean")).exists():
            return mod
    return ""


def _build_decl_module_map(names: list[str], declarations_path: Path | None) -> tuple[dict[str, str], Counter]:
    stats = Counter()
    out: dict[str, str] = {}
    if declarations_path and declarations_path.exists():
        out.update(_load_decl_module_map(declarations_path))
        stats["module_map_from_declarations"] = len(out)
    for n in names:
        if n in out and out[n]:
            continue
        inferred = _infer_module_from_name(n)
        if inferred:
            out[n] = inferred
            stats["module_map_inferred"] += 1
    return out, stats


def _module_to_path(module: str) -> Path:
    return lean_root() / Path(*module.split(".")).with_suffix(".lean")


def _decl_token(full_name: str, module: str) -> str:
    if module and full_name.startswith(module + "."):
        return full_name[len(module) + 1 :]
    return full_name.split(".")[-1]


def _index_repo_decl_positions() -> dict[str, list[tuple[Path, int]]]:
    idx: dict[str, list[tuple[Path, int]]] = defaultdict(list)
    root = lean_root()
    for file_path in sorted(root.rglob("*.lean")):
        lines = file_path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            m = _DECL_RE.match(line)
            if m:
                idx[m.group("name")].append((file_path, i))
    return idx


def _is_already_blueprint(lines: list[str], decl_line: int) -> bool:
    j = decl_line - 1
    while j >= 0 and not lines[j].strip():
        j -= 1
    return j >= 0 and "@[blueprint" in lines[j]


def _resolve_target(
    full_name: str,
    token: str,
    module: str,
    index: dict[str, list[tuple[Path, int]]],
) -> tuple[Path, int] | None:
    candidates = [token, token.split(".")[-1], full_name]
    possible: list[tuple[Path, int]] = []
    for c in candidates:
        possible.extend(index.get(c, []))
    if not possible:
        return None

    # Strong preference: match inferred/module-mapped file.
    if module:
        module_path = _module_to_path(module)
        for p, line in possible:
            if p == module_path:
                return p, line

    # Otherwise use unique position if possible.
    unique = list(dict.fromkeys(possible))
    if len(unique) == 1:
        return unique[0]

    # Fallback to first stable entry.
    unique.sort(key=lambda t: (str(t[0]), t[1]))
    return unique[0]


def _insert_tags(
    targets: dict[Path, list[tuple[str, int]]],
    dry_run: bool,
    label_mode: str,
) -> tuple[dict[str, dict[str, Any]], Counter]:
    stats = Counter()
    positions: dict[str, dict[str, Any]] = {}

    for file_path, decls in sorted(targets.items()):
        if not file_path.exists():
            stats["missing_files"] += len(decls)
            continue
        lines = file_path.read_text(encoding="utf-8").splitlines()
        inserts: list[tuple[int, str, str]] = []

        seen_decl_lines: set[int] = set()
        for full_name, line_idx in sorted(decls, key=lambda t: t[1]):
            if line_idx in seen_decl_lines:
                stats["duplicate_line_target"] += 1
                continue
            seen_decl_lines.add(line_idx)
            if _is_already_blueprint(lines, line_idx):
                stats["already_tagged"] += 1
                positions[full_name] = {
                    "file": str(file_path),
                    "line": line_idx + 1,
                    "column": 1,
                    "status": "already_tagged",
                }
                continue
            label = full_name.replace(".", "_")
            attr = "@[blueprint]" if label_mode == "none" else f'@[blueprint "{label}"]'
            inserts.append((line_idx, full_name, attr))

        if inserts:
            inserts.sort(key=lambda t: t[0])
            offset = 0
            for line_idx, full_name, attr in inserts:
                at = line_idx + offset
                lines.insert(at, attr)
                positions[full_name] = {
                    "file": str(file_path),
                    "line": at + 1,
                    "column": 1,
                    "status": "inserted",
                }
                offset += 1
                stats["inserted"] += 1
            if not dry_run:
                file_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    return positions, stats


def _emit_blueprint_file(target: Path, module_name: str, names: list[str], source_graph: Path) -> None:
    lines: list[str] = [
        "import Architect",
        "",
        "/-!",
        "AUTO-GENERATED FILE. DO NOT EDIT BY HAND.",
        "",
        "Generated by scripts/graph_to_blueprint.py from a dependency graph.",
        f"Source graph: {source_graph}",
        "-/",
        "",
        f"namespace {module_name}",
        "",
        "-- auto-generated blueprint annotations",
    ]
    for name in names:
        lines.append(f"attribute [blueprint] {name}")
    lines += ["", f"end {module_name}", ""]
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("\n".join(lines), encoding="utf-8")

def main() -> int:
    ap = argparse.ArgumentParser(description="Add inline blueprint tags from graph.json")
    ap.add_argument("--graph", default=None, help="Path to graph.json (default docs-map/graph.json)")
    ap.add_argument("--modules", nargs="*", default=[], help="Only include nodes starting with these prefixes")
    ap.add_argument("--clusters", nargs="*", type=int, default=[], help="Only include selected connected-component indices")
    ap.add_argument("--declarations", default=None, help="Path to declarations.json with name/module metadata")
    ap.add_argument("--import-module", default="InfoGeometry", help="Import root used if declarations map must be generated")
    ap.add_argument("--namespace", default="InfoGeometry", help="Namespace prefix used if declarations map must be generated")
    ap.add_argument("--positions-out", default=None, help="JSON file to write declaration->position map")
    ap.add_argument("--label-mode", choices=["full", "none"], default="full", help="Use generated labels or bare @[blueprint]")
    ap.add_argument("--dry-run", action="store_true", help="Do not modify files; still compute/print stats")
    ap.add_argument("--target", default=None, help="Lean output path for a bulk attribute file")
    ap.add_argument(
        "--module",
        default="InfoGeometry.BlueprintTags",
        help="Namespace wrapper for generated output file",
    )
    args = ap.parse_args()

    docs_root = default_docs_map_root()
    graph_path = normalize_user_path(args.graph, docs_root / "graph.json")
    decls_default = docs_root / "declarations.json"
    declarations_path = normalize_user_path(args.declarations, decls_default)
    positions_out = normalize_user_path(args.positions_out, docs_root / "blueprint_positions.json")

    graph = _load_graph(graph_path)
    names, stats = _select_nodes(graph, args.modules, args.clusters)
    if not names:
        print("[graph_to_blueprint] no nodes selected, nothing to do")
        print(f"[graph_to_blueprint] stats: {dict(stats)}")
        return 0

    if args.target:
        target_path = normalize_user_path(args.target, Path(args.target))
        if args.dry_run:
            print(f"[graph_to_blueprint] would write {len(names)} attributes to {target_path}")
            print(f"[graph_to_blueprint] stats: {dict(stats)}")
            return 0
        _emit_blueprint_file(target_path, args.module, names, graph_path)
        print(f"[graph_to_blueprint] wrote {target_path} ({len(names)} attributes)")
        print(f"[graph_to_blueprint] stats: {dict(stats)}")
        return 0

    declarations_path = _ensure_declarations_json(declarations_path, args.import_module, args.namespace)
    decl_map, map_stats = _build_decl_module_map(names, declarations_path)
    stats.update(map_stats)

    decl_index = _index_repo_decl_positions()
    targets: dict[Path, list[tuple[str, int]]] = defaultdict(list)
    for full_name in names:
        mod = decl_map.get(full_name, "")
        token = _decl_token(full_name, mod)
        resolved = _resolve_target(full_name, token, mod, decl_index)
        if resolved is None:
            stats["position_not_found"] += 1
            continue
        file_path, line_idx = resolved
        targets[file_path].append((full_name, line_idx))

    positions, mutate_stats = _insert_tags(targets, args.dry_run, args.label_mode)
    stats.update(mutate_stats)

    unresolved = [n for n in names if n not in positions]
    payload = {
        "graph": str(graph_path),
        "count_requested": len(names),
        "count_positions": len(positions),
        "positions": positions,
        "unresolved": unresolved,
        "stats": dict(stats),
    }
    positions_out.parent.mkdir(parents=True, exist_ok=True)
    positions_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    action = "would modify" if args.dry_run else "modified"
    print(f"[graph_to_blueprint] {action} {stats.get('inserted', 0)} declarations")
    print(f"[graph_to_blueprint] positions written to {positions_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
