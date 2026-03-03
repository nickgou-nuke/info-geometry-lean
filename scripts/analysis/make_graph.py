#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable

if __package__ is None or __package__ == "":
    # Support direct execution: `python3 scripts/analysis/make_graph.py ...`
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.pathing import normalize_user_path, default_docs_map_root
from tools.pathing import lean_root


def run_export(import_mods: str, out: Path, ns_prefix: str = "InfoGeometry") -> None:
    # invoke the Lean exporter via lake env lean --run
    cmd = [
        "lake",
        "env",
        "lean",
        "--run",
        "lean/InfoGeometry/GraphExport.lean",
        import_mods,
        str(out),
        ns_prefix,
    ]
    subprocess.run(cmd, check=True)


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _to_module_name(lean_dir: Path, file_path: Path) -> str:
    rel = file_path.relative_to(lean_dir).with_suffix("")
    return ".".join(rel.parts)


def _module_to_file_path(lean_dir: Path, module: str) -> Path | None:
    path = lean_dir / Path(*module.split(".")).with_suffix(".lean")
    return path if path.exists() else None


def discover_repo_modules(ns_prefix: str = "InfoGeometry") -> list[str]:
    lean_dir = lean_root()
    modules: set[str] = set()
    root_module = lean_dir / f"{ns_prefix}.lean"
    if root_module.exists():
        modules.add(ns_prefix)
    src_dir = lean_dir / ns_prefix
    if src_dir.exists():
        for path in sorted(src_dir.rglob("*.lean")):
            modules.add(_to_module_name(lean_dir, path))
    return sorted(m for m in modules if m == ns_prefix or m.startswith(f"{ns_prefix}."))


def _olean_path_for_module(module: str) -> Path:
    return Path(".lake/build/lib/lean") / Path(*module.split(".")).with_suffix(".olean")


def _build_root_target(ns_prefix: str) -> str | None:
    # Prefer the project library target when present; fall back to namespace root.
    candidates = [f"{ns_prefix}.Library", ns_prefix]
    for target in candidates:
        proc = subprocess.run(
            ["lake", "build", target],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if proc.returncode == 0:
            return target
    return None


def build_modules(
    modules: list[str], ns_prefix: str, probe_unresolved: bool = False
) -> tuple[list[str], list[str]]:
    """
    Buildability classification modes:
    - default: build root target once and classify by `.olean` presence.
    - probe mode: run targeted `lake build <module>` for every module.
    """
    buildable: list[str] = []
    skipped: list[str] = []

    if probe_unresolved:
        # Strict mode: probe every discovered module with `lake build <module>`.
        # This avoids stale `.olean` false positives when a module source changed
        # but is no longer pulled in by the root target.
        for i, mod in enumerate(modules, start=1):
            proc = subprocess.run(
                ["lake", "build", mod],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=False,
            )
            if proc.returncode == 0:
                buildable.append(mod)
            else:
                skipped.append(mod)
                print(
                    f"[make_graph] skipping non-buildable module "
                    f"{i}/{len(modules)} (probe): {mod}"
                )
    else:
        root_target = _build_root_target(ns_prefix)
        if root_target:
            print(f"[make_graph] built root target `{root_target}` for baseline buildability scan")
        else:
            print("[make_graph] root target build failed; falling back to per-module checks")

        unresolved: list[str] = []
        for mod in modules:
            if _olean_path_for_module(mod).exists():
                buildable.append(mod)
            else:
                unresolved.append(mod)

        skipped.extend(unresolved)
        if unresolved:
            print(
                "[make_graph] unresolved modules from root build classified as "
                f"non-buildable: {len(unresolved)} "
                "(use --probe-unresolved for per-module fallback checks)"
            )

    buildable = sorted(set(buildable))
    skipped = sorted(set(skipped))
    return buildable, skipped


def parse_project_imports(file_path: Path, ns_prefix: str) -> list[str]:
    imports: list[str] = []
    for raw in file_path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = raw.strip()
        if not line or line.startswith("--"):
            continue
        if not line.startswith("import "):
            continue
        rhs = line[len("import ") :]
        for tok in rhs.split():
            if tok == ns_prefix or tok.startswith(f"{ns_prefix}."):
                imports.append(tok)
    return imports


def _module_region(module: str, ns_prefix: str) -> str:
    if module == ns_prefix:
        return "Root"
    parts = module.split(".")
    if len(parts) >= 2 and parts[0] == ns_prefix:
        return parts[1]
    return "External"


def _undirected_components(
    modules: Iterable[str], edges: Iterable[tuple[str, str, str]]
) -> list[list[str]]:
    adj: dict[str, set[str]] = defaultdict(set)
    for m in modules:
        adj[m]
    for src, dst, _ in edges:
        adj[src].add(dst)
        adj[dst].add(src)
    unseen = set(adj)
    comps: list[list[str]] = []
    while unseen:
        start = min(unseen)
        stack = [start]
        comp: list[str] = []
        unseen.remove(start)
        while stack:
            cur = stack.pop()
            comp.append(cur)
            for nxt in sorted(adj[cur]):
                if nxt in unseen:
                    unseen.remove(nxt)
                    stack.append(nxt)
        comps.append(sorted(comp))
    comps.sort(key=lambda c: (-len(c), c[0]))
    return comps


def write_module_graph(
    module_list: list[str],
    buildable: list[str],
    skipped: list[str],
    out_path: Path,
    ns_prefix: str,
) -> None:
    lean_dir = lean_root()
    module_set = set(module_list)
    buildable_set = set(buildable)
    skipped_set = set(skipped)
    nodes: dict[str, dict[str, Any]] = {}
    edges: set[tuple[str, str, str]] = set()

    for mod in sorted(module_set):
        path = _module_to_file_path(lean_dir, mod)
        nodes[mod] = {
            "id": mod,
            "path": str(path) if path else None,
            "discovered": True,
            "buildable": mod in buildable_set,
            "region": _module_region(mod, ns_prefix),
        }
        if not path:
            continue
        for dep in parse_project_imports(path, ns_prefix):
            edges.add((mod, dep, "import"))
            if dep not in nodes:
                dep_path = _module_to_file_path(lean_dir, dep)
                nodes[dep] = {
                    "id": dep,
                    "path": str(dep_path) if dep_path else None,
                    "discovered": dep in module_set,
                    "buildable": dep in buildable_set if dep in module_set else None,
                    "region": _module_region(dep, ns_prefix),
                }

    node_rows = [nodes[k] for k in sorted(nodes)]
    edge_rows = [[u, v, kind] for (u, v, kind) in sorted(edges)]
    components = _undirected_components(sorted(nodes), edges)

    data: dict[str, Any] = {
        "schema": "infogeometry.module_graph.v1",
        "namespace": ns_prefix,
        "nodes": node_rows,
        "edges": edge_rows,
        "stats": {
            "discovered_modules": len(module_list),
            "nodes": len(node_rows),
            "edges": len(edge_rows),
            "buildable": len(buildable),
            "non_buildable": len(skipped_set),
            "components": len(components),
            "largest_component": len(components[0]) if components else 0,
        },
        "non_buildable_modules": sorted(skipped_set),
        "connected_components": components,
    }
    out_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(
        "[make_graph] exported module graph with "
        f"{len(node_rows)} nodes, {len(edge_rows)} import edges -> {out_path}"
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--modules",
        default=None,
        help="Comma-separated modules to load. Default: discover all modules under the namespace prefix.",
    )
    ap.add_argument("--ns", default="InfoGeometry", help="Namespace prefix to filter by")
    ap.add_argument("--out", default=None, help="Output JSON path")
    ap.add_argument(
        "--probe-unresolved",
        action="store_true",
        help="Attempt per-module `lake build` for all discovered modules (slower but robust).",
    )
    args = ap.parse_args()

    docs_root = default_docs_map_root()
    out_path = normalize_user_path(args.out, docs_root / "graph.json")

    modules_csv = args.modules
    if modules_csv is None:
        discovered = discover_repo_modules(args.ns)
        if not discovered:
            raise SystemExit(f"[make_graph] no modules found under namespace prefix '{args.ns}'")
        print(f"[make_graph] discovered {len(discovered)} modules under '{args.ns}'")
        module_list = discovered
    else:
        module_list = [m for m in modules_csv.split(",") if m]

    # Ensure all imports exist as olean before exporting.
    buildable, skipped = build_modules(module_list, args.ns, args.probe_unresolved)
    if not buildable:
        raise SystemExit("[make_graph] no buildable modules discovered")
    if skipped:
        print(f"[make_graph] excluded {len(skipped)} non-buildable modules")
    print(f"[make_graph] using {len(buildable)} buildable modules for export")

    run_export(",".join(buildable), out_path, args.ns)
    module_graph_path = out_path.with_name("module_graph.json")
    write_module_graph(module_list, buildable, skipped, module_graph_path, args.ns)

    # Report a quick summary of node/edge counts; attempt to parse the JSON
    try:
        data = load_json(out_path)
        nodes = data.get("nodes", [])
        edges = data.get("edges", [])
        edge_count = len(edges)
        # edges may be triples (from,to,kind) or pairs
        if edge_count > 0 and isinstance(edges[0], list) and len(edges[0]) == 3:
            kinds = {e[2] for e in edges}
            print(f"[make_graph] exported graph with {len(nodes)} nodes, {edge_count} edges (kinds={kinds})")
        else:
            print(f"[make_graph] exported graph with {len(nodes)} nodes, {edge_count} edges")
    except Exception:
        print(f"[make_graph] exported graph to {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
