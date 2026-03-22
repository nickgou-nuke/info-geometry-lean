#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict, deque
from pathlib import Path
from typing import Any


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def to_node_map(nodes: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    return {n["id"]: n for n in nodes if "id" in n}


def build_adjacency(edges: list[list[str]]) -> tuple[dict[str, list[str]], dict[str, list[str]]]:
    out: dict[str, list[str]] = defaultdict(list)
    undirected: dict[str, set[str]] = defaultdict(set)
    for e in edges:
        if len(e) < 2:
            continue
        src, dst = e[0], e[1]
        out[src].append(dst)
        undirected[src].add(dst)
        undirected[dst].add(src)
    out_sorted = {k: sorted(v) for k, v in out.items()}
    undirected_sorted = {k: sorted(v) for k, v in undirected.items()}
    return out_sorted, undirected_sorted


def dependency_closure(starts: list[str], out_adj: dict[str, list[str]]) -> set[str]:
    seen: set[str] = set()
    q: deque[str] = deque()
    for s in starts:
        if s and s not in seen:
            seen.add(s)
            q.append(s)
    while q:
        cur = q.popleft()
        for nxt in out_adj.get(cur, []):
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
    return seen


def shortest_path_undirected(
    start: str, target: str, undirected_adj: dict[str, list[str]]
) -> list[str] | None:
    if start == target:
        return [start]
    if start not in undirected_adj or target not in undirected_adj:
        return None
    q: deque[str] = deque([start])
    prev: dict[str, str | None] = {start: None}
    while q:
        cur = q.popleft()
        for nxt in undirected_adj.get(cur, []):
            if nxt in prev:
                continue
            prev[nxt] = cur
            if nxt == target:
                path = [target]
                while path[-1] is not None and prev[path[-1]] is not None:
                    path.append(prev[path[-1]])  # type: ignore[arg-type]
                path.reverse()
                return path
            q.append(nxt)
    return None


def region_of(module: str) -> str:
    if module == "InfoGeometry":
        return "Root"
    parts = module.split(".")
    if len(parts) >= 2 and parts[0] == "InfoGeometry":
        return parts[1]
    return "External"


def classify_error(errs: list[str]) -> str:
    text = " || ".join(errs)
    rules: list[tuple[str, str]] = [
        ("symbol-drift", r"Unknown constant|Unknown identifier"),
        ("missing-import-or-scope", r"unknown namespace"),
        ("syntax-or-notation-drift", r"invalid binder annotation|Function expected at|expected token|unexpected token|unexpected identifier"),
        ("proof-gap", r"unsolved goals|simp made no progress"),
        ("module-structure", r"invalid 'import' command"),
    ]
    for label, pat in rules:
        if re.search(pat, text):
            return label
    return "other"


def main() -> int:
    ap = argparse.ArgumentParser(description="Generate deterministic graph-driven refactor plan.")
    ap.add_argument(
        "--module-graph",
        default="docs-map/module_graph.json",
        help="Path to module graph JSON",
    )
    ap.add_argument(
        "--errors",
        default=".artifacts/nonbuildable_errors.json",
        help="Path to optional non-buildable diagnostics JSON",
    )
    ap.add_argument(
        "--out",
        default="docs-map/refactor_plan.md",
        help="Output markdown path",
    )
    ap.add_argument(
        "--rn-module",
        default="InfoGeometry.Assumptions.LLN",
        help="Module to treat as the Radon-Nikodym derivative anchor.",
    )
    ap.add_argument(
        "--potential-module",
        default="InfoGeometry.Potential.LogPotential",
        help="Module to treat as the generating-potential anchor.",
    )
    ap.add_argument(
        "--calabi-module",
        default="InfoGeometry.Canonical.CalabiYauBridge",
        help="Module to treat as the Calabi-Yau target anchor.",
    )
    ap.add_argument(
        "--compat-modules",
        default="InfoGeometry.SuperUnified,InfoGeometry.generalizedKL",
        help=(
            "Comma-separated compatibility alias modules to ignore in "
            "orphan-buildable classification."
        ),
    )
    args = ap.parse_args()

    module_graph_path = Path(args.module_graph)
    data = load_json(module_graph_path)
    nodes = to_node_map(data.get("nodes", []))
    edges = data.get("edges", [])
    out_adj, undirected_adj = build_adjacency(edges)
    modules = sorted(nodes)
    compat_modules = {m for m in args.compat_modules.split(",") if m}

    buildable = sorted(m for m in modules if nodes[m].get("buildable") is True)
    non_buildable = sorted(m for m in modules if nodes[m].get("buildable") is False)
    non_buildable_set = set(non_buildable)

    seeds = ["InfoGeometry", "InfoGeometry.Library", "InfoGeometry.Canonical.All"]
    present_seeds = [s for s in seeds if s in nodes]
    stable_closure = dependency_closure(present_seeds, out_adj)

    outside_canonical = [m for m in modules if m.startswith("InfoGeometry.") and ".Canonical." not in f".{m}."]
    orphan_buildable = sorted(
        m
        for m in outside_canonical
        if nodes[m].get("buildable") is True and m not in stable_closure and m not in compat_modules
    )
    compat_outside_closure = sorted(
        m
        for m in compat_modules
        if m in nodes and nodes[m].get("buildable") is True and m not in stable_closure
    )
    nonbuildable_nonarchive = sorted(
        m
        for m in non_buildable
        if not m.startswith("InfoGeometry.Archive.")
    )
    nonbuildable_archive = sorted(
        m
        for m in non_buildable
        if m.startswith("InfoGeometry.Archive.")
    )

    region_counts: dict[str, dict[str, int]] = defaultdict(lambda: {"total": 0, "buildable": 0, "non_buildable": 0})
    for m in modules:
        r = region_of(m)
        region_counts[r]["total"] += 1
        if nodes[m].get("buildable") is True:
            region_counts[r]["buildable"] += 1
        elif nodes[m].get("buildable") is False:
            region_counts[r]["non_buildable"] += 1

    short_name_buckets: dict[str, list[str]] = defaultdict(list)
    for m in modules:
        short_name_buckets[m.split(".")[-1]].append(m)
    duplicate_short_names = sorted(
        (k, sorted(v)) for k, v in short_name_buckets.items() if len(v) > 1
    )

    error_summary: dict[str, list[str]] = defaultdict(list)
    stale_error_modules: list[str] = []
    missing_error_modules: list[str] = []
    errors_path = Path(args.errors)
    if errors_path.exists():
        diag = load_json(errors_path)
        diag_modules = set(diag)
        for mod in sorted(diag_modules):
            if mod not in non_buildable_set:
                stale_error_modules.append(mod)
                continue
            category = classify_error(diag[mod].get("errors", []))
            error_summary[category].append(mod)
        missing_error_modules = sorted(non_buildable_set - diag_modules)

    rn_module = args.rn_module
    potential_module = args.potential_module
    calabi_module = args.calabi_module
    rn_to_potential = shortest_path_undirected(rn_module, potential_module, undirected_adj)
    potential_to_calabi = shortest_path_undirected(potential_module, calabi_module, undirected_adj)
    rn_to_calabi = shortest_path_undirected(rn_module, calabi_module, undirected_adj)

    out_lines: list[str] = []
    out_lines.append("# Graph-Driven Refactor Plan\n\n")
    out_lines.append("## Snapshot\n\n")
    out_lines.append(f"- Module graph: `{module_graph_path}`\n")
    out_lines.append(f"- Total modules in graph: **{len(modules)}**\n")
    out_lines.append(f"- Buildable modules: **{len(buildable)}**\n")
    out_lines.append(f"- Non-buildable modules: **{len(non_buildable)}**\n")
    out_lines.append(f"- Stable-closure size from `{', '.join(present_seeds)}`: **{len(stable_closure)}**\n\n")

    out_lines.append("## Region Health\n\n")
    out_lines.append("| Region | Total | Buildable | Non-buildable |\n")
    out_lines.append("|---|---:|---:|---:|\n")
    for region in sorted(region_counts):
        c = region_counts[region]
        out_lines.append(f"| {region} | {c['total']} | {c['buildable']} | {c['non_buildable']} |\n")
    out_lines.append("\n")

    out_lines.append("## Highest-Priority Repair Set (Non-Archive)\n\n")
    if nonbuildable_nonarchive:
        for m in nonbuildable_nonarchive:
            out_lines.append(f"- `{m}`\n")
    else:
        out_lines.append("- None\n")
    out_lines.append("\n")

    out_lines.append("## Archive Non-Buildable Set\n\n")
    if nonbuildable_archive:
        for m in nonbuildable_archive:
            out_lines.append(f"- `{m}`\n")
    else:
        out_lines.append("- None\n")
    out_lines.append("\n")

    out_lines.append("## Error Cause Buckets\n\n")
    if error_summary:
        for k in sorted(error_summary):
            out_lines.append(f"- `{k}`: {len(error_summary[k])}\n")
    elif non_buildable:
        out_lines.append("- No diagnostics available for current non-buildable modules.\n")
    else:
        out_lines.append("- No non-buildable modules in current graph.\n")
    if stale_error_modules:
        out_lines.append(f"- `stale-diagnostic-entries-ignored`: {len(stale_error_modules)}\n")
    if missing_error_modules:
        out_lines.append(f"- `non-buildable-modules-without-diagnostics`: {len(missing_error_modules)}\n")
    out_lines.append("\n")

    if stale_error_modules or missing_error_modules:
        out_lines.append("## Diagnostics Consistency\n\n")
        if stale_error_modules:
            out_lines.append(
                f"- Ignored **{len(stale_error_modules)}** stale diagnostics that no longer "
                "match current non-buildable modules.\n"
            )
            for m in stale_error_modules[:20]:
                out_lines.append(f"  - `{m}`\n")
            if len(stale_error_modules) > 20:
                out_lines.append(f"  - `...` ({len(stale_error_modules) - 20} more)\n")
        if missing_error_modules:
            out_lines.append(
                f"- Current non-buildable modules missing diagnostics: "
                f"**{len(missing_error_modules)}**\n"
            )
            for m in missing_error_modules[:20]:
                out_lines.append(f"  - `{m}`\n")
            if len(missing_error_modules) > 20:
                out_lines.append(f"  - `...` ({len(missing_error_modules) - 20} more)\n")
        out_lines.append("\n")

    out_lines.append("## Buildable Modules Outside Canonical and Outside Stable Closure\n\n")
    if orphan_buildable:
        for m in orphan_buildable:
            out_lines.append(f"- `{m}`\n")
    else:
        out_lines.append("- None\n")
    out_lines.append("\n")

    if compat_outside_closure:
        out_lines.append("## Compatibility Aliases Outside Stable Closure\n\n")
        for m in compat_outside_closure:
            out_lines.append(f"- `{m}`\n")
        out_lines.append("\n")

    out_lines.append("## Short-Name Duplicates (Potential De-dup Targets)\n\n")
    if duplicate_short_names:
        for short, mods in duplicate_short_names[:50]:
            out_lines.append(f"- `{short}`:\n")
            for m in mods:
                out_lines.append(f"  - `{m}`\n")
    else:
        out_lines.append("- None\n")
    out_lines.append("\n")

    out_lines.append("## Path Probe: RN -> Potential -> Calabi-Yau (Module Level)\n\n")
    for label, path in [
        (f"Radon-Nikodym anchor `{rn_module}` to potential anchor `{potential_module}`", rn_to_potential),
        (f"Potential anchor `{potential_module}` to Calabi-Yau anchor `{calabi_module}`", potential_to_calabi),
        (f"Radon-Nikodym anchor `{rn_module}` to Calabi-Yau anchor `{calabi_module}`", rn_to_calabi),
    ]:
        out_lines.append(f"- {label}: ")
        if path:
            out_lines.append("`" + " -> ".join(path) + "`\n")
        else:
            out_lines.append("no undirected path in current module graph\n")
    out_lines.append("\n")

    out_lines.append("## Refactor Phases\n\n")
    phases: list[str] = []
    if nonbuildable_nonarchive:
        phases.append("Repair syntax/import drift in the non-archive non-buildable set.")
    else:
        phases.append(
            "Keep non-archive modules green with CI `lake build` checks; treat new "
            "non-buildable modules as release blockers."
        )
    if orphan_buildable:
        phases.append(
            "Promote buildable orphan modules by creating canonical wrappers and adding "
            "explicit imports into `InfoGeometry.Canonical.Foundations` or domain umbrellas."
        )
    else:
        phases.append(
            "Maintain stable closure by importing newly promoted modules into canonical "
            "umbrellas as soon as they are intended to be public."
        )
    phases.append(
        "De-duplicate short-name collisions by selecting one canonical module path and "
        "leaving thin aliases in old paths."
    )
    phases.append(
        "Keep `Archive/Drafts` out of stable closure; salvage only declarations with "
        "complete proofs into canonical/domain modules."
    )
    phases.append(
        "Re-run `make_graph` and `refactor_plan` after each refactor slice to track convergence."
    )
    for i, phase in enumerate(phases, start=1):
        out_lines.append(f"{i}. {phase}\n")

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("".join(out_lines), encoding="utf-8")
    print(f"[refactor_plan] wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
