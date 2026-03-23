#!/usr/bin/env python3
from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import default_source_sink_bipartite_file, repo_root
else:
    from tools.pathing import default_source_sink_bipartite_file, repo_root


@dataclass
class ModuleSummary:
    name: str
    source_file: str
    raw_blocks: int
    raw_decls: int
    raw_primary_blocks: int
    semantic_nodes: int
    semantic_edges: int
    semantic_skeleton_nodes: int
    top_hubs: list[str]


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def count_lean_files_and_loc(root: Path) -> tuple[int, int]:
    lean_dir = root / "lean"
    files = sorted(lean_dir.rglob("*.lean"))
    loc = 0
    for path in files:
        try:
            with path.open(encoding="utf-8") as handle:
                loc += sum(1 for _ in handle)
        except OSError:
            continue
    return len(files), loc


def summarize_module(path: Path) -> ModuleSummary:
    obj = load_json(path)
    source_file = str(obj.get("sourceFile", path.name))
    module_name = Path(source_file).stem
    skeleton = obj.get("skeleton", [])
    top_hubs: list[str] = []
    for entry in skeleton[:5]:
        produces = entry.get("primaryProduces", [])
        if produces:
            top_hubs.append(str(produces[0]))
        else:
            top_hubs.append(str(entry.get("stableId", "")))
    return ModuleSummary(
        name=module_name,
        source_file=source_file,
        raw_blocks=int(obj.get("rawBlocks", 0)),
        raw_decls=int(obj.get("rawDecls", 0)),
        raw_primary_blocks=int(obj.get("rawPrimaryBlocks", 0)),
        semantic_nodes=int(obj.get("semanticBlockNodes", 0)),
        semantic_edges=int(obj.get("semanticBlockEdges", 0)),
        semantic_skeleton_nodes=int(obj.get("semanticSkeletonNodes", 0)),
        top_hubs=top_hubs,
    )


def module_table_rows(summaries: list[ModuleSummary]) -> list[str]:
    rows = [
        "| Module | Semantic nodes | Semantic edges | Skeleton nodes | Top hubs |",
        "| :--- | ---: | ---: | ---: | :--- |",
    ]
    for s in summaries:
        hubs = ", ".join(f"`{h}`" for h in s.top_hubs[:3]) if s.top_hubs else "-"
        rows.append(
            f"| `{s.name}` | {s.semantic_nodes} | {s.semantic_edges} | {s.semantic_skeleton_nodes} | {hubs} |"
        )
    return rows


def seed_bridge_summary(kasparov_path: Path) -> tuple[str, list[str]]:
    obj = load_json(kasparov_path)
    for block in obj.get("blocks", []):
        produces = [str(x) for x in block.get("primaryProduces", [])]
        if "InfoGeometry.KK.KasparovCycle.analyticalIndex" in produces:
            deps = [str(x) for x in block.get("primaryDeps", [])]
            return str(block.get("stableId", "")), deps
    return "", []


def frontier_names(frontier_obj: dict[str, Any], limit: int = 6) -> list[str]:
    out: list[str] = []
    for row in frontier_obj.get("frontier", [])[:limit]:
        produces = row.get("primaryProduces", [])
        if produces:
            out.append(str(produces[0]))
        else:
            out.append(str(row.get("stableId", "")))
    return out


def burndown_names(burndown_obj: dict[str, Any], limit: int = 5) -> list[str]:
    out: list[str] = []
    for row in burndown_obj.get("rows", [])[:limit]:
        name = str(row.get("module", "")).strip()
        if name:
            out.append(name)
    return out


def compression_bundle_names(obj: dict[str, Any], limit: int = 4) -> list[str]:
    out: list[str] = []
    for row in obj.get("atomic_nodes", obj.get("bundles", []))[:limit]:
        bundle_id = str(row.get("bundle_id", "")).strip()
        motif = str(row.get("motif_signature", "")).strip()
        if bundle_id:
            out.append(f"{bundle_id}: {motif}" if motif else bundle_id)
    return out


def compression_module_names(obj: dict[str, Any], limit: int = 4) -> list[str]:
    out: list[str] = []
    for row in obj.get("hydrated_nodes", obj.get("hydrated_modules", []))[:limit]:
        module = str(row.get("module", "")).strip()
        if module:
            out.append(module)
    return out


def frontier_names_matching(frontier_obj: dict[str, Any], needle: str, limit: int = 4) -> list[str]:
    out: list[str] = []
    for row in frontier_obj.get("frontier", []):
        source_file = str(row.get("sourceFile", ""))
        if needle not in source_file:
            continue
        produces = row.get("primaryProduces", [])
        if produces:
            out.append(str(produces[0]))
        else:
            out.append(str(row.get("stableId", "")))
        if len(out) >= limit:
            break
    return out


def render_index(
    lean_files: int,
    lean_loc: int,
    summaries: list[ModuleSummary],
    both_frontier: dict[str, Any],
    reverse_frontier: dict[str, Any],
    frontier_burndown: dict[str, Any],
    source_sink_compression: dict[str, Any],
    seed_block: str,
    seed_deps: list[str],
) -> str:
    lines: list[str] = []
    lines.append("# InfoGeometry Auto Status")
    lines.append("")
    lines.append("Status:")
    lines.append("- generated from local repository state and trusted DAG artifacts")
    lines.append("- authoritative for current metrics/frontier snapshot")
    lines.append("- preferred refresh path: `python3 tools/docs/update_repo_docs.py`")
    lines.append("- low-level generator: `python3 tools/docs/generate_auto_docs.py`")
    lines.append("- declaration-level causal-order inputs live under `artifacts/dag/`; readable frontier/causal reports and NetworkX exports live under `reports/dag/`")
    lines.append("")
    lines.append("## Repository Scale")
    lines.append(f"- Lean files under `lean/`: **{lean_files}**")
    lines.append(f"- Lean LOC under `lean/`: **{lean_loc:,}**")
    lines.append("")
    lines.append("## Trusted Semantic Exports")
    lines.extend(module_table_rows(summaries))
    lines.append("")
    lines.append("## Verified Bridge Snapshot")
    lines.append(f"- seed declaration: `InfoGeometry.KK.KasparovCycle.analyticalIndex`")
    lines.append(f"- seed block: `{seed_block or 'missing'}`")
    if "InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex" in seed_deps:
        lines.append(
            "- direct hard dependency detected:"
            " `InfoGeometry.KK.KasparovCycle.analyticalIndex"
            " -> InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`"
        )
    else:
        lines.append("- direct KK -> AnalyticalIndex bridge dependency not detected in current local artifacts")
    lines.append("")
    lines.append("## Skynet v2 Frontier")
    lines.append(f"- graph nodes: **{both_frontier.get('nodeCount', 0)}**")
    lines.append(f"- graph edges: **{both_frontier.get('edgeCount', 0)}**")
    lines.append(f"- cross-module edges: **{both_frontier.get('crossModuleEdgesAdded', 0)}**")
    lines.append(f"- seed blocks: **{len(both_frontier.get('seedBlocks', []))}**")
    lines.append("")
    lines.append("### Local Bridge Kernel (`--walk both`)")
    for name in frontier_names(both_frontier):
        lines.append(f"- `{name}`")
    lines.append("")
    lines.append("### Downstream Consumer Frontier (`--walk reverse`)")
    for name in frontier_names(reverse_frontier):
        lines.append(f"- `{name}`")
    lines.append("")
    grand_synthesis_hits = frontier_names_matching(reverse_frontier, "GrandSynthesis.lean")
    if grand_synthesis_hits:
        lines.append("### First GrandSynthesis Consumer Hits")
        for name in grand_synthesis_hits:
            lines.append(f"- `{name}`")
        lines.append("")
    lines.append("## Frontier Burn-Down")
    lines.append("- weighted clean-up order for the current top frontier hotspot modules")
    for name in burndown_names(frontier_burndown):
        lines.append(f"- `{name}`")
    lines.append("")
    lines.append("## Source-Sink Compression")
    lines.append("- public bipartite incidence artifact between the atomic declaration DAG and the hydrated module graph")
    lines.append("- exposes canonical source bundles, repeated path motifs, and module-level compression carriers")
    for name in compression_bundle_names(source_sink_compression):
        lines.append(f"- source bundle `{name}`")
    for name in compression_module_names(source_sink_compression):
        lines.append(f"- hydrated carrier `{name}`")
    lines.append("")
    lines.append("## Current Reading Order")
    lines.append("1. `README.md`")
    lines.append("2. `lean/DAG/README.md`")
    lines.append("3. `tools/README.md`")
    lines.append("4. `skills/info-geometry-repo/references/frontier-prompt.md`")
    lines.append("5. `skills/info-geometry-repo/references/bridge-candidates.md`")
    lines.append("")
    lines.append("## Notes")
    lines.append("- This page is a generated status view, not a narrative design document.")
    lines.append("- Trusted declaration graph inputs for causal-order analysis live under `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl`.")
    lines.append("- Native Lean structural analysis now lives under `artifacts/dag/structural-topology.json` with stable condensation ids, membership, dominators, and canonical root-witness paths.")
    lines.append("- Public DAG artifacts now include `artifacts/dag/source-sink-bipartite.json` alongside `artifacts/dag/full_graph.json`, `artifacts/dag/index/decls.jsonl`, and `artifacts/dag/structural-topology.json`; readable projections live under `reports/dag/`, including `source-sink-compression.md`, `structural-anti-bleed.md`, `structural-dedup.md`, and `source-sink-incidence.{graphml,svg}`.")
    lines.append("- Treat causal-order rankings as provisional until `reports/dag/true-root-order.md` shows no coverage warning; the public `artifacts/dag/` graph may still be partial if `InfoGeometry.All` omits declaration-bearing branches.")
    lines.append("- Use `reports/dag/missing-all-classification.md` to classify the remaining declaration-bearing files outside `InfoGeometry.All` into direct imports, branch-façade expansions, namespace fixes, and noncanonical exclusions.")
    lines.append("- Generated semantic exports and derived frontier/causal JSONs under `reports/dag/` are intentionally untracked.")
    lines.append("- Historical crosswalk/intake documents may still exist, but this page reflects the current trusted bridge workflow.")
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    root = repo_root()
    reports = root / "reports" / "dag"
    docs_auto = root / "docs" / "auto"
    docs_auto.mkdir(parents=True, exist_ok=True)

    module_files = [
        reports / "KasparovCycle.semantic-block.stdlib.json",
        reports / "AnalyticalIndex.semantic-block.stdlib.json",
        reports / "OperatorAlgebraBridge.semantic-block.stdlib.json",
        reports / "GrandSynthesis.semantic-block.stdlib.json",
    ]
    both_frontier_path = reports / "skynet-v2-frontier.json"
    reverse_frontier_path = reports / "skynet-v2-frontier-reverse.json"
    frontier_burndown_path = reports / "frontier-burndown.json"
    source_sink_compression_path = default_source_sink_bipartite_file()

    missing = [
        str(p.relative_to(root))
        for p in module_files + [both_frontier_path, reverse_frontier_path, frontier_burndown_path, source_sink_compression_path]
        if not p.exists()
    ]
    if missing:
        raise SystemExit("missing required generated artifacts:\n" + "\n".join(f"- {m}" for m in missing))

    lean_files, lean_loc = count_lean_files_and_loc(root)
    summaries = [summarize_module(p) for p in module_files]
    both_frontier = load_json(both_frontier_path)
    reverse_frontier = load_json(reverse_frontier_path)
    frontier_burndown = load_json(frontier_burndown_path)
    source_sink_compression = load_json(source_sink_compression_path)
    seed_block, seed_deps = seed_bridge_summary(module_files[0])

    out = render_index(
        lean_files=lean_files,
        lean_loc=lean_loc,
        summaries=summaries,
        both_frontier=both_frontier,
        reverse_frontier=reverse_frontier,
        frontier_burndown=frontier_burndown,
        source_sink_compression=source_sink_compression,
        seed_block=seed_block,
        seed_deps=seed_deps,
    )
    out_path = docs_auto / "index.md"
    out_path.write_text(out, encoding="utf-8")
    print(f"[auto-docs] wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
