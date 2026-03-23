#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import (
        default_decl_structure_file,
        default_source_sink_bipartite_file,
        normalize_user_path,
        repo_root,
    )
else:
    from tools.pathing import (
        default_decl_structure_file,
        default_source_sink_bipartite_file,
        normalize_user_path,
        repo_root,
    )


DEFAULT_STRUCTURE = str(default_decl_structure_file().relative_to(repo_root()))
DEFAULT_BIPARTITE = str(default_source_sink_bipartite_file().relative_to(repo_root()))
DEFAULT_JSON_OUT = "reports/dag/structural-anti-bleed.json"
DEFAULT_MD_OUT = "reports/dag/structural-anti-bleed.md"


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Check pairwise anti-bleed directly on the native structural condensation DAG "
            "and the public source-sink bipartite correspondence artifact."
        )
    )
    ap.add_argument("--structure", default=DEFAULT_STRUCTURE)
    ap.add_argument("--bipartite", default=DEFAULT_BIPARTITE)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--top", type=int, default=25)
    return ap.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    return raw if isinstance(raw, dict) else {}


def ordered_unique(items: list[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        if not item or item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def component_repr(component_id: str, components_by_id: dict[str, dict[str, Any]]) -> str:
    row = components_by_id.get(component_id, {})
    return str(row.get("representative", component_id))


def sort_component_ids(component_ids: set[str], components_by_id: dict[str, dict[str, Any]]) -> list[str]:
    return sorted(component_ids, key=lambda cid: (component_repr(cid, components_by_id), cid))


def parse_structure(
    payload: dict[str, Any]
) -> tuple[dict[str, dict[str, Any]], dict[str, set[str]]]:
    components_by_id: dict[str, dict[str, Any]] = {}
    adj: dict[str, set[str]] = {}
    for row in payload.get("components", []):
        if not isinstance(row, dict):
            continue
        component_id = str(row.get("componentId", ""))
        if not component_id:
            continue
        components_by_id[component_id] = row
        adj[component_id] = {
            str(dep)
            for dep in row.get("dependencyComponentIds", [])
            if str(dep)
        }
    for component_id in list(components_by_id.keys()):
        adj.setdefault(component_id, set())
    return components_by_id, adj


def parse_bipartite(
    payload: dict[str, Any]
) -> tuple[
    dict[str, dict[str, Any]],
    dict[str, dict[str, Any]],
    dict[str, set[str]],
]:
    atomic_by_id: dict[str, dict[str, Any]] = {}
    for row in payload.get("atomic_nodes", []):
        if not isinstance(row, dict):
            continue
        atomic_id = str(row.get("atomic_id", ""))
        if atomic_id:
            atomic_by_id[atomic_id] = row

    hydrated_by_id: dict[str, dict[str, Any]] = {}
    for row in payload.get("hydrated_nodes", []):
        if not isinstance(row, dict):
            continue
        hydrated_id = str(row.get("hydrated_id", ""))
        if hydrated_id:
            hydrated_by_id[hydrated_id] = row

    support_atomic_ids: dict[str, set[str]] = defaultdict(set)
    for row in payload.get("incidence_edges", []):
        if not isinstance(row, dict):
            continue
        if str(row.get("role", "")) != "supports":
            continue
        if str(row.get("projection_kind", "")) != "node_support":
            continue
        atomic_id = str(row.get("atomic_id", ""))
        hydrated_id = str(row.get("hydrated_id", ""))
        if atomic_id and hydrated_id:
            support_atomic_ids[hydrated_id].add(atomic_id)

    support_components: dict[str, set[str]] = {}
    for hydrated_id, row in hydrated_by_id.items():
        native_components = {
            str(cid)
            for cid in row.get("native_component_ids", [])
            if str(cid)
        }
        if native_components:
            support_components[hydrated_id] = native_components
            continue

        via_atomic: set[str] = set()
        for atomic_id in support_atomic_ids.get(hydrated_id, set()):
            atomic_row = atomic_by_id.get(atomic_id, {})
            for cid in atomic_row.get("native_component_ids", []):
                if str(cid):
                    via_atomic.add(str(cid))
            scc_id = str(atomic_row.get("scc_id", ""))
            if scc_id:
                via_atomic.add(scc_id)
        support_components[hydrated_id] = via_atomic

    return atomic_by_id, hydrated_by_id, support_components


def closure_from_component(
    component_id: str,
    adj: dict[str, set[str]],
    memo: dict[str, set[str]],
) -> set[str]:
    cached = memo.get(component_id)
    if cached is not None:
        return cached

    seen: set[str] = set()
    stack = [component_id]
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        cached_current = memo.get(current)
        if cached_current is not None:
            seen.update(cached_current)
            continue
        for nxt in adj.get(current, ()):
            if nxt not in seen:
                stack.append(nxt)

    memo[component_id] = seen
    return seen


def downward_closure(
    component_ids: set[str],
    adj: dict[str, set[str]],
    memo: dict[str, set[str]],
) -> set[str]:
    out: set[str] = set()
    for component_id in component_ids:
        out.update(closure_from_component(component_id, adj, memo))
    return out


def shared_strict_dominator_ids(
    component_ids: set[str],
    components_by_id: dict[str, dict[str, Any]],
) -> list[str]:
    if not component_ids:
        return []
    dominator_sets: list[set[str]] = []
    for component_id in component_ids:
        row = components_by_id.get(component_id, {})
        dominator_sets.append({
            str(cid)
            for cid in row.get("strictDominatorComponentIds", [])
            if str(cid)
        })
    shared = dominator_sets[0].copy()
    for doms in dominator_sets[1:]:
        shared.intersection_update(doms)
    return sorted(shared)


def support_summary(
    component_ids: set[str],
    components_by_id: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    ordered_ids = sort_component_ids(component_ids, components_by_id)
    representatives = [component_repr(cid, components_by_id) for cid in ordered_ids]
    root_witnesses = ordered_unique([
        str(rep)
        for cid in ordered_ids
        for rep in components_by_id.get(cid, {}).get("canonicalRootWitness", [])
        if str(rep)
    ])
    shared_dom_ids = shared_strict_dominator_ids(component_ids, components_by_id)
    shared_dom_reps = [component_repr(cid, components_by_id) for cid in shared_dom_ids]
    return {
        "component_ids": ordered_ids,
        "representatives": representatives,
        "root_witnesses": root_witnesses,
        "shared_strict_dominator_component_ids": shared_dom_ids,
        "shared_strict_dominator_representatives": shared_dom_reps,
    }


def find_anchor_candidates(
    support_components: dict[str, set[str]],
    components_by_id: dict[str, dict[str, Any]],
    adj: dict[str, set[str]],
    memo: dict[str, set[str]],
    hydrated_by_id: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    strictly_safe: list[dict[str, Any]] = []
    anchored: list[dict[str, Any]] = []
    unanchored: list[dict[str, Any]] = []

    for hydrated_id in sorted(hydrated_by_id.keys()):
        module = str(hydrated_by_id[hydrated_id].get("module", hydrated_id))
        support = support_components.get(hydrated_id, set())
        ordered_support = sort_component_ids(support, components_by_id)

        if len(ordered_support) == 1:
            anchor = ordered_support[0]
            strictly_safe.append({
                "hydrated_id": hydrated_id,
                "module": module,
                "support_size": 1,
                "anchor_component_id": anchor,
                "anchor_representative": component_repr(anchor, components_by_id),
                "anchor_root_witness": components_by_id.get(anchor, {}).get("canonicalRootWitness", []),
            })
            continue

        anchors = [
            cid
            for cid in ordered_support
            if support.issubset(closure_from_component(cid, adj, memo))
        ]
        if len(anchors) == 1:
            anchor = anchors[0]
            anchored.append({
                "hydrated_id": hydrated_id,
                "module": module,
                "support_size": len(ordered_support),
                "anchor_component_id": anchor,
                "anchor_representative": component_repr(anchor, components_by_id),
                "anchor_root_witness": components_by_id.get(anchor, {}).get("canonicalRootWitness", []),
                "support_representatives": [component_repr(cid, components_by_id) for cid in ordered_support],
            })
        else:
            reason = "multiple native anchor components cover the full support" if len(anchors) > 1 else "no single native component covers the full support"
            unanchored.append({
                "hydrated_id": hydrated_id,
                "module": module,
                "support_size": len(ordered_support),
                "reason": reason,
                "anchor_candidates": anchors,
                "support_representatives": [component_repr(cid, components_by_id) for cid in ordered_support],
            })

    anchored.sort(key=lambda row: (-int(row["support_size"]), row["module"]))
    unanchored.sort(key=lambda row: (-int(row["support_size"]), row["module"]))
    return {
        "strictly_safe": strictly_safe,
        "anchored": anchored,
        "unanchored": unanchored,
    }


def pairwise_bleed_scan(
    support_components: dict[str, set[str]],
    hydrated_by_id: dict[str, dict[str, Any]],
    components_by_id: dict[str, dict[str, Any]],
    adj: dict[str, set[str]],
    memo: dict[str, set[str]],
) -> list[dict[str, Any]]:
    violations: list[dict[str, Any]] = []
    hydrated_ids = sorted(hydrated_by_id.keys())

    summaries = {
        hydrated_id: support_summary(support_components.get(hydrated_id, set()), components_by_id)
        for hydrated_id in hydrated_ids
    }

    for source_id in hydrated_ids:
        source_support = support_components.get(source_id, set())
        if not source_support:
            continue
        source_closure = downward_closure(source_support, adj, memo)
        source_summary = summaries[source_id]

        for target_id in hydrated_ids:
            if target_id == source_id:
                continue
            target_support = support_components.get(target_id, set())
            if not target_support:
                continue

            overlap = target_support & source_closure
            missing = target_support - source_closure
            if not overlap or not missing:
                continue

            target_summary = summaries[target_id]
            overlap_ids = sort_component_ids(overlap, components_by_id)
            missing_ids = sort_component_ids(missing, components_by_id)
            violations.append({
                "source_hydrated_id": source_id,
                "source_module": str(hydrated_by_id[source_id].get("module", source_id)),
                "target_hydrated_id": target_id,
                "target_module": str(hydrated_by_id[target_id].get("module", target_id)),
                "source_support_size": len(source_support),
                "target_support_size": len(target_support),
                "closure_size": len(source_closure),
                "source_support_component_ids": source_summary["component_ids"],
                "source_support_representatives": source_summary["representatives"],
                "source_shared_strict_dominator_component_ids": source_summary["shared_strict_dominator_component_ids"],
                "source_shared_strict_dominator_representatives": source_summary["shared_strict_dominator_representatives"],
                "source_root_witnesses": source_summary["root_witnesses"],
                "target_support_component_ids": target_summary["component_ids"],
                "target_support_representatives": target_summary["representatives"],
                "target_shared_strict_dominator_component_ids": target_summary["shared_strict_dominator_component_ids"],
                "target_shared_strict_dominator_representatives": target_summary["shared_strict_dominator_representatives"],
                "target_root_witnesses": target_summary["root_witnesses"],
                "overlap_component_ids": overlap_ids,
                "overlap_representatives": [component_repr(cid, components_by_id) for cid in overlap_ids],
                "missing_component_ids": missing_ids,
                "missing_representatives": [component_repr(cid, components_by_id) for cid in missing_ids],
                "overlap_count": len(overlap_ids),
                "missing_count": len(missing_ids),
            })

    violations.sort(
        key=lambda row: (
            -int(row["missing_count"]),
            -int(row["overlap_count"]),
            row["source_module"],
            row["target_module"],
        )
    )
    return violations


def summarize_violations(violations: list[dict[str, Any]]) -> dict[str, Any]:
    by_source: dict[str, dict[str, Any]] = defaultdict(
        lambda: {"target_count": 0, "total_missing": 0, "total_overlap": 0, "targets": []}
    )
    by_target: dict[str, dict[str, Any]] = defaultdict(
        lambda: {"source_count": 0, "total_missing": 0, "total_overlap": 0, "sources": []}
    )

    for row in violations:
        source_id = str(row["source_hydrated_id"])
        target_id = str(row["target_hydrated_id"])

        by_source[source_id]["target_count"] += 1
        by_source[source_id]["total_missing"] += int(row["missing_count"])
        by_source[source_id]["total_overlap"] += int(row["overlap_count"])
        by_source[source_id]["targets"].append({
            "target_hydrated_id": target_id,
            "target_module": row["target_module"],
            "missing_count": row["missing_count"],
            "overlap_count": row["overlap_count"],
        })

        by_target[target_id]["source_count"] += 1
        by_target[target_id]["total_missing"] += int(row["missing_count"])
        by_target[target_id]["total_overlap"] += int(row["overlap_count"])
        by_target[target_id]["sources"].append({
            "source_hydrated_id": source_id,
            "source_module": row["source_module"],
            "missing_count": row["missing_count"],
            "overlap_count": row["overlap_count"],
        })

    worst_sources = sorted(
        ({"hydrated_id": key, **value} for key, value in by_source.items()),
        key=lambda row: (-row["target_count"], -row["total_missing"], row["hydrated_id"]),
    )
    worst_targets = sorted(
        ({"hydrated_id": key, **value} for key, value in by_target.items()),
        key=lambda row: (-row["source_count"], -row["total_missing"], row["hydrated_id"]),
    )
    return {
        "worst_sources": worst_sources,
        "worst_targets": worst_targets,
    }


def render_markdown(
    structure_path: Path,
    bipartite_path: Path,
    anchor_report: dict[str, Any],
    violations: list[dict[str, Any]],
    summary: dict[str, Any],
    top: int,
) -> str:
    lines: list[str] = []
    lines.append("# Structural anti-bleed diagnostic")
    lines.append("")
    lines.append(f"- structure: `{structure_path}`")
    lines.append(f"- bipartite artifact: `{bipartite_path}`")
    lines.append("- model: native component support on the Lean-emitted condensation DAG")
    lines.append("- criterion: pairwise partial-support bleed")
    lines.append("")
    lines.append("## Anchor structure")
    lines.append(f"- strictly safe: **{len(anchor_report['strictly_safe'])}**")
    lines.append(f"- anchored: **{len(anchor_report['anchored'])}**")
    lines.append(f"- unanchored: **{len(anchor_report['unanchored'])}**")
    lines.append("")
    lines.append("## Pairwise bleed")
    lines.append(f"- violating pairs: **{len(violations)}**")
    lines.append(f"- leaking source carriers: **{len(summary['worst_sources'])}**")
    lines.append(f"- split target carriers: **{len(summary['worst_targets'])}**")
    lines.append("")
    lines.append("## Worst source carriers")
    for row in summary["worst_sources"][:top]:
        lines.append(
            f"- `{row['hydrated_id']}`: {row['target_count']} leaking targets, "
            f"total missing={row['total_missing']}, total overlap={row['total_overlap']}"
        )
    lines.append("")
    lines.append("## Worst target carriers")
    for row in summary["worst_targets"][:top]:
        lines.append(
            f"- `{row['hydrated_id']}`: {row['source_count']} leaking sources, "
            f"total missing={row['total_missing']}, total overlap={row['total_overlap']}"
        )
    lines.append("")
    lines.append("## Anchor candidates")
    for row in anchor_report["anchored"][:top]:
        lines.append(
            f"- `{row['module']}`: support={row['support_size']}, "
            f"anchor={row['anchor_representative']}"
        )
    lines.append("")
    lines.append("## Worst violating pairs")
    for row in violations[:top]:
        lines.append(
            f"- `{row['source_module']}` -> `{row['target_module']}`: "
            f"overlap={row['overlap_count']}, missing={row['missing_count']}"
        )
        if row["source_shared_strict_dominator_representatives"]:
            lines.append(
                f"  - source shared dominators: {', '.join(row['source_shared_strict_dominator_representatives'][:6])}"
            )
        if row["target_shared_strict_dominator_representatives"]:
            lines.append(
                f"  - target shared dominators: {', '.join(row['target_shared_strict_dominator_representatives'][:6])}"
            )
        if row["overlap_representatives"]:
            lines.append(
                f"  - overlap components: {', '.join(row['overlap_representatives'][:6])}"
            )
        if row["missing_representatives"]:
            lines.append(
                f"  - missing components: {', '.join(row['missing_representatives'][:6])}"
            )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    structure_path = normalize_user_path(args.structure, default_decl_structure_file())
    bipartite_path = normalize_user_path(args.bipartite, default_source_sink_bipartite_file())
    json_out = normalize_user_path(args.json_out, repo_root() / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, repo_root() / DEFAULT_MD_OUT)

    structure = load_json(structure_path)
    bipartite = load_json(bipartite_path)

    components_by_id, adj = parse_structure(structure)
    _, hydrated_by_id, support_components = parse_bipartite(bipartite)
    closure_memo: dict[str, set[str]] = {}

    anchor_report = find_anchor_candidates(
        support_components,
        components_by_id,
        adj,
        closure_memo,
        hydrated_by_id,
    )
    violations = pairwise_bleed_scan(
        support_components,
        hydrated_by_id,
        components_by_id,
        adj,
        closure_memo,
    )
    summary = summarize_violations(violations)

    payload = {
        "kind": "structural_anti_bleed_diagnostic",
        "structure_artifact": str(structure_path),
        "bipartite_artifact": str(bipartite_path),
        "component_count": len(components_by_id),
        "hydrated_node_count": len(hydrated_by_id),
        "anchor_analysis": anchor_report,
        "pairwise_bleed": {
            "violation_count": len(violations),
            "violations": violations,
            "summary": summary,
        },
    }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    md_out.write_text(
        render_markdown(
            structure_path,
            bipartite_path,
            anchor_report,
            violations,
            summary,
            args.top,
        ),
        encoding="utf-8",
    )

    print(f"[structural-anti-bleed] wrote {json_out}")
    print(f"[structural-anti-bleed] wrote {md_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
