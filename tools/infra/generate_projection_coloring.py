#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import default_source_sink_bipartite_file, normalize_user_path, repo_root
else:
    from tools.pathing import default_source_sink_bipartite_file, normalize_user_path, repo_root


DEFAULT_BIPARTITE = str(default_source_sink_bipartite_file().relative_to(repo_root()))
DEFAULT_FIBERS = "reports/dag/structural-fibers.json"
DEFAULT_QUOTIENT = "reports/dag/semantic-quotient.json"
DEFAULT_JSON_OUT = "reports/dag/projection-coloring.json"
DEFAULT_MD_OUT = "reports/dag/projection-coloring.md"


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Cluster the lower constructive side of the maintained source-sink graph and project "
            "those cluster colors upward onto module carriers and sink families."
        )
    )
    ap.add_argument("--bipartite", default=DEFAULT_BIPARTITE)
    ap.add_argument("--fibers", default=DEFAULT_FIBERS)
    ap.add_argument("--quotient", default=DEFAULT_QUOTIENT)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--cluster-threshold", type=float, default=0.8)
    ap.add_argument("--top", type=int, default=20)
    return ap.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    return raw if isinstance(raw, dict) else {}


def ordered_unique(items: list[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        text = str(item).strip()
        if not text or text in seen:
            continue
        seen.add(text)
        out.append(text)
    return out


def parse_module_list(value: Any) -> list[str]:
    if isinstance(value, list):
        return ordered_unique([str(x) for x in value])
    text = str(value or "").strip()
    if not text:
        return []
    return ordered_unique([chunk.strip() for chunk in text.split(",") if chunk.strip()])


def safe_float(value: Any) -> float:
    try:
        return float(value)
    except Exception:
        return 0.0


def short_name(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def md_table(headers: list[str], rows: list[list[str]]) -> str:
    out = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join(["---"] * len(headers)) + " |",
    ]
    for row in rows:
        out.append("| " + " | ".join(row) + " |")
    return "\n".join(out)


def stable_cluster_id(members: list[str]) -> str:
    digest = hashlib.sha1("||".join(sorted(members)).encode("utf-8")).hexdigest()[:10]
    return f"cluster:{digest}"


def edge_mass(row: dict[str, Any]) -> float:
    compression = safe_float(row.get("compression_potential"))
    path_count = int(row.get("path_count", 0) or 0)
    if compression > 0:
        return compression + 0.5 * path_count
    if path_count > 0:
        return float(path_count)
    return 1.0


def incidence_mass(row: dict[str, Any]) -> float:
    compression = safe_float(row.get("compression_potential"))
    if compression > 0:
        return compression
    score = safe_float(row.get("source_score"))
    if score > 0:
        return score
    path_len = int(row.get("path_length", 0) or 0)
    return max(1.0, float(path_len))


def add_affinity(
    affinity: dict[tuple[str, str], float],
    reasons: dict[tuple[str, str], Counter[str]],
    a: str,
    b: str,
    weight: float,
    reason: str,
) -> None:
    if not a or not b or a == b or weight <= 0:
        return
    key = (a, b) if a < b else (b, a)
    affinity[key] = affinity.get(key, 0.0) + weight
    reasons[key][reason] += 1


def classify_projection(cluster_weights: dict[str, float]) -> tuple[str, float, str]:
    total = sum(cluster_weights.values())
    if total <= 0 or not cluster_weights:
        return "inactive", 0.0, ""
    top_cluster, top_mass = max(cluster_weights.items(), key=lambda item: (item[1], item[0]))
    share = top_mass / total
    cluster_count = len(cluster_weights)
    if cluster_count == 1 or share >= 0.85:
        label = "monochrome"
    elif share >= 0.6:
        label = "dominant_mixed"
    else:
        label = "braided"
    return label, round(share, 4), top_cluster


def main() -> int:
    args = parse_args()
    root = repo_root()
    bipartite_path = normalize_user_path(args.bipartite, root / DEFAULT_BIPARTITE)
    fibers_path = normalize_user_path(args.fibers, root / DEFAULT_FIBERS)
    quotient_path = normalize_user_path(args.quotient, root / DEFAULT_QUOTIENT)
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)

    bipartite = load_json(bipartite_path)
    fibers = load_json(fibers_path)
    quotient = load_json(quotient_path) if quotient_path.exists() else {}

    hydrated_edges = [row for row in bipartite.get("hydrated_edges", []) if isinstance(row, dict)]
    incidence_entries = [row for row in bipartite.get("incidence_entries", []) if isinstance(row, dict)]

    source_modules = sorted(
        {
            str(row.get("source_module", "")).strip()
            for row in hydrated_edges
            if str(row.get("source_module", "")).strip()
        }
    )
    source_set = set(source_modules)

    out_by_source: dict[str, dict[str, float]] = defaultdict(dict)
    in_by_target: dict[str, dict[str, float]] = defaultdict(dict)
    for row in hydrated_edges:
        source = str(row.get("source_module", "")).strip()
        target = str(row.get("target_module", "")).strip()
        if not source or not target:
            continue
        mass = edge_mass(row)
        out_by_source[source][target] = out_by_source[source].get(target, 0.0) + mass
        in_by_target[target][source] = in_by_target[target].get(source, 0.0) + mass

    affinity: dict[tuple[str, str], float] = {}
    reasons: dict[tuple[str, str], Counter[str]] = defaultdict(Counter)

    for source, targets in out_by_source.items():
        total_mass = sum(targets.values()) or 1.0
        for target, mass in targets.items():
            if target in source_set:
                normalized = min(1.0, mass / total_mass)
                add_affinity(
                    affinity,
                    reasons,
                    source,
                    target,
                    0.75 + 0.5 * normalized,
                    "direct_chain",
                )

    for target, supporters in in_by_target.items():
        items = sorted(supporters.items())
        for i in range(len(items)):
            left, left_mass = items[i]
            for j in range(i + 1, len(items)):
                right, right_mass = items[j]
                overlap = min(left_mass, right_mass) / max(left_mass, right_mass)
                if overlap <= 0:
                    continue
                add_affinity(
                    affinity,
                    reasons,
                    left,
                    right,
                    0.6 * overlap,
                    f"co_target:{target}",
                )

    for group in fibers.get("source_sink_fiber_groups", []):
        if not isinstance(group, dict):
            continue
        mods = parse_module_list(group.get("source_modules"))
        score = safe_float(group.get("group_score"))
        weight = min(1.0, 0.25 + 0.03 * score)
        for i in range(len(mods)):
            for j in range(i + 1, len(mods)):
                add_affinity(affinity, reasons, mods[i], mods[j], weight, "fiber_group")

    for family in fibers.get("sink_family_entanglements", []):
        if not isinstance(family, dict):
            continue
        mods = parse_module_list(family.get("source_modules"))
        score = safe_float(family.get("entanglement_score"))
        weight = min(0.9, 0.2 + 0.015 * score)
        for i in range(len(mods)):
            for j in range(i + 1, len(mods)):
                add_affinity(affinity, reasons, mods[i], mods[j], weight, "sink_entanglement")

    parent = {module: module for module in source_modules}

    def find(x: str) -> str:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a: str, b: str) -> None:
        ra = find(a)
        rb = find(b)
        if ra != rb:
            if ra < rb:
                parent[rb] = ra
            else:
                parent[ra] = rb

    active_affinities: list[dict[str, Any]] = []
    for (left, right), weight in sorted(affinity.items(), key=lambda item: (-item[1], item[0])):
        if weight < args.cluster_threshold:
            continue
        union(left, right)
        active_affinities.append(
            {
                "left": left,
                "right": right,
                "weight": round(weight, 4),
                "reasons": dict(reasons[(left, right)]),
            }
        )

    members_by_root: dict[str, list[str]] = defaultdict(list)
    for module in source_modules:
        members_by_root[find(module)].append(module)

    cluster_id_by_module: dict[str, str] = {}
    cluster_rows: list[dict[str, Any]] = []
    for members in members_by_root.values():
        members = sorted(members)
        cluster_id = stable_cluster_id(members)
        for module in members:
            cluster_id_by_module[module] = cluster_id
        direct_targets: Counter[str] = Counter()
        total_mass = 0.0
        for module in members:
            for target, mass in out_by_source.get(module, {}).items():
                direct_targets[target] += mass
                total_mass += mass
        sink_families: Counter[str] = Counter()
        for row in incidence_entries:
            source = str(row.get("source_module", "")).strip()
            if source not in members:
                continue
            sink = str(row.get("sink_module", "")).strip()
            if sink:
                sink_families[sink] += incidence_mass(row)
        cluster_rows.append(
            {
                "cluster_id": cluster_id,
                "member_modules": members,
                "member_count": len(members),
                "total_direct_projection_mass": round(total_mass, 4),
                "top_direct_targets": [[name, round(mass, 4)] for name, mass in direct_targets.most_common(5)],
                "top_sink_families": [[name, round(mass, 4)] for name, mass in sink_families.most_common(5)],
            }
        )

    cluster_rows.sort(key=lambda row: (-row["total_direct_projection_mass"], row["cluster_id"]))
    cluster_members_by_id = {row["cluster_id"]: row["member_modules"] for row in cluster_rows}

    quotient_rows = {
        str(row.get("module", "")).strip(): row
        for row in quotient.get("hotspot_rows", [])
        if isinstance(row, dict)
    }

    direct_projection_by_target: dict[str, dict[str, float]] = defaultdict(lambda: defaultdict(float))
    for row in hydrated_edges:
        source = str(row.get("source_module", "")).strip()
        target = str(row.get("target_module", "")).strip()
        if source not in cluster_id_by_module or not target:
            continue
        cluster = cluster_id_by_module[source]
        direct_projection_by_target[target][cluster] += edge_mass(row)

    sink_projection_by_module: dict[str, dict[str, float]] = defaultdict(lambda: defaultdict(float))
    for row in incidence_entries:
        source = str(row.get("source_module", "")).strip()
        sink = str(row.get("sink_module", "")).strip()
        if source not in cluster_id_by_module or not sink:
            continue
        cluster = cluster_id_by_module[source]
        sink_projection_by_module[sink][cluster] += incidence_mass(row)

    projected_rows: list[dict[str, Any]] = []
    for module, cluster_weights in sink_projection_by_module.items():
        label, share, top_cluster = classify_projection(cluster_weights)
        total = sum(cluster_weights.values())
        q = quotient_rows.get(module, {})
        projected_rows.append(
            {
                "module": module,
                "projection_kind": "sink_family",
                "cluster_count": len(cluster_weights),
                "total_mass": round(total, 4),
                "dominant_cluster": top_cluster,
                "dominant_share": share,
                "classification": label,
                "cluster_weights": {
                    k: round(v, 4)
                    for k, v in sorted(cluster_weights.items(), key=lambda item: (-item[1], item[0]))
                },
                "dominant_cluster_members": cluster_members_by_id.get(top_cluster, []),
                "shell_class": str(q.get("residual_class", "")),
                "shell_ratio": round(safe_float(q.get("quotient_shell_ratio")), 4) if q else 0.0,
            }
        )

    direct_rows: list[dict[str, Any]] = []
    for module, cluster_weights in direct_projection_by_target.items():
        label, share, top_cluster = classify_projection(cluster_weights)
        total = sum(cluster_weights.values())
        direct_rows.append(
            {
                "module": module,
                "projection_kind": "carrier",
                "cluster_count": len(cluster_weights),
                "total_mass": round(total, 4),
                "dominant_cluster": top_cluster,
                "dominant_share": share,
                "classification": label,
                "cluster_weights": {
                    k: round(v, 4)
                    for k, v in sorted(cluster_weights.items(), key=lambda item: (-item[1], item[0]))
                },
            }
        )

    projected_rows.sort(key=lambda row: (-row["total_mass"], row["module"]))
    direct_rows.sort(key=lambda row: (-row["total_mass"], row["module"]))

    monochrome_shells = [
        row
        for row in projected_rows
        if row["classification"] == "monochrome" and row.get("shell_class") in {"shell_heavy", "mixed"}
    ]
    braided_rows = [row for row in projected_rows if row["classification"] == "braided"]

    summary = {
        "source_module_count": len(source_modules),
        "cluster_count": len(cluster_rows),
        "active_affinity_count": len(active_affinities),
        "top_sink_projection": projected_rows[0]["module"] if projected_rows else "",
        "top_direct_projection": direct_rows[0]["module"] if direct_rows else "",
        "monochrome_shell_count": len(monochrome_shells),
        "braided_sink_count": len(braided_rows),
        "cluster_threshold": args.cluster_threshold,
    }

    payload = {
        "kind": "projection_coloring",
        "inputs": {
            "bipartite": str(bipartite_path),
            "fibers": str(fibers_path),
            "quotient": str(quotient_path) if quotient_path.exists() else "",
        },
        "summary": summary,
        "source_clusters": cluster_rows,
        "active_affinities": active_affinities[: max(args.top, 25)],
        "sink_projections": projected_rows,
        "direct_projections": direct_rows,
        "monochrome_shells": monochrome_shells,
        "braided_sinks": braided_rows,
    }

    md_lines: list[str] = [
        "# Projection Coloring",
        "",
        "This report clusters the lower constructive/source side of the maintained source-sink graph and projects those cluster colors upward onto carrier and sink modules.",
        "It is a maintained heuristic over the authoritative DAG artifacts, not kernel truth.",
        "",
        "## Summary",
        f"- source modules clustered: `{summary['source_module_count']}`",
        f"- lower clusters: `{summary['cluster_count']}`",
        f"- active affinity edges: `{summary['active_affinity_count']}` at threshold `{summary['cluster_threshold']:.2f}`",
        f"- top sink projection: `{summary['top_sink_projection']}`",
        f"- top carrier projection: `{summary['top_direct_projection']}`",
        f"- monochrome shell candidates: `{summary['monochrome_shell_count']}`",
        f"- braided sink modules: `{summary['braided_sink_count']}`",
        "",
        "## Lower Clusters",
        md_table(
            ["Cluster", "Members", "Top Direct Targets", "Top Sink Families", "Mass"],
            [
                [
                    f"`{row['cluster_id']}`",
                    ", ".join(f"`{short_name(x)}`" for x in row["member_modules"]),
                    ", ".join(
                        f"`{short_name(name)}`:{mass:.1f}" for name, mass in row["top_direct_targets"][:3]
                    ) or "-",
                    ", ".join(
                        f"`{short_name(name)}`:{mass:.1f}" for name, mass in row["top_sink_families"][:3]
                    ) or "-",
                    f"{row['total_direct_projection_mass']:.1f}",
                ]
                for row in cluster_rows[: args.top]
            ],
        ),
        "",
        "## Monochrome Shell Candidates",
        md_table(
            ["Module", "Shell", "Dominant Cluster", "Share", "Cluster Members"],
            [
                [
                    f"`{row['module']}`",
                    row.get("shell_class") or "-",
                    f"`{row['dominant_cluster']}`" if row.get("dominant_cluster") else "-",
                    f"{row['dominant_share']:.2f}",
                    ", ".join(
                        f"`{short_name(x)}`" for x in row.get("dominant_cluster_members", [])[:4]
                    ) or "-",
                ]
                for row in monochrome_shells[: args.top]
            ]
            or [["-", "-", "-", "-", "-"]],
        ),
        "",
        "## Braided Sink Modules",
        md_table(
            ["Module", "Clusters", "Top Share", "Mass", "Cluster Mix"],
            [
                [
                    f"`{row['module']}`",
                    str(row["cluster_count"]),
                    f"{row['dominant_share']:.2f}",
                    f"{row['total_mass']:.1f}",
                    ", ".join(
                        f"`{short_name(cid)}`:{mass:.1f}"
                        for cid, mass in list(row["cluster_weights"].items())[:4]
                    ),
                ]
                for row in braided_rows[: args.top]
            ]
            or [["-", "-", "-", "-", "-"]],
        ),
        "",
        "## Top Sink Projections",
        md_table(
            ["Module", "Class", "Dominant Cluster", "Share", "Clusters", "Mass"],
            [
                [
                    f"`{row['module']}`",
                    row["classification"],
                    f"`{row['dominant_cluster']}`" if row.get("dominant_cluster") else "-",
                    f"{row['dominant_share']:.2f}",
                    str(row["cluster_count"]),
                    f"{row['total_mass']:.1f}",
                ]
                for row in projected_rows[: args.top]
            ],
        ),
        "",
        "## Method",
        "- lower/source modules come from `hydrated_edges[*].source_module` in `source-sink-bipartite.json`",
        "- source affinity combines direct source-to-source chains, co-target overlap, and maintained fiber / entanglement group evidence",
        "- clusters are connected components after thresholding the affinity graph",
        "- colors are projected upward to sink modules using `incidence_entries` and to carrier modules using `hydrated_edges`",
        "- `monochrome` means one lower cluster dominates; `braided` means the sink is genuinely mixed across lower clusters",
    ]

    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    md_out.write_text("\n".join(md_lines) + "\n", encoding="utf-8")

    print(f"[projection-coloring] wrote {json_out}")
    print(f"[projection-coloring] wrote {md_out}")
    print(f"[projection-coloring] clusters: {len(cluster_rows)}")
    if monochrome_shells:
        top = monochrome_shells[0]
        print(
            "[projection-coloring] top monochrome shell: "
            f"{top['module']} ({top['dominant_cluster']}, share={top['dominant_share']:.2f})"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
