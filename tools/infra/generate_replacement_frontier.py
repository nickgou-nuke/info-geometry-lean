#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
else:
    from tools.pathing import repo_root

DEFAULT_META = "artifacts/dag/index/meta.json"
DEFAULT_SURFACE_INDEX = "reports/dag/theorem-surface-index.json"
DEFAULT_GRAPH = "artifacts/dag/full_graph.json"
DEFAULT_REP_DEPTH = "artifacts/dag/representation-depth-tags.json"
DEFAULT_SIGNIFICANCE = "reports/theorem-significance.json"
DEFAULT_MD_OUT = "reports/dag/replacement-frontier.md"
DEFAULT_JSON_OUT = "reports/dag/replacement-frontier.json"

KNOWN_FACADE_STEMS = {
    "All",
    "Rosetta",
    "LLM",
    "Library",
    "Generated",
    "BlueprintTags",
    "auto_blueprints",
}

PRIORITY_CATEGORIES = {
    "package_reprojection",
    "surrogate_or_vacuous",
    "hypothesis_bridge",
}

DEPTH_BONUS = {
    "count": 3,
    "projective": 2,
    "operator": 1,
    "krein": 0,
    "transport": -1,
    "thermo": -2,
}

AUTO_NAME_PATTERNS = [
    re.compile(r"(^|\.)noConfusion(Type)?$"),
    re.compile(r"(^|\.)casesOn$"),
    re.compile(r"(^|\.)rec(On)?$"),
    re.compile(r"(^|\.)brecOn$"),
    re.compile(r"(^|\.)binductionOn$"),
    re.compile(r"(^|\.)below$"),
    re.compile(r"(^|\.)ibelow$"),
    re.compile(r"(^|\.)injEq$"),
    re.compile(r"(^|\.)sizeOf_spec$"),
    re.compile(r"(^|\.)_match_"),
]


@dataclass
class DeclRow:
    name: str
    short_name: str
    kind: str
    module: str
    file: str
    line: int
    category: str
    signals: list[str] = field(default_factory=list)
    audit_hits: list[str] = field(default_factory=list)


@dataclass
class DepthInfo:
    depth: str | None = None
    depth_nat: int | None = None
    judgment: str | None = None
    capstone: bool = False


@dataclass
class SignificanceInfo:
    codes: list[str] = field(default_factory=list)
    tags: list[str] = field(default_factory=list)


def load_meta(path: Path) -> dict[str, object]:
    meta = json.loads(path.read_text())
    schema = int(meta.get("schemaVersion", 0) or 0)
    if schema < 2:
        raise SystemExit(
            f"[replacement-frontier] refusing to trust stale DAG schema: meta.json schemaVersion={schema} < 2"
        )
    for key in ["timestamp", "nodeCount", "edgeCount", "morphismCount", "oleanHash"]:
        if key not in meta:
            raise SystemExit(f"[replacement-frontier] meta.json missing required field: {key}")
    return meta


def load_rows(path: Path) -> dict[str, DeclRow]:
    obj = json.loads(path.read_text())
    rows: dict[str, DeclRow] = {}
    for row in obj["rows"]:
        if row["kind"] not in {"def", "theorem"}:
            continue
        if not row.get("file") or not row.get("module"):
            continue
        rows[row["name"]] = DeclRow(
            name=row["name"],
            short_name=row["short_name"],
            kind=row["kind"],
            module=row["module"],
            file=row["file"],
            line=int(row["line"]),
            category=row["category"],
            signals=list(row.get("signals", [])),
            audit_hits=list(row.get("audit_hits", [])),
        )
    return rows


def load_depth_info(path: Path) -> dict[str, DepthInfo]:
    obj = json.loads(path.read_text())
    out: dict[str, DepthInfo] = {}
    for row in obj.get("declarations", []):
        out[row["name"]] = DepthInfo(
            depth=row.get("depth"),
            depth_nat=row.get("depthNat"),
            judgment=row.get("judgment"),
            capstone=bool(row.get("capstone", False)),
        )
    return out


def load_significance(path: Path) -> dict[str, SignificanceInfo]:
    out: dict[str, SignificanceInfo] = {}
    for row in json.loads(path.read_text()):
        codes = sorted({item["code"] for item in row.get("violations", [])})
        tags = list(row.get("tags", []))
        out[row["name"]] = SignificanceInfo(codes=codes, tags=tags)
    return out


def load_graph(path: Path):
    obj = json.loads(path.read_text())
    nodes: list[str] = obj["nodes"]
    forward = obj["forward"]
    rev: list[list[tuple[int, str]]] = [[] for _ in nodes]
    edge_count = 0
    for src, edges in enumerate(forward):
        for dst, kind in edges:
            rev[int(dst)].append((src, str(kind)))
            edge_count += 1
    name_to_idx = {name: i for i, name in enumerate(nodes)}
    return nodes, forward, rev, name_to_idx, edge_count


def verify_graph_against_meta(meta: dict[str, object], nodes: list[str], edge_count: int) -> None:
    meta_node_count = int(meta["nodeCount"])
    meta_edge_count = int(meta["edgeCount"])
    if meta_node_count != len(nodes):
        raise SystemExit(
            f"[replacement-frontier] nodeCount mismatch: meta={meta_node_count} graph={len(nodes)}"
        )
    if meta_edge_count != edge_count:
        raise SystemExit(
            f"[replacement-frontier] edgeCount mismatch: meta={meta_edge_count} graph={edge_count}"
        )


def is_autogen(name: str, row: DeclRow) -> bool:
    if row.line <= 0:
        return True
    return any(p.search(name) for p in AUTO_NAME_PATTERNS)


def module_of(name: str, rows: dict[str, DeclRow]) -> str:
    row = rows.get(name)
    if row is not None:
        return row.module
    parts = name.split(".")
    return ".".join(parts[:-1]) if len(parts) > 1 else name


def file_of(name: str, rows: dict[str, DeclRow]) -> str:
    row = rows.get(name)
    return row.file if row is not None else ""


def is_facade_module(module: str, file: str, stems: set[str]) -> bool:
    if file:
        if Path(file).stem in stems:
            return True
    return module.split(".")[-1] in stems


def classify_consumers(
    row: DeclRow,
    consumer_names: list[str],
    rows: dict[str, DeclRow],
    facade_stems: set[str],
) -> dict[str, list[str]]:
    buckets = {"local": [], "facade": [], "substantive": []}
    for name in consumer_names:
        mod = module_of(name, rows)
        fil = file_of(name, rows)
        if fil == row.file:
            buckets["local"].append(name)
        elif is_facade_module(mod, fil, facade_stems):
            buckets["facade"].append(name)
        else:
            buckets["substantive"].append(name)
    return buckets


def score_candidate(
    row: DeclRow,
    depth: DepthInfo,
    sig: SignificanceInfo,
    substantive_count: int,
    facade_count: int,
    local_count: int,
    external_support_count: int,
) -> int:
    codes = set(sig.codes)
    score = 0
    score += DEPTH_BONUS.get(depth.depth or "", 0)

    if row.category in PRIORITY_CATEGORIES:
        score += 4
    if substantive_count == 0:
        score += 5
    else:
        score -= min(substantive_count, 4) * 3

    if facade_count > 0:
        score += 3 + min(facade_count, 3)
    elif local_count > 0:
        score += 1

    if external_support_count <= 2:
        score += 2
    elif external_support_count >= 7:
        score -= 2

    if "V1/public-wrapper-inflation" in codes:
        score += 6
    if "V4/bridge-infrastructure-promoted" in codes:
        score += 5
    if "V2/dead-public-theorem" in codes:
        score += 4
    if "V0/syntactic-vacuity" in codes:
        score += 2

    if depth.capstone:
        score -= 2
    if row.kind == "theorem":
        score += 1
    if row.kind == "def" and not codes and row.category == "neutral_definition":
        score -= 4
    if row.audit_hits:
        score += 1
    return score


def replacement_class(
    row: DeclRow,
    sig: SignificanceInfo,
    substantive_count: int,
    facade_count: int,
    local_count: int,
) -> str | None:
    codes = set(sig.codes)
    if substantive_count > 0:
        if not codes and row.category not in PRIORITY_CATEGORIES:
            return None
        if "V1/public-wrapper-inflation" in codes:
            return "live_wrapper_surface"
        if "V4/bridge-infrastructure-promoted" in codes:
            return "live_bridge_surface"
        return None

    if "V4/bridge-infrastructure-promoted" in codes:
        return "bridge_surface_promoted"
    if "V1/public-wrapper-inflation" in codes:
        return "wrapper_surface"
    if "V2/dead-public-theorem" in codes:
        return "dead_public_theorem"
    if row.category == "surrogate_or_vacuous":
        return "surrogate_surface"
    if row.category == "hypothesis_bridge":
        return "hypothesis_bridge_surface"
    if row.category == "package_reprojection":
        return "package_reprojection_surface"
    if facade_count > 0:
        return "facade_export_only"
    if local_count > 0 and (sig.codes or row.category in PRIORITY_CATEGORIES):
        return "internal_staging_only"
    return None


def should_consider(
    row: DeclRow,
    sig: SignificanceInfo,
    substantive_count: int,
    facade_count: int,
) -> bool:
    if sig.codes:
        return True
    if row.category in PRIORITY_CATEGORIES:
        return True
    if facade_count > 0 and substantive_count == 0:
        return True
    return False


def shorten_targets(targets: list[str], limit: int = 10) -> tuple[list[str], int]:
    unique = sorted(set(targets))
    return unique[:limit], len(unique)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--meta", default=DEFAULT_META)
    ap.add_argument("--surface-index", default=DEFAULT_SURFACE_INDEX)
    ap.add_argument("--graph", default=DEFAULT_GRAPH)
    ap.add_argument("--rep-depth", default=DEFAULT_REP_DEPTH)
    ap.add_argument("--significance", default=DEFAULT_SIGNIFICANCE)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--min-score", type=int, default=8)
    ap.add_argument("--top", type=int, default=80)
    args = ap.parse_args()

    root = repo_root()
    meta = load_meta(root / args.meta)
    rows = load_rows(root / args.surface_index)
    depth_info = load_depth_info(root / args.rep_depth)
    significance = load_significance(root / args.significance)
    nodes, forward, rev, name_to_idx, edge_count = load_graph(root / args.graph)
    verify_graph_against_meta(meta, nodes, edge_count)
    facade_stems = set(KNOWN_FACADE_STEMS)

    candidates = []
    module_rollup: dict[str, dict[str, object]] = defaultdict(
        lambda: {
            "score": 0,
            "count": 0,
            "classes": Counter(),
            "depths": Counter(),
            "codes": Counter(),
            "substantive_free": 0,
        }
    )

    for name, row in rows.items():
        if is_autogen(name, row):
            continue
        idx = name_to_idx.get(name)
        if idx is None:
            continue

        forward_edges = forward[idx]
        value_targets = [
            nodes[int(dst)]
            for dst, kind in forward_edges
            if kind == "value" and nodes[int(dst)] != name
        ]
        external_value_targets = [t for t in value_targets if module_of(t, rows) != row.module]
        reverse_names = [nodes[src] for src, _kind in rev[idx] if nodes[src] != name]
        buckets = classify_consumers(row, reverse_names, rows, facade_stems)
        substantive_count = len(buckets["substantive"])
        facade_count = len(buckets["facade"])
        local_count = len(buckets["local"])
        sig = significance.get(name, SignificanceInfo())
        depth = depth_info.get(name, DepthInfo())

        if not should_consider(row, sig, substantive_count, facade_count):
            continue

        display_targets, target_count = shorten_targets(external_value_targets)
        score = score_candidate(
            row=row,
            depth=depth,
            sig=sig,
            substantive_count=substantive_count,
            facade_count=facade_count,
            local_count=local_count,
            external_support_count=target_count,
        )
        klass = replacement_class(
            row=row,
            sig=sig,
            substantive_count=substantive_count,
            facade_count=facade_count,
            local_count=local_count,
        )
        if klass is None or score < args.min_score:
            continue

        entry = {
            "name": name,
            "kind": row.kind,
            "module": row.module,
            "file": row.file,
            "line": row.line,
            "category": row.category,
            "depth": depth.depth,
            "depth_nat": depth.depth_nat,
            "judgment": depth.judgment,
            "capstone": depth.capstone,
            "score": score,
            "replacement_class": klass,
            "substantive_consumers": buckets["substantive"],
            "facade_consumers": buckets["facade"],
            "local_consumers": buckets["local"],
            "external_value_targets": display_targets,
            "external_value_target_count": target_count,
            "signals": row.signals,
            "audit_hits": row.audit_hits,
            "vacuity_codes": sig.codes,
            "significance_tags": sig.tags,
        }
        candidates.append(entry)

        roll = module_rollup[row.file]
        roll["score"] += score
        roll["count"] += 1
        roll["classes"][klass] += 1
        if depth.depth:
            roll["depths"][depth.depth] += 1
        for code in sig.codes:
            roll["codes"][code] += 1
        if substantive_count == 0:
            roll["substantive_free"] += 1

    candidates.sort(key=lambda e: (-e["score"], e["file"], e["line"], e["name"]))
    top = candidates[: args.top]

    module_rows = []
    for file, info in module_rollup.items():
        module_rows.append(
            {
                "file": file,
                "score": info["score"],
                "count": info["count"],
                "substantive_free": info["substantive_free"],
                "classes": dict(info["classes"]),
                "depths": dict(info["depths"]),
                "codes": dict(info["codes"]),
            }
        )
    module_rows.sort(key=lambda e: (-e["score"], -e["substantive_free"], -e["count"], e["file"]))

    out = {
        "source": {
            "meta": args.meta,
            "surface_index": args.surface_index,
            "graph": args.graph,
            "rep_depth": args.rep_depth,
            "significance": args.significance,
            "meta_timestamp": meta["timestamp"],
            "meta_schema_version": meta["schemaVersion"],
            "meta_olean_hash": meta["oleanHash"],
        },
        "summary": {
            "candidate_count": len(candidates),
            "top_count": len(top),
            "module_count": len(module_rows),
            "class_counts": dict(Counter(e["replacement_class"] for e in candidates)),
            "depth_counts": dict(Counter(e["depth"] or "untracked" for e in candidates)),
            "vacuity_counts": dict(Counter(code for e in candidates for code in e["vacuity_codes"])),
        },
        "top_candidates": top,
        "candidates": candidates,
        "module_rollup": module_rows,
    }

    json_out = root / args.json_out
    md_out = root / args.md_out
    json_out.write_text(json.dumps(out, indent=2))

    lines: list[str] = []
    lines.append("# Replacement Frontier")
    lines.append("")
    lines.append("This report ranks declarations by replacement feasibility, not by proof triviality.")
    lines.append("It integrates DAG consumer classes, representation depth, vacuity signals, and artifact freshness checks.")
    lines.append("")
    lines.append("## Artifact Trust")
    lines.append("")
    lines.append(f"- schema version: `{meta['schemaVersion']}`")
    lines.append(f"- timestamp: `{meta['timestamp']}`")
    lines.append(f"- olean hash: `{meta['oleanHash']}`")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- candidate declarations: `{out['summary']['candidate_count']}`")
    lines.append(f"- modules with replacement pressure: `{out['summary']['module_count']}`")
    lines.append(f"- class counts: `{out['summary']['class_counts']}`")
    lines.append(f"- depth counts: `{out['summary']['depth_counts']}`")
    lines.append(f"- vacuity counts: `{out['summary']['vacuity_counts']}`")
    lines.append("")
    lines.append("## Top Modules")
    lines.append("")
    lines.append("| File | Score | Candidates | Substantive-free | Depths | Classes | Vacuity |")
    lines.append("| --- | ---: | ---: | ---: | --- | --- | --- |")
    for row in module_rows[:25]:
        lines.append(
            f"| `{row['file']}` | {row['score']} | {row['count']} | {row['substantive_free']} | `{row['depths']}` | `{row['classes']}` | `{row['codes']}` |"
        )
    lines.append("")
    lines.append("## Top Declarations")
    lines.append("")
    for row in top:
        lines.append(f"### `{row['name']}`")
        lines.append(f"- file: `{row['file']}:{row['line']}`")
        lines.append(
            f"- kind/category/class/depth: `{row['kind']}` / `{row['category']}` / `{row['replacement_class']}` / `{row['depth']}`"
        )
        lines.append(f"- score: `{row['score']}`")
        lines.append(f"- substantive consumers: `{len(row['substantive_consumers'])}`")
        lines.append(f"- facade consumers: `{len(row['facade_consumers'])}`")
        lines.append(f"- local consumers: `{len(row['local_consumers'])}`")
        if row["external_value_target_count"]:
            clipped = " (clipped)" if row["external_value_target_count"] > len(row["external_value_targets"]) else ""
            lines.append(
                f"- external support targets: `{row['external_value_target_count']}` total{clipped} -> `{row['external_value_targets']}`"
            )
        if row["vacuity_codes"]:
            lines.append(f"- vacuity codes: `{row['vacuity_codes']}`")
        if row["significance_tags"]:
            lines.append(f"- significance tags: `{row['significance_tags']}`")
        if row["signals"]:
            lines.append(f"- signals: `{row['signals']}`")
        if row["audit_hits"]:
            lines.append(f"- audit hits: `{row['audit_hits']}`")
        lines.append("")

    md_out.write_text("\n".join(lines) + "\n")
    print(f"[replacement-frontier] wrote {json_out}")
    print(f"[replacement-frontier] wrote {md_out}")
    print(
        f"[replacement-frontier] candidate_count={len(candidates)} module_count={len(module_rows)} schemaVersion={meta['schemaVersion']} timestamp={meta['timestamp']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
