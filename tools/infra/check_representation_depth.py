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
        default_decl_graph_file,
        default_decl_metadata_file,
        normalize_user_path,
        repo_root,
    )
else:
    from tools.pathing import (
        default_decl_graph_file,
        default_decl_metadata_file,
        normalize_user_path,
        repo_root,
    )


DEFAULT_DEPTH_INDEX = "reports/dag/representation-depth-index.json"
DEFAULT_JSON_OUT = "reports/dag/representation-depth-audit.json"
DEFAULT_MD_OUT = "reports/dag/representation-depth-audit.md"


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Audit the stable representation spine for direct file-to-file depth skips "
            "using the authoritative declaration DAG and a manual depth index."
        )
    )
    ap.add_argument("--graph", default=str(default_decl_graph_file().relative_to(repo_root())))
    ap.add_argument("--decls", default=str(default_decl_metadata_file().relative_to(repo_root())))
    ap.add_argument("--depth-index", default=DEFAULT_DEPTH_INDEX)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument(
        "--top",
        type=int,
        default=40,
        help="Maximum number of wormhole/regression edges to render in the markdown summary.",
    )
    return ap.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    return raw if isinstance(raw, dict) else {}


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            raw = json.loads(line)
            if isinstance(raw, dict):
                out.append(raw)
    return out


def rel_repo_path(path: str, root: Path) -> str:
    p = Path(path)
    try:
        return str(p.resolve().relative_to(root.resolve()))
    except Exception:
        try:
            return str((root / p).resolve().relative_to(root.resolve()))
        except Exception:
            return str(path)


def normalize_decls(rows: list[dict[str, Any]], root: Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in rows:
        name = str(row.get("name", ""))
        if not name:
            continue
        copied = dict(row)
        copied["file_rel"] = rel_repo_path(str(row.get("file", "")), root)
        out[name] = copied
    return out


def load_depth_index(path: Path) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    payload = load_json(path)
    files_by_rel: dict[str, dict[str, Any]] = {}
    for row in payload.get("files", []):
        if not isinstance(row, dict):
            continue
        rel = str(row.get("file", ""))
        if not rel:
            continue
        files_by_rel[rel] = {
            "file": rel,
            "kind": str(row.get("kind", "")),
            "source_depth": int(row.get("source_depth", 0)),
            "target_depth": int(row.get("target_depth", 0)),
            "notes": str(row.get("notes", "")),
        }
    return files_by_rel, payload


def classify_edge(src_info: dict[str, Any], dst_info: dict[str, Any]) -> tuple[str, int]:
    src_low = int(src_info["source_depth"])
    src_high = int(src_info["target_depth"])
    dst_low = int(dst_info["source_depth"])
    dst_high = int(dst_info["target_depth"])

    if dst_low > src_high:
        return "regression", dst_low - src_high
    if src_low > dst_high + 1:
        return "wormhole", src_low - dst_high
    return "healthy", 0


def interval_label(info: dict[str, Any]) -> str:
    return f"{int(info['source_depth'])}→{int(info['target_depth'])}"


def aggregate_edges(
    graph: dict[str, Any],
    decls_by_name: dict[str, dict[str, Any]],
    depth_files: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    nodes = graph.get("nodes", [])
    forward = graph.get("forward", [])
    decl_names = [node if isinstance(node, str) else "" for node in nodes]

    edge_map: dict[tuple[str, str], dict[str, Any]] = {}
    skipped_decls = 0
    tracked_files_seen: set[str] = set()

    for src_idx, raw_edges in enumerate(forward):
        if src_idx >= len(decl_names):
            continue
        src_name = decl_names[src_idx]
        if not src_name:
            continue
        src_decl = decls_by_name.get(src_name)
        if not src_decl:
            skipped_decls += 1
            continue
        src_file = str(src_decl.get("file_rel", ""))
        src_info = depth_files.get(src_file)
        if src_info is None:
            continue
        tracked_files_seen.add(src_file)

        if not isinstance(raw_edges, list):
            continue
        for edge in raw_edges:
            if not isinstance(edge, list) or len(edge) < 1:
                continue
            try:
                dst_idx = int(edge[0])
            except Exception:
                continue
            if not (0 <= dst_idx < len(decl_names)):
                continue
            dst_name = decl_names[dst_idx]
            if not dst_name:
                continue
            dst_decl = decls_by_name.get(dst_name)
            if not dst_decl:
                skipped_decls += 1
                continue
            dst_file = str(dst_decl.get("file_rel", ""))
            dst_info = depth_files.get(dst_file)
            if dst_info is None or dst_file == src_file:
                continue
            tracked_files_seen.add(dst_file)

            status, severity = classify_edge(src_info, dst_info)
            key = (src_file, dst_file)
            row = edge_map.setdefault(
                key,
                {
                    "src_file": src_file,
                    "dst_file": dst_file,
                    "src_kind": src_info["kind"],
                    "dst_kind": dst_info["kind"],
                    "src_source_depth": src_info["source_depth"],
                    "src_target_depth": src_info["target_depth"],
                    "dst_source_depth": dst_info["source_depth"],
                    "dst_target_depth": dst_info["target_depth"],
                    "src_interval": interval_label(src_info),
                    "dst_interval": interval_label(dst_info),
                    "status": status,
                    "severity": severity,
                    "direct_decl_edges": 0,
                    "example_src_decl": src_name,
                    "example_dst_decl": dst_name,
                    "edge_kinds": defaultdict(int),
                },
            )
            row["direct_decl_edges"] += 1
            row["severity"] = max(int(row["severity"]), severity)
            if status != "healthy":
                row["status"] = status
            edge_kind = str(edge[1]) if len(edge) > 1 else "unknown"
            row["edge_kinds"][edge_kind] += 1

    edges = []
    for row in edge_map.values():
        row["edge_kinds"] = dict(sorted(row["edge_kinds"].items()))
        edges.append(row)

    return {
        "edges": edges,
        "skipped_decl_metadata": skipped_decls,
        "tracked_files_seen": sorted(tracked_files_seen),
    }


def summarize(depth_payload: dict[str, Any], aggregated: dict[str, Any], depth_files: dict[str, dict[str, Any]]) -> dict[str, Any]:
    edges = aggregated["edges"]
    wormholes = sorted(
        [row for row in edges if row["status"] == "wormhole"],
        key=lambda row: (-int(row["severity"]), -int(row["direct_decl_edges"]), row["src_file"], row["dst_file"]),
    )
    regressions = sorted(
        [row for row in edges if row["status"] == "regression"],
        key=lambda row: (-int(row["severity"]), -int(row["direct_decl_edges"]), row["src_file"], row["dst_file"]),
    )
    healthy = [row for row in edges if row["status"] == "healthy"]

    by_src: dict[str, dict[str, int]] = defaultdict(lambda: {"wormholes": 0, "regressions": 0})
    for row in wormholes:
        by_src[row["src_file"]]["wormholes"] += 1
    for row in regressions:
        by_src[row["src_file"]]["regressions"] += 1

    offenders = sorted(
        (
            {
                "file": file,
                "wormholes": counts["wormholes"],
                "regressions": counts["regressions"],
                "total": counts["wormholes"] + counts["regressions"],
            }
            for file, counts in by_src.items()
        ),
        key=lambda row: (-int(row["total"]), -int(row["wormholes"]), row["file"]),
    )

    kind_counts: dict[str, int] = defaultdict(int)
    interval_counts: dict[str, int] = defaultdict(int)
    depth_counts: dict[str, int] = defaultdict(int)
    file_rows: list[dict[str, Any]] = []
    for rel, info in sorted(depth_files.items()):
        interval = interval_label(info)
        kind = str(info.get("kind", "unknown"))
        kind_counts[kind] += 1
        interval_counts[interval] += 1
        depth_counts[f"L{int(info['source_depth'])}"] += 1
        file_rows.append(
            {
                "file": rel,
                "kind": kind,
                "source_depth": int(info["source_depth"]),
                "target_depth": int(info["target_depth"]),
                "interval": interval,
                "notes": str(info.get("notes", "")),
            }
        )

    transition_counts: dict[tuple[str, str, str], int] = defaultdict(int)
    transition_decl_edges: dict[tuple[str, str, str], int] = defaultdict(int)
    for row in edges:
        key = (str(row["src_interval"]), str(row["dst_interval"]), str(row["status"]))
        transition_counts[key] += 1
        transition_decl_edges[key] += int(row["direct_decl_edges"])
    transitions = sorted(
        (
            {
                "src_interval": src,
                "dst_interval": dst,
                "status": status,
                "file_edges": file_edges,
                "decl_edges": transition_decl_edges[(src, dst, status)],
            }
            for (src, dst, status), file_edges in transition_counts.items()
        ),
        key=lambda row: (-int(row["file_edges"]), -int(row["decl_edges"]), row["src_interval"], row["dst_interval"], row["status"]),
    )

    indexed_files = len(depth_files)
    tracked_files_seen = aggregated.get("tracked_files_seen", [])

    return {
        "status": "PASS" if not wormholes and not regressions else "FAIL",
        "source": {
            "layers": depth_payload.get("layers", []),
            "rules": depth_payload.get("rules", {}),
            "review_surface": depth_payload.get("review_surface", []),
        },
        "counts": {
            "indexed_files": indexed_files,
            "tracked_files_seen_in_graph": len(tracked_files_seen),
            "tracked_edges": len(edges),
            "healthy_edges": len(healthy),
            "wormholes": len(wormholes),
            "regressions": len(regressions),
            "offender_files": len(offenders),
            "skipped_decl_metadata": aggregated.get("skipped_decl_metadata", 0),
        },
        "inventory": {
            "kind_counts": dict(sorted(kind_counts.items())),
            "interval_counts": dict(sorted(interval_counts.items())),
            "depth_counts": dict(sorted(depth_counts.items())),
            "files": file_rows,
        },
        "transitions": transitions,
        "offenders": offenders,
        "wormholes": wormholes,
        "regressions": regressions,
    }


def render_md(payload: dict[str, Any], top: int) -> str:
    counts = payload.get("counts", {})
    inventory = payload.get("inventory", {})
    lines: list[str] = []
    lines.append("# Representation Depth Audit")
    lines.append("")
    lines.append(
        "Direct file-to-file dependency audit over the authoritative declaration DAG, "
        "scored against the manual representation-depth index."
    )
    lines.append("")
    lines.append("## Status")
    lines.append(f"- topological integrity gate: **{payload.get('status', 'FAIL')}**")
    lines.append("- edge semantics: direct declaration dependencies lifted to owner-file edges")
    lines.append("- depth semantics: each tracked file is an interval `[source_depth, target_depth]`")
    lines.append("- rule: a direct dependency may stay within the same interval or touch the immediately previous layer only")
    lines.append("")
    lines.append("## Counts")
    lines.append(f"- indexed files in manual depth map: **{counts.get('indexed_files', 0)}**")
    lines.append(f"- indexed files seen in authoritative graph: **{counts.get('tracked_files_seen_in_graph', 0)}**")
    lines.append(f"- tracked file edges: **{counts.get('tracked_edges', 0)}**")
    lines.append(f"- healthy direct edges: **{counts.get('healthy_edges', 0)}**")
    lines.append(f"- wormholes: **{counts.get('wormholes', 0)}**")
    lines.append(f"- regressions: **{counts.get('regressions', 0)}**")
    lines.append(f"- offending source files: **{counts.get('offender_files', 0)}**")
    lines.append("")
    lines.append("## Indexed Inventory")
    lines.append("### Kinds")
    for kind, count in inventory.get("kind_counts", {}).items():
        lines.append(f"- `{kind}`: `{count}`")
    lines.append("### Intervals")
    for interval, count in inventory.get("interval_counts", {}).items():
        lines.append(f"- `{interval}`: `{count}`")
    lines.append("")
    lines.append("## Observed Direct Transition Bands")
    transitions = payload.get("transitions", [])
    if transitions:
        lines.append("| Source interval | Dependency interval | Status | File edges | Decl edges |")
        lines.append("| --- | --- | --- | ---: | ---: |")
        for row in transitions[:top]:
            lines.append(
                f"| `{row.get('src_interval')}` | `{row.get('dst_interval')}` | `{row.get('status')}` | "
                f"{row.get('file_edges', 0)} | {row.get('decl_edges', 0)} |"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Top Offenders")
    offenders = payload.get("offenders", [])
    if offenders:
        for row in offenders[:top]:
            lines.append(
                f"- `{row.get('file')}` | wormholes `{row.get('wormholes', 0)}` | "
                f"regressions `{row.get('regressions', 0)}` | total `{row.get('total', 0)}`"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Wormholes")
    wormholes = payload.get("wormholes", [])
    if wormholes:
        for row in wormholes[:top]:
            lines.append(
                f"- `{row.get('src_file')}` [{row.get('src_source_depth')}→{row.get('src_target_depth')}] "
                f"-> `{row.get('dst_file')}` [{row.get('dst_source_depth')}→{row.get('dst_target_depth')}] "
                f"| severity `{row.get('severity')}` | decl-edges `{row.get('direct_decl_edges')}`"
            )
            lines.append(
                f"  example: `{row.get('example_src_decl')}` depends on `{row.get('example_dst_decl')}`"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Regressions")
    regressions = payload.get("regressions", [])
    if regressions:
        for row in regressions[:top]:
            lines.append(
                f"- `{row.get('src_file')}` [{row.get('src_source_depth')}→{row.get('src_target_depth')}] "
                f"-> `{row.get('dst_file')}` [{row.get('dst_source_depth')}→{row.get('dst_target_depth')}] "
                f"| severity `{row.get('severity')}` | decl-edges `{row.get('direct_decl_edges')}`"
            )
            lines.append(
                f"  example: `{row.get('example_src_decl')}` depends on `{row.get('example_dst_decl')}`"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Notes")
    lines.append("- this report only scores files present in the manual depth index")
    lines.append("- unknown files are ignored rather than guessed")
    lines.append("- capstone files should be modeled as consumers/composites, not primitive translators")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    root = repo_root()

    graph_path = normalize_user_path(args.graph, default_decl_graph_file())
    decls_path = normalize_user_path(args.decls, default_decl_metadata_file())
    depth_path = normalize_user_path(args.depth_index, root / DEFAULT_DEPTH_INDEX)
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)

    graph = load_json(graph_path)
    decls = normalize_decls(load_jsonl(decls_path), root)
    depth_files, depth_payload = load_depth_index(depth_path)
    aggregated = aggregate_edges(graph, decls, depth_files)
    summary = summarize(depth_payload, aggregated, depth_files)

    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    md_out.write_text(render_md(summary, args.top), encoding="utf-8")

    print(f"[check-representation-depth] wrote {json_out}")
    print(f"[check-representation-depth] wrote {md_out}")
    print(
        "[check-representation-depth] "
        f"status={summary.get('status', 'FAIL')} "
        f"wormholes={summary['counts'].get('wormholes', 0)} "
        f"regressions={summary['counts'].get('regressions', 0)}"
    )
    return 0 if summary.get("status") == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
