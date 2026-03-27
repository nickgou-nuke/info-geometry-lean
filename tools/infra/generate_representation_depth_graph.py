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
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


DEFAULT_DEPTH_INDEX = "reports/dag/representation-depth-index.json"
DEFAULT_AUDIT = "reports/dag/representation-depth-audit.json"
DEFAULT_JSON_OUT = "reports/dag/representation-depth-graph.json"
DEFAULT_MD_OUT = "reports/dag/representation-depth-graph.md"


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Render the manual representation-depth index as a bicategorical graph "
            "with layers, primitive translators, coherence files, and forbidden skips."
        )
    )
    ap.add_argument("--depth-index", default=DEFAULT_DEPTH_INDEX)
    ap.add_argument("--audit", default=DEFAULT_AUDIT)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    return ap.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    return raw if isinstance(raw, dict) else {}


def interval_label(src: int, dst: int) -> str:
    return f"{src}→{dst}"


def build_payload(depth_index: dict[str, Any], audit: dict[str, Any]) -> dict[str, Any]:
    layers = [row for row in depth_index.get("layers", []) if isinstance(row, dict)]
    files = [row for row in depth_index.get("files", []) if isinstance(row, dict)]
    review_surface = [row for row in depth_index.get("review_surface", []) if isinstance(row, dict)]

    max_depth = max((int(layer.get("depth", 0)) for layer in layers), default=0)
    layer_map = {int(layer.get("depth", 0)): dict(layer) for layer in layers}

    owners_by_depth: dict[int, list[dict[str, Any]]] = defaultdict(list)
    coherence_by_depth: dict[int, list[dict[str, Any]]] = defaultdict(list)
    capstones_by_depth: dict[int, list[dict[str, Any]]] = defaultdict(list)
    translators_by_step: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    files_by_interval: dict[str, list[dict[str, Any]]] = defaultdict(list)

    for row in files:
        src = int(row.get("source_depth", 0))
        dst = int(row.get("target_depth", 0))
        kind = str(row.get("kind", "unknown"))
        info = {
            "file": str(row.get("file", "")),
            "kind": kind,
            "source_depth": src,
            "target_depth": dst,
            "interval": interval_label(src, dst),
            "notes": str(row.get("notes", "")),
        }
        files_by_interval[info["interval"]].append(info)
        if kind == "owner":
            owners_by_depth[src].append(info)
        elif kind == "coherence":
            coherence_by_depth[dst].append(info)
        elif kind == "translator":
            translators_by_step[(src, dst)].append(info)
            if dst == max_depth:
                capstones_by_depth[dst].append(info)
        else:
            capstones_by_depth[dst].append(info)

    primitive_steps = []
    for depth in range(max_depth):
        key = (depth, depth + 1)
        primitive_steps.append(
            {
                "from_depth": depth,
                "to_depth": depth + 1,
                "present": bool(translators_by_step.get(key)),
                "translators": sorted(translators_by_step.get(key, []), key=lambda row: row["file"]),
            }
        )

    forbidden_skips = []
    for src in range(max_depth + 1):
        for dst in range(src + 2, max_depth + 1):
            forbidden_skips.append(
                {
                    "from_depth": src,
                    "to_depth": dst,
                    "label": f"L{src}→L{dst}",
                }
            )

    observed_dependency_bands = []
    observed_forward_bands = []
    for row in audit.get("transitions", []):
        if not isinstance(row, dict):
            continue
        src_interval = str(row.get("src_interval", ""))
        dst_interval = str(row.get("dst_interval", ""))
        status = str(row.get("status", ""))
        if not src_interval or not dst_interval:
            continue
        band = {
            "consumer_interval": src_interval,
            "dependency_interval": dst_interval,
            "status": status,
            "file_edges": int(row.get("file_edges", 0)),
            "decl_edges": int(row.get("decl_edges", 0)),
        }
        observed_dependency_bands.append(band)
        observed_forward_bands.append(
            {
                "support_interval": dst_interval,
                "consumer_interval": src_interval,
                "status": status,
                "file_edges": int(row.get("file_edges", 0)),
                "decl_edges": int(row.get("decl_edges", 0)),
            }
        )

    layer_objects = []
    for depth in sorted(layer_map):
        layer = layer_map[depth]
        layer_objects.append(
            {
                "depth": depth,
                "label": str(layer.get("label", f"L{depth}")),
                "description": str(layer.get("description", "")),
                "owners": sorted(owners_by_depth.get(depth, []), key=lambda row: row["file"]),
                "coherence": sorted(coherence_by_depth.get(depth, []), key=lambda row: row["file"]),
                "capstones": sorted(capstones_by_depth.get(depth, []), key=lambda row: row["file"]),
            }
        )

    role_counts: dict[str, int] = defaultdict(int)
    for row in files:
        role_counts[str(row.get("kind", "unknown"))] += 1

    return {
        "status": audit.get("status", "UNKNOWN"),
        "intent": depth_index.get("intent", ""),
        "rules": depth_index.get("rules", {}),
        "layers": layer_objects,
        "primitive_steps": primitive_steps,
        "forbidden_skips": forbidden_skips,
        "observed_dependency_bands": observed_dependency_bands,
        "observed_forward_bands": observed_forward_bands,
        "inventory": {
            "role_counts": dict(sorted(role_counts.items())),
            "interval_counts": dict(sorted((audit.get("inventory", {}) or {}).get("interval_counts", {}).items())),
            "indexed_files": int((audit.get("counts", {}) or {}).get("indexed_files", len(files))),
            "tracked_edges": int((audit.get("counts", {}) or {}).get("tracked_edges", 0)),
        },
        "review_surface": review_surface,
    }


def render_md(payload: dict[str, Any]) -> str:
    lines: list[str] = []
    inv = payload.get("inventory", {})

    lines.append("# Representation Depth Graph")
    lines.append("")
    lines.append("This report renders the stable representation-depth index as a bicategorical dictionary of presentations.")
    lines.append("")
    lines.append("## Status")
    lines.append(f"- source audit status: **{payload.get('status', 'UNKNOWN')}**")
    lines.append(f"- indexed files: `{inv.get('indexed_files', 0)}`")
    lines.append(f"- tracked direct edges: `{inv.get('tracked_edges', 0)}`")
    lines.append(f"- role counts: `{inv.get('role_counts', {})}`")
    lines.append("")
    lines.append("## Interpretation")
    lines.append("- objects: representation layers `L0 … Ln`")
    lines.append("- primitive 1-morphisms: adjacent translator files with `source_depth = d`, `target_depth = d+1`")
    lines.append("- 2-morphisms: coherence files that prove different adjacent composites agree")
    lines.append("- capstones: composite consumers that may touch many layers but should define no new skip-level ontology")
    lines.append("")
    lines.append("## Layer Objects")
    for layer in payload.get("layers", []):
        depth = layer.get("depth")
        lines.append(f"### L{depth} {layer.get('label', '')}")
        desc = str(layer.get("description", "")).strip()
        if desc:
            lines.append(desc)
        owners = layer.get("owners", [])
        if owners:
            lines.append("Owners:")
            for row in owners:
                lines.append(f"- `{row.get('file')}`")
        coherence = layer.get("coherence", [])
        if coherence:
            lines.append("Coherence files touching this layer:")
            for row in coherence:
                lines.append(f"- `{row.get('file')}`")
        capstones = layer.get("capstones", [])
        if capstones:
            lines.append("Capstones / composites ending here:")
            for row in capstones:
                lines.append(f"- `{row.get('file')}`")
        lines.append("")

    lines.append("## Primitive Translator Steps")
    for row in payload.get("primitive_steps", []):
        lines.append(f"### L{row.get('from_depth')} → L{row.get('to_depth')}")
        translators = row.get("translators", [])
        if translators:
            for tr in translators:
                lines.append(f"- `{tr.get('file')}`")
        else:
            lines.append("- missing")
        lines.append("")

    lines.append("## Forbidden Skips")
    for row in payload.get("forbidden_skips", []):
        lines.append(f"- `{row.get('label')}`")
    lines.append("")

    lines.append("## Observed Direct Dependency Bands")
    lines.append("| Consumer interval | Dependency interval | Status | File edges | Decl edges |")
    lines.append("| --- | --- | --- | ---: | ---: |")
    for row in payload.get("observed_dependency_bands", []):
        lines.append(
            f"| `{row.get('consumer_interval')}` | `{row.get('dependency_interval')}` | `{row.get('status')}` | {row.get('file_edges', 0)} | {row.get('decl_edges', 0)} |"
        )
    lines.append("")

    lines.append("## Review Surface")
    review = payload.get("review_surface", [])
    if review:
        for row in review:
            lines.append(f"- `{row.get('file')}` | {row.get('reason', '')}")
    else:
        lines.append("- none")
    lines.append("")

    lines.append("## Notes")
    lines.append("- this graph is driven by the manual representation-depth index, not by hotspot clustering")
    lines.append("- it complements `representation-depth-audit`, which checks direct edge legality")
    lines.append("- it is the right substrate for a future depth-aware coloring / projector pass")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    root = repo_root()
    depth_path = normalize_user_path(args.depth_index, root / DEFAULT_DEPTH_INDEX)
    audit_path = normalize_user_path(args.audit, root / DEFAULT_AUDIT)
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)

    depth_index = load_json(depth_path)
    audit = load_json(audit_path)
    payload = build_payload(depth_index, audit)

    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    md_out.write_text(render_md(payload), encoding="utf-8")

    print(f"[representation-depth-graph] wrote {json_out}")
    print(f"[representation-depth-graph] wrote {md_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
