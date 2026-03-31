#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
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

DEFAULT_TAGS = "artifacts/dag/representation-depth-tags.json"
DEFAULT_JSON_OUT = "reports/dag/structural-dictionary.json"
DEFAULT_MD_OUT = "reports/dag/structural-dictionary.md"
STOP_TOKENS = {
    "infogeometry",
    "canonical",
    "quantum",
    "krein",
    "theorem",
    "lemma",
    "def",
    "instance",
    "core",
}


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Build a declaration-level structural dictionary over the authoritative DAG. "
            "WL refinement is purely structural and blind to Lean tags during clustering; "
            "Lean-audited tags are applied only after structural classes are formed."
        )
    )
    ap.add_argument("--graph", default=str(default_decl_graph_file().relative_to(repo_root())))
    ap.add_argument("--decls", default=str(default_decl_metadata_file().relative_to(repo_root())))
    ap.add_argument("--tags", default=DEFAULT_TAGS)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--iters", type=int, default=3)
    ap.add_argument("--top", type=int, default=25)
    ap.add_argument("--top-suggestions", type=int, default=80)
    ap.add_argument("--min-tagged-support", type=int, default=2)
    return ap.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    raw = json.loads(path.read_text(encoding="utf-8"))
    return raw if isinstance(raw, dict) else {}


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def tokenize_name(text: str) -> list[str]:
    text = text.replace("'", " ")
    text = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", text)
    parts = re.split(r"[^A-Za-z0-9]+", text)
    return [
        tok.lower()
        for tok in parts
        if len(tok) >= 3 and tok.lower() not in STOP_TOKENS
    ]


def stable_hash(obj: Any) -> str:
    raw = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.blake2b(raw, digest_size=12).hexdigest()


def bucket_degree(n: int) -> str:
    if n <= 0:
        return "0"
    if n == 1:
        return "1"
    if n <= 4:
        return "2-4"
    if n <= 16:
        return "5-16"
    return "17+"


def edge_kind_counts(edges: list[list[Any]]) -> Counter[str]:
    counter: Counter[str] = Counter()
    for row in edges:
        if len(row) >= 2:
            counter[str(row[1])] += 1
    return counter


def top_items(counter: Counter[str], n: int) -> list[dict[str, Any]]:
    return [{"label": k, "count": v} for k, v in counter.most_common(n)]


def module_family(module: str) -> str:
    parts = [p for p in module.split(".") if p]
    if len(parts) >= 3 and parts[0] == "InfoGeometry":
        return ".".join(parts[:3])
    if len(parts) >= 2:
        return ".".join(parts[:2])
    return module or "<unknown>"


def initial_signature(
    meta: dict[str, Any],
    outgoing: list[list[Any]],
    incoming: list[tuple[int, str]],
) -> tuple[Any, ...]:
    out_counter = edge_kind_counts(outgoing)
    in_counter = Counter(kind for _, kind in incoming)
    return (
        str(meta.get("kind", "unknown")),
        bucket_degree(len(outgoing)),
        bucket_degree(len(incoming)),
        out_counter.get("value", 0),
        out_counter.get("type", 0),
        in_counter.get("value", 0),
        in_counter.get("type", 0),
    )


def wl_refine(
    nodes: list[str],
    forward: list[list[list[Any]]],
    reverse: list[list[tuple[int, str]]],
    base_colors: list[str],
    iters: int,
) -> list[str]:
    colors = list(base_colors)
    for _ in range(iters):
        next_colors: list[str] = []
        for idx, _ in enumerate(nodes):
            out_multiset = Counter()
            for row in forward[idx]:
                if len(row) < 2:
                    continue
                dst = int(row[0])
                kind = str(row[1])
                if 0 <= dst < len(nodes):
                    out_multiset[(kind, colors[dst])] += 1
            in_multiset = Counter((str(kind), colors[int(src)]) for src, kind in reverse[idx])
            signature = {
                "self": colors[idx],
                "out": sorted((kind, color, count) for (kind, color), count in out_multiset.items()),
                "in": sorted((kind, color, count) for (kind, color), count in in_multiset.items()),
            }
            next_colors.append(stable_hash(signature))
        colors = next_colors
    return colors


def render_md(payload: dict[str, Any], top: int, top_suggestions: int) -> str:
    summary = payload.get("summary", {})
    lines: list[str] = []
    lines.append("# Structural Dictionary")
    lines.append("")
    lines.append(
        "Declaration-level structural dictionary over the authoritative dependency DAG. "
        "WL refinement is blind to Lean tags during clustering. Lean-audited depth/judgment "
        "facts are only applied after structural classes are formed, so any transfer to "
        "untagged declarations is genuinely post-hoc."
    )
    lines.append("")
    lines.append("## Summary")
    for key in [
        "node_count",
        "edge_count",
        "tagged_seed_count",
        "wl_iterations",
        "color_class_count",
        "anchored_class_count",
        "pure_anchored_class_count",
        "mixed_anchored_class_count",
        "suggestable_untagged_count",
        "min_tagged_support",
    ]:
        lines.append(f"- `{key}`: `{summary.get(key, 0)}`")
    lines.append("")
    lines.append("## Tagged Anchors")
    for item in payload.get("seed_inventory", []):
        lines.append(
            f"- `L{item.get('depthNat')}` / `{item.get('judgment')}`: `{item.get('count')}`"
        )
    lines.append("")
    lines.append("## Pure Anchored Classes")
    pure = payload.get("pure_anchored_classes", [])[:top]
    if pure:
        for row in pure:
            lines.append(
                f"- `{row.get('class_id')}` size `{row.get('size')}` | tagged `{row.get('tagged_count')}` -> "
                f"depth `{row.get('suggested_depth')}` / `{row.get('suggested_judgment')}` | tokens `{row.get('top_tokens')}`"
            )
            for ex in row.get("examples", [])[:4]:
                lines.append(f"  example: `{ex}`")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Mixed Anchored Classes")
    mixed = payload.get("mixed_anchored_classes", [])[:top]
    if mixed:
        for row in mixed:
            lines.append(
                f"- `{row.get('class_id')}` size `{row.get('size')}` | tagged `{row.get('tagged_count')}` | "
                f"depths `{row.get('depth_counts')}` | judgments `{row.get('judgment_counts')}`"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Suggested Untagged Declarations")
    suggestions = payload.get("suggestions", [])[:top_suggestions]
    if suggestions:
        for row in suggestions:
            lines.append(
                f"- `{row.get('name')}` -> L`{row.get('suggested_depth')}` / `{row.get('suggested_judgment')}` "
                f"(class `{row.get('class_id')}`, tagged support `{row.get('tagged_count')}`)"
            )
    else:
        lines.append("- none")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    root = repo_root()
    graph_path = normalize_user_path(args.graph, default_decl_graph_file())
    decls_path = normalize_user_path(args.decls, default_decl_metadata_file())
    tags_path = normalize_user_path(args.tags, root / DEFAULT_TAGS)
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)

    graph = load_json(graph_path)
    decl_rows = load_jsonl(decls_path)
    tags_payload = load_json(tags_path)

    nodes = [str(x) for x in graph.get("nodes", [])]
    forward = graph.get("forward", [])
    if len(nodes) != len(forward):
        raise SystemExit("graph shape mismatch: nodes and forward adjacency lengths differ")

    meta_by_name = {
        str(row.get("name", "")): row
        for row in decl_rows
        if str(row.get("name", ""))
    }
    tags_by_name = {
        str(row.get("name", "")): row
        for row in tags_payload.get("declarations", [])
        if str(row.get("name", ""))
    }

    reverse: list[list[tuple[int, str]]] = [[] for _ in nodes]
    edge_count = 0
    for src, rows in enumerate(forward):
        for row in rows:
            if len(row) < 2:
                continue
            dst = int(row[0])
            kind = str(row[1])
            if 0 <= dst < len(nodes):
                reverse[dst].append((src, kind))
                edge_count += 1

    base_colors: list[str] = []
    for idx, name in enumerate(nodes):
        meta = meta_by_name.get(name, {})
        sig = initial_signature(meta, forward[idx], reverse[idx])
        base_colors.append(stable_hash(sig))

    final_colors = wl_refine(nodes, forward, reverse, base_colors, args.iters)

    class_members: dict[str, list[int]] = defaultdict(list)
    for idx, color in enumerate(final_colors):
        class_members[color].append(idx)

    seed_inventory_counter: Counter[tuple[int, str]] = Counter()
    for row in tags_by_name.values():
        if "depthNat" in row and "judgment" in row:
            seed_inventory_counter[(int(row["depthNat"]), str(row["judgment"]))] += 1

    classes: list[dict[str, Any]] = []
    pure_anchored_classes: list[dict[str, Any]] = []
    mixed_anchored_classes: list[dict[str, Any]] = []
    suggestions: list[dict[str, Any]] = []

    for color, members in class_members.items():
        tagged = [tags_by_name[nodes[i]] for i in members if nodes[i] in tags_by_name]
        depth_counts = Counter(int(row["depthNat"]) for row in tagged if "depthNat" in row)
        judgment_counts = Counter(str(row["judgment"]) for row in tagged if "judgment" in row)
        module_counts = Counter(
            module_family(str(meta_by_name.get(nodes[i], {}).get("module", "")))
            for i in members
        )
        token_counts: Counter[str] = Counter()
        kind_counts: Counter[str] = Counter()
        for i in members:
            name = nodes[i]
            meta = meta_by_name.get(name, {})
            kind_counts[str(meta.get("kind", "unknown"))] += 1
            token_counts.update(tokenize_name(name.rsplit(".", 1)[-1]))

        is_pure = (
            len(tagged) >= args.min_tagged_support
            and len(depth_counts) == 1
            and len(judgment_counts) == 1
        )
        suggested_depth = next(iter(depth_counts)) if is_pure else None
        suggested_judgment = next(iter(judgment_counts)) if is_pure else None

        cls = {
            "class_id": color[:12],
            "size": len(members),
            "anchored": bool(tagged),
            "tagged_count": len(tagged),
            "depth_counts": dict(sorted(depth_counts.items())),
            "judgment_counts": dict(sorted(judgment_counts.items())),
            "kind_counts": dict(sorted(kind_counts.items())),
            "module_families": top_items(module_counts, 5),
            "top_tokens": [tok for tok, _ in token_counts.most_common(6)],
            "examples": sorted(nodes[i] for i in members)[:6],
            "suggested_depth": suggested_depth,
            "suggested_judgment": suggested_judgment,
            "member_names": [nodes[i] for i in members],
        }
        classes.append(cls)

        if tagged:
            if is_pure:
                pure_anchored_classes.append(cls)
                for i in members:
                    name = nodes[i]
                    if name in tags_by_name:
                        continue
                    meta = meta_by_name.get(name, {})
                    suggestions.append(
                        {
                            "name": name,
                            "module": str(meta.get("module", "")),
                            "kind": str(meta.get("kind", "unknown")),
                            "class_id": cls["class_id"],
                            "tagged_count": len(tagged),
                            "suggested_depth": suggested_depth,
                            "suggested_judgment": suggested_judgment,
                            "top_tokens": cls["top_tokens"],
                        }
                    )
            else:
                mixed_anchored_classes.append(cls)

    pure_anchored_classes.sort(key=lambda row: (-row["size"], -row["tagged_count"], row["class_id"]))
    mixed_anchored_classes.sort(key=lambda row: (-row["size"], -row["tagged_count"], row["class_id"]))
    suggestions.sort(
        key=lambda row: (
            row["suggested_depth"],
            row["suggested_judgment"],
            -row["tagged_count"],
            row["module"],
            row["name"],
        )
    )
    classes.sort(key=lambda row: (-row["size"], -row["tagged_count"], row["class_id"]))

    payload = {
        "kind": "structural_dictionary",
        "inputs": {
            "graph": str(graph_path.relative_to(root)),
            "decls": str(decls_path.relative_to(root)),
            "tags": str(tags_path.relative_to(root)),
        },
        "summary": {
            "node_count": len(nodes),
            "edge_count": edge_count,
            "tagged_seed_count": len(tags_by_name),
            "wl_iterations": int(args.iters),
            "color_class_count": len(classes),
            "anchored_class_count": sum(1 for row in classes if row["anchored"]),
            "pure_anchored_class_count": len(pure_anchored_classes),
            "mixed_anchored_class_count": len(mixed_anchored_classes),
            "suggestable_untagged_count": len(suggestions),
            "min_tagged_support": int(args.min_tagged_support),
        },
        "seed_inventory": [
            {"depthNat": depth, "judgment": judgment, "count": count}
            for (depth, judgment), count in sorted(seed_inventory_counter.items())
        ],
        "pure_anchored_classes": pure_anchored_classes,
        "mixed_anchored_classes": mixed_anchored_classes,
        "suggestions": suggestions,
        "classes": classes,
    }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    md_out.write_text(render_md(payload, args.top, args.top_suggestions), encoding="utf-8")
    print(
        f"[structural-dictionary] nodes={len(nodes)} edges={edge_count} classes={len(classes)} "
        f"pure_anchored={len(pure_anchored_classes)} suggestions={len(suggestions)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
