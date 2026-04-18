#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


DEFAULT_INPUT_DIR = "artifacts/expr-graph/arango"
DEFAULT_JSON_OUT = "reports/dag/expr-alpha-dedup.json"
DEFAULT_MD_OUT = "reports/dag/expr-alpha-dedup.md"

ROLE_ORDER = {
    "type": 0,
    "value": 1,
    "fn": 2,
    "arg": 3,
    "body": 4,
    "expr": 5,
}


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Compute alpha-equivalence style structural dedup over ExprArangoExport graphs "
            "(ig_nodes.jsonl / ig_edges.jsonl), producing declaration-level and subgraph-level "
            "compression evidence."
        )
    )
    ap.add_argument("--input-dir", default=DEFAULT_INPUT_DIR)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--top-decl-groups", type=int, default=30)
    ap.add_argument("--top-subgraphs", type=int, default=40)
    ap.add_argument("--min-decl-group-size", type=int, default=2)
    ap.add_argument("--min-subgraph-occurrences", type=int, default=4)
    ap.add_argument(
        "--const-mode",
        choices=["strict", "normalize"],
        default="strict",
        help=(
            "strict: constant names participate in fingerprints; "
            "normalize: all constants collapsed to one token."
        ),
    )
    ap.add_argument(
        "--allow-missing-input",
        action="store_true",
        help=(
            "If ig_nodes/ig_edges are missing, write a skipped report and exit 0 "
            "instead of failing."
        ),
    )
    return ap.parse_args()


def iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except Exception:
                continue
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def parse_key(raw: str) -> str:
    value = str(raw).strip()
    if "/" in value:
        return value.split("/", 1)[1]
    return value


def stable_hash(payload: str) -> str:
    return hashlib.sha1(payload.encode("utf-8")).hexdigest()


def role_sort_key(role: str) -> tuple[int, str]:
    return (ROLE_ORDER.get(role, 99), role)


def node_payload(node: dict[str, Any], *, const_mode: str) -> str:
    expr_tag = str(node.get("exprTag", "")).strip()
    info = str(node.get("info", "")).strip()

    if expr_tag == "bvar":
        idx = node.get("deBruijnIdx")
        if not isinstance(idx, int):
            try:
                idx = int(info)
            except Exception:
                idx = -1
        return f"bvar:{idx}"
    if expr_tag in {"fvar", "mvar"}:
        return f"{expr_tag}:*"
    if expr_tag == "const":
        if const_mode == "normalize":
            return "const:*"
        return f"const:{info}"
    if expr_tag in {"lit_nat", "lit_str", "sort", "proj"}:
        return f"{expr_tag}:{info}"
    return f"{expr_tag}:{info}"


def rel_path(path: Path) -> str:
    root = repo_root().resolve()
    p = path.resolve()
    try:
        return str(p.relative_to(root))
    except Exception:
        return str(p)


def build_markdown(
    report: dict[str, Any],
    *,
    top_decl_groups: list[dict[str, Any]],
    top_subgraphs: list[dict[str, Any]],
) -> str:
    stats = report.get("stats", {})
    lines: list[str] = []
    lines.append("# Expr Alpha Dedup Report")
    lines.append("")
    lines.append(f"- generated_at: `{report.get('generated_at', '')}`")
    lines.append(f"- input_dir: `{report.get('input_dir', '')}`")
    lines.append(f"- const_mode: `{report.get('const_mode', '')}`")
    lines.append("")
    lines.append("## Compression Summary")
    lines.append("")
    lines.append(f"- decl_nodes: `{stats.get('decl_nodes', 0)}`")
    lines.append(f"- expr_nodes: `{stats.get('expr_nodes', 0)}`")
    lines.append(f"- unique_expr_fingerprints: `{stats.get('unique_expr_fingerprints', 0)}`")
    lines.append(f"- expr_dedup_factor: `{stats.get('expr_dedup_factor', 0.0)}`")
    lines.append(f"- declarations_with_roots: `{stats.get('declarations_with_roots', 0)}`")
    lines.append(f"- unique_decl_fingerprints: `{stats.get('unique_decl_fingerprints', 0)}`")
    lines.append(f"- decl_dedup_factor: `{stats.get('decl_dedup_factor', 0.0)}`")
    lines.append("")
    lines.append("## Declaration Equivalence Groups")
    lines.append("")
    if not top_decl_groups:
        lines.append("_No declaration equivalence groups matched thresholds._")
    else:
        lines.append("| rank | group_size | fingerprint | declarations |")
        lines.append("|---|---:|---|---|")
        for idx, row in enumerate(top_decl_groups, start=1):
            members = ", ".join(str(x) for x in row.get("declarations", []))
            lines.append(
                f"| {idx} | {int(row.get('group_size', 0))} | `{str(row.get('fingerprint', ''))[:16]}` | {members} |"
            )
    lines.append("")
    lines.append("## Repeated Subgraphs")
    lines.append("")
    if not top_subgraphs:
        lines.append("_No repeated subgraphs matched thresholds._")
    else:
        lines.append("| rank | expr_tag | occurrences | declarations | fingerprint |")
        lines.append("|---|---|---:|---:|---|")
        for idx, row in enumerate(top_subgraphs, start=1):
            lines.append(
                f"| {idx} | `{row.get('expr_tag', '')}` | {int(row.get('occurrences', 0))} | "
                f"{int(row.get('declaration_count', 0))} | `{str(row.get('fingerprint', ''))[:16]}` |"
            )
    lines.append("")
    return "\n".join(lines) + "\n"


def build_missing_input_markdown(report: dict[str, Any]) -> str:
    missing = report.get("missing_inputs", [])
    lines: list[str] = []
    lines.append("# Expr Alpha Dedup Report")
    lines.append("")
    lines.append(f"- generated_at: `{report.get('generated_at', '')}`")
    lines.append(f"- input_dir: `{report.get('input_dir', '')}`")
    lines.append(f"- status: `{report.get('status', '')}`")
    lines.append("")
    lines.append("## Missing Inputs")
    lines.append("")
    if not missing:
        lines.append("_No missing input paths recorded._")
    else:
        for item in missing:
            lines.append(f"- `{item}`")
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    input_dir = normalize_user_path(args.input_dir, (repo_root() / DEFAULT_INPUT_DIR))
    json_out = normalize_user_path(args.json_out, (repo_root() / DEFAULT_JSON_OUT))
    md_out = normalize_user_path(args.md_out, (repo_root() / DEFAULT_MD_OUT))

    nodes_path = input_dir / "ig_nodes.jsonl"
    edges_path = input_dir / "ig_edges.jsonl"
    meta_path = input_dir / "metadata.json"

    missing_inputs: list[Path] = []
    if not nodes_path.exists():
        missing_inputs.append(nodes_path)
    if not edges_path.exists():
        missing_inputs.append(edges_path)
    if missing_inputs:
        if not args.allow_missing_input:
            raise FileNotFoundError(
                "missing required ExprArangoExport inputs: "
                + ", ".join(str(p) for p in missing_inputs)
            )
        report = {
            "generated_at": utc_now_iso(),
            "input_dir": rel_path(input_dir),
            "const_mode": str(args.const_mode),
            "status": "skipped_missing_input",
            "missing_inputs": [rel_path(p) for p in missing_inputs],
            "stats": {
                "decl_nodes": 0,
                "expr_nodes": 0,
                "declarations_with_roots": 0,
                "unique_expr_fingerprints": 0,
                "unique_decl_fingerprints": 0,
                "expr_dedup_factor": 0.0,
                "decl_dedup_factor": 0.0,
                "decl_equivalence_groups": 0,
                "repeated_subgraphs": 0,
            },
            "top_decl_groups": [],
            "top_subgraphs": [],
        }
        json_out.parent.mkdir(parents=True, exist_ok=True)
        json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
        md_out.parent.mkdir(parents=True, exist_ok=True)
        md_out.write_text(build_missing_input_markdown(report), encoding="utf-8")
        print(
            f"[ExprAlphaDedup] input missing; wrote skipped report {json_out} and {md_out}",
            flush=True,
        )
        return 0

    nodes = iter_jsonl(nodes_path)
    edges = iter_jsonl(edges_path)
    source_meta: dict[str, Any] = {}
    if meta_path.exists():
        try:
            parsed = json.loads(meta_path.read_text(encoding="utf-8"))
            if isinstance(parsed, dict):
                source_meta = parsed
        except Exception:
            source_meta = {}

    node_by_key: dict[str, dict[str, Any]] = {}
    expr_keys: list[str] = []
    decl_keys: list[str] = []
    for row in nodes:
        key = str(row.get("_key", "")).strip()
        if not key:
            continue
        node_by_key[key] = row
        graph_kind = str(row.get("graphKind", "")).strip()
        if graph_kind == "expr":
            expr_keys.append(key)
        elif graph_kind == "decl":
            decl_keys.append(key)

    ast_children: dict[str, list[tuple[str, str]]] = defaultdict(list)
    decl_roots: dict[str, dict[str, str]] = defaultdict(dict)
    for row in edges:
        kind = str(row.get("kind", "")).strip()
        role = str(row.get("role", "")).strip()
        src = parse_key(str(row.get("_from", "")))
        dst = parse_key(str(row.get("_to", "")))
        if not src or not dst:
            continue
        if kind == "ast":
            ast_children[src].append((role, dst))
        elif kind == "decl_root":
            decl_roots[src][role] = dst

    memo_expr_fp: dict[str, str] = {}
    memo_expr_repr: dict[str, str] = {}

    def expr_fp(key: str) -> str:
        cached = memo_expr_fp.get(key)
        if cached is not None:
            return cached
        node = node_by_key.get(key, {})
        if str(node.get("graphKind", "")) != "expr":
            fp = stable_hash(f"non_expr:{key}")
            memo_expr_fp[key] = fp
            memo_expr_repr[key] = f"non_expr:{key}"
            return fp

        parts: list[str] = [node_payload(node, const_mode=args.const_mode)]
        children = ast_children.get(key, [])
        children_sorted = sorted(children, key=lambda pair: role_sort_key(pair[0]))
        for role, child_key in children_sorted:
            parts.append(f"{role}:{expr_fp(child_key)}")

        rep = "|".join(parts)
        fp = stable_hash(rep)
        memo_expr_repr[key] = rep
        memo_expr_fp[key] = fp
        return fp

    # Force fingerprints for all expr nodes.
    for key in expr_keys:
        expr_fp(key)

    decl_group_map: dict[str, list[dict[str, Any]]] = defaultdict(list)
    decl_count_with_roots = 0
    for decl_key in decl_keys:
        root_map = decl_roots.get(decl_key, {})
        type_root = root_map.get("type_root", "")
        value_root = root_map.get("value_root", "")
        if not type_root and not value_root:
            continue
        decl_count_with_roots += 1
        type_hash = expr_fp(type_root) if type_root else "-"
        value_hash = expr_fp(value_root) if value_root else "-"
        rep = f"type:{type_hash}|value:{value_hash}"
        fp = stable_hash(rep)
        decl_node = node_by_key.get(decl_key, {})
        decl_name = str(decl_node.get("decl", decl_key))
        decl_group_map[fp].append(
            {
                "decl_key": decl_key,
                "decl": decl_name,
                "type_root": type_root,
                "value_root": value_root,
                "type_hash": type_hash,
                "value_hash": value_hash,
            }
        )

    decl_groups: list[dict[str, Any]] = []
    for fp, rows in decl_group_map.items():
        if len(rows) < max(2, int(args.min_decl_group_size)):
            continue
        decls = sorted({str(r.get("decl", "")) for r in rows if str(r.get("decl", ""))})
        decl_groups.append(
            {
                "fingerprint": fp,
                "group_size": len(decls),
                "declarations": decls,
                "members": rows,
            }
        )
    decl_groups.sort(key=lambda r: (-int(r.get("group_size", 0)), str(r.get("fingerprint", ""))))

    expr_occurrence_count: dict[str, int] = defaultdict(int)
    expr_decls: dict[str, set[str]] = defaultdict(set)
    expr_sample: dict[str, dict[str, Any]] = {}
    for key in expr_keys:
        fp = memo_expr_fp.get(key, "")
        if not fp:
            continue
        node = node_by_key.get(key, {})
        decl_name = str(node.get("decl", "")).strip()
        expr_occurrence_count[fp] += 1
        if decl_name:
            expr_decls[fp].add(decl_name)
        if fp not in expr_sample:
            expr_sample[fp] = node

    repeated_subgraphs: list[dict[str, Any]] = []
    min_occ = max(2, int(args.min_subgraph_occurrences))
    for fp, occ in expr_occurrence_count.items():
        if occ < min_occ:
            continue
        sample = expr_sample.get(fp, {})
        decls = sorted(expr_decls.get(fp, set()))
        repeated_subgraphs.append(
            {
                "fingerprint": fp,
                "expr_tag": str(sample.get("exprTag", "")),
                "occurrences": occ,
                "declaration_count": len(decls),
                "sample_decl": str(sample.get("decl", "")),
                "sample_info": str(sample.get("info", "")),
                "sample_deBruijnIdx": sample.get("deBruijnIdx"),
                "sample_repr_prefix": memo_expr_repr.get(str(sample.get("_key", "")), "")[:200],
                "declarations": decls[:50],
            }
        )
    repeated_subgraphs.sort(
        key=lambda r: (
            -int(r.get("declaration_count", 0)),
            -int(r.get("occurrences", 0)),
            str(r.get("fingerprint", "")),
        )
    )

    unique_expr_fps = len(expr_occurrence_count)
    unique_decl_fps = len(decl_group_map)

    stats = {
        "decl_nodes": len(decl_keys),
        "expr_nodes": len(expr_keys),
        "declarations_with_roots": decl_count_with_roots,
        "unique_expr_fingerprints": unique_expr_fps,
        "unique_decl_fingerprints": unique_decl_fps,
        "expr_dedup_factor": round((len(expr_keys) / unique_expr_fps), 6) if unique_expr_fps else 0.0,
        "decl_dedup_factor": round((decl_count_with_roots / unique_decl_fps), 6) if unique_decl_fps else 0.0,
        "decl_equivalence_groups": len(decl_groups),
        "repeated_subgraphs": len(repeated_subgraphs),
    }

    top_decl_groups = decl_groups[: max(0, int(args.top_decl_groups))]
    top_subgraphs = repeated_subgraphs[: max(0, int(args.top_subgraphs))]

    report = {
        "generated_at": utc_now_iso(),
        "input_dir": rel_path(input_dir),
        "const_mode": str(args.const_mode),
        "thresholds": {
            "min_decl_group_size": int(args.min_decl_group_size),
            "min_subgraph_occurrences": int(args.min_subgraph_occurrences),
            "top_decl_groups": int(args.top_decl_groups),
            "top_subgraphs": int(args.top_subgraphs),
        },
        "source_meta": source_meta,
        "stats": stats,
        "top_decl_groups": top_decl_groups,
        "top_subgraphs": top_subgraphs,
    }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")

    md_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(
        build_markdown(report, top_decl_groups=top_decl_groups, top_subgraphs=top_subgraphs),
        encoding="utf-8",
    )

    print(
        f"[ExprAlphaDedup] input={input_dir} decl_groups={len(decl_groups)} "
        f"repeated_subgraphs={len(repeated_subgraphs)} wrote {json_out} and {md_out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
