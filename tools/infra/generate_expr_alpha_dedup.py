#!/usr/bin/env python3
"""
Compute alpha-equivalence structural dedup over ExprArangoExport graphs,
producing declaration-level and subgraph-level compression evidence,
plus RDF-style de Bruijn incidence triples for the memory graph.

Outputs:
  - JSON report (declaration equivalence groups, repeated subgraphs, stats)
  - Markdown summary
  - ig_triples.jsonl  (RDF-style triples: subject, predicate, object, hash)
  - ig_binder_incidence.jsonl (binder incidence edges with SHA-256 hashes)
"""

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
DEFAULT_TRIPLES_OUT = "reports/dag/ig_triples.jsonl"
DEFAULT_BINDER_INCIDENCE_OUT = "reports/dag/ig_binder_incidence.jsonl"
DEFAULT_ENRICHED_NODES_OUT = "reports/dag/ig_nodes_enriched.jsonl"
DEFAULT_ENRICHED_EDGES_OUT = "reports/dag/ig_edges_enriched.jsonl"

ROLE_ORDER = {
    "type": 0,
    "value": 1,
    "fn": 2,
    "arg": 3,
    "body": 4,
    "expr": 5,
}


# [lossless-compact] utc_now_iso folded into igf.common.time_utils.utc_now_iso
from igf.common.time_utils import utc_now_iso


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Compute alpha-equivalence structural dedup over ExprArangoExport graphs "
            "(ig_nodes.jsonl / ig_edges.jsonl), producing declaration-level and subgraph-level "
            "compression evidence plus RDF-style de Bruijn incidence triples."
        )
    )
    ap.add_argument("--input-dir", default=DEFAULT_INPUT_DIR)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--triples-out", default=DEFAULT_TRIPLES_OUT)
    ap.add_argument("--binder-incidence-out", default=DEFAULT_BINDER_INCIDENCE_OUT)
    ap.add_argument("--enriched-nodes-out", default=DEFAULT_ENRICHED_NODES_OUT)
    ap.add_argument("--enriched-edges-out", default=DEFAULT_ENRICHED_EDGES_OUT)
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
        "--emit-triples",
        action="store_true",
        default=True,
        help="Emit RDF-style incidence triples (default: True).",
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


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def parse_key(raw: str) -> str:
    value = str(raw).strip()
    if "/" in value:
        return value.split("/", 1)[1]
    return value


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


def sha256_hex(payload: str) -> str:
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


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


def compute_debruijn_node_hash(node: dict[str, Any]) -> str:
    """
    Compute a stable SHA-256 hash for a bvar node capturing its de Bruijn identity.

    Hash input: debruijn:node|<decl>|<sectionTag>|<path>|<idx>
    """
    decl = str(node.get("decl", ""))
    section_tag = str(node.get("sectionTag", ""))
    path = str(node.get("path", ""))
    idx = node.get("deBruijnIdx")
    if idx is None:
        idx = -1
    payload = f"debruijn:node|{decl}|{section_tag}|{path}|{idx}"
    return sha256_hex(payload)


def compute_debruijn_incidence_hash(
    source_node: dict[str, Any],
    target_node: dict[str, Any],
    idx: int,
) -> str:
    """
    Compute a stable SHA-256 hash for a bound_by incidence edge.

    Hash input: debruijn:incidence|<decl>|<sectionTag>|<source_key>|<target_key>|<idx>
    """
    decl = str(source_node.get("decl", ""))
    section_tag = str(source_node.get("sectionTag", ""))
    source_key = str(source_node.get("_key", ""))
    target_key = str(target_node.get("_key", ""))
    payload = f"debruijn:incidence|{decl}|{section_tag}|{source_key}|{target_key}|{idx}"
    return sha256_hex(payload)


def compute_binder_incidence_hash(
    binder_key: str,
    bvar_keys: list[str],
    decl: str,
) -> str:
    """
    Compute a stable SHA-256 hash for a binder's full incidence neighborhood.

    This captures the triple: binder --[binds]--> {bvar_1, bvar_2, ...}
    enabling clustering of binders by their binding pattern.

    Hash input: binder:incidence|<decl>|<binder_key>|<sorted bvar keys>
    """
    sorted_bvars = sorted(bvar_keys)
    payload = f"binder:incidence|{decl}|{binder_key}|{','.join(sorted_bvars)}"
    return sha256_hex(payload)


def compute_alpha_local_hash(
    node_key: str,
    children_hashes: list[tuple[str, str]],
    expr_tag: str,
    info: str,
) -> str:
    """
    Compute a local alpha-equivalence hash for an expression node.

    This is the structural hash of the node's immediate neighborhood,
    invariant under alpha-renaming (de Bruijn indices already encode
    binding structure name-independently).

    Hash input: alpha:local|<expr_tag>|<info>|<role1:hash1>|...
    """
    parts = [f"alpha:local|{expr_tag}|{info}"]
    for role, child_hash in sorted(children_hashes, key=lambda x: role_sort_key(x[0])):
        parts.append(f"{role}:{child_hash}")
    return sha256_hex("|".join(parts))


def build_triples(
    nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    node_by_key: dict[str, dict[str, Any]],
    ast_children: dict[str, list[tuple[str, str]]],
    decl_roots: dict[str, dict[str, str]],
) -> list[dict[str, Any]]:
    """
    Build RDF-style triples from the expression graph.

    Triple types:
      - (decl, declares, expr_root)       -- declaration roots
      - (parent, has_child:expr_role, child)  -- AST edges
      - (bvar_node, bound_by:deBruijnIdx, binder_node)  -- de Bruijn binding
      - (binder, binds, bvar_node)        -- reverse binding incidence
    """
    triples: list[dict[str, Any]] = []

    for edge in edges:
        kind = str(edge.get("kind", "")).strip()
        role = str(edge.get("role", "")).strip()
        src = parse_key(str(edge.get("_from", "")))
        dst = parse_key(str(edge.get("_to", "")))
        if not src or not dst:
            continue

        src_node = node_by_key.get(src, {})
        dst_node = node_by_key.get(dst, {})

        if kind == "decl_root":
            triple = {
                "subject": src,
                "predicate": f"declares:{role}",
                "object": dst,
                "triple_hash": sha256_hex(f"triple|{src}|declares:{role}|{dst}"),
                "kind": "decl_root",
                "decl": str(edge.get("decl", "")),
            }
            triples.append(triple)

        elif kind == "ast":
            triple = {
                "subject": src,
                "predicate": f"has_child:{role}",
                "object": dst,
                "triple_hash": sha256_hex(f"triple|{src}|has_child:{role}|{dst}"),
                "kind": "ast",
                "decl": str(edge.get("decl", "")),
            }
            triples.append(triple)

        elif kind == "bind" and role == "bound_by":
            idx = edge.get("deBruijnIdx")
            if idx is None:
                idx = src_node.get("deBruijnIdx", -1)
            if not isinstance(idx, int):
                idx = -1

            # Forward: bvar -> binder
            incidence_hash = compute_debruijn_incidence_hash(
                src_node, dst_node, idx
            )
            triple_fwd = {
                "subject": src,
                "predicate": f"bound_by:deBruijnIdx={idx}",
                "object": dst,
                "triple_hash": sha256_hex(
                    f"triple|{src}|bound_by:deBruijnIdx={idx}|{dst}"
                ),
                "kind": "deBruijn_binding",
                "deBruijnIdx": idx,
                "incidenceHash": incidence_hash,
                "decl": str(edge.get("decl", "")),
            }
            triples.append(triple_fwd)

            # Reverse: binder -> bvar (incidence duality)
            triple_rev = {
                "subject": dst,
                "predicate": f"binds:deBruijnIdx={idx}",
                "object": src,
                "triple_hash": sha256_hex(
                    f"triple|{dst}|binds:deBruijnIdx={idx}|{src}"
                ),
                "kind": "deBruijn_incidence",
                "deBruijnIdx": idx,
                "incidenceHash": incidence_hash,
                "decl": str(edge.get("decl", "")),
            }
            triples.append(triple_rev)

        elif kind == "const_ref":
            triple = {
                "subject": src,
                "predicate": "references_const",
                "object": dst,
                "triple_hash": sha256_hex(f"triple|{src}|references_const|{dst}"),
                "kind": "const_ref",
                "decl": str(edge.get("decl", "")),
            }
            triples.append(triple)

    return triples


def build_binder_incidence_index(
    edges: list[dict[str, Any]],
    node_by_key: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    """
    Build a binder-centric incidence index.

    For each binder node, collect all bvar nodes bound by it and compute
    a binderIncidenceHash capturing the full binding neighborhood.
    """
    # Map: binder_key -> list of (bvar_key, idx)
    binder_to_bvars: dict[str, list[tuple[str, int]]] = defaultdict(list)

    for edge in edges:
        kind = str(edge.get("kind", "")).strip()
        role = str(edge.get("role", "")).strip()
        if kind != "bind" or role != "bound_by":
            continue
        src = parse_key(str(edge.get("_to", "")))   # binder
        dst = parse_key(str(edge.get("_from", "")))  # bvar
        if not src or not dst:
            continue
        idx = edge.get("deBruijnIdx", -1)
        if not isinstance(idx, int):
            idx = -1
        binder_to_bvars[src].append((dst, idx))

    records: list[dict[str, Any]] = []
    for binder_key, bvar_list in binder_to_bvars.items():
        bvar_keys = [bk for bk, _ in bvar_list]
        binder_node = node_by_key.get(binder_key, {})
        decl = str(binder_node.get("decl", ""))

        incidence_hash = compute_binder_incidence_hash(
            binder_key, bvar_keys, decl
        )

        records.append({
            "binder_key": binder_key,
            "decl": decl,
            "binder_expr_tag": str(binder_node.get("exprTag", "")),
            "binder_info": str(binder_node.get("info", "")),
            "bound_bvar_count": len(bvar_list),
            "bound_bvars": [
                {"bvar_key": bk, "deBruijnIdx": idx}
                for bk, idx in sorted(bvar_list, key=lambda x: x[1])
            ],
            "binderIncidenceHash": incidence_hash,
        })

    records.sort(key=lambda r: (r["decl"], r["binder_key"]))
    return records


def build_enriched_raw_rows(
    nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    node_by_key: dict[str, dict[str, Any]],
    alpha_local_by_key: dict[str, str],
    binder_incidence: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Return raw graph rows enriched with deterministic SHA-256 identity fields.

    This does not mutate the authoritative exporter output.  It creates a
    post-processed evidence layer where process-local Lean hashes are replaced
    by stable content hashes suitable for Arango/RDF/vector memory.
    """
    binder_hash_by_key = {
        str(row.get("binder_key", "")): str(row.get("binderIncidenceHash", ""))
        for row in binder_incidence
        if row.get("binder_key") and row.get("binderIncidenceHash")
    }

    enriched_nodes: list[dict[str, Any]] = []
    for node in nodes:
        out = dict(node)
        key = str(out.get("_key", ""))
        if key in alpha_local_by_key:
            out["alphaLocalHash"] = alpha_local_by_key[key]
        if str(out.get("exprTag", "")) == "bvar":
            out["deBruijnHash"] = compute_debruijn_node_hash(out)
        enriched_nodes.append(out)

    enriched_edges: list[dict[str, Any]] = []
    for edge in edges:
        out = dict(edge)
        kind = str(out.get("kind", "")).strip()
        role = str(out.get("role", "")).strip()
        if kind == "bind" and role == "bound_by":
            src = parse_key(str(out.get("_from", "")))
            dst = parse_key(str(out.get("_to", "")))
            src_node = node_by_key.get(src, {})
            dst_node = node_by_key.get(dst, {})
            idx = out.get("deBruijnIdx")
            if idx is None:
                idx = src_node.get("deBruijnIdx", -1)
            if not isinstance(idx, int):
                idx = -1
            out["incidenceHash"] = compute_debruijn_incidence_hash(src_node, dst_node, idx)
            out["binderIncidenceHash"] = binder_hash_by_key.get(dst, "")
        enriched_edges.append(out)

    return enriched_nodes, enriched_edges


def build_markdown(
    report: dict[str, Any],
    *,
    top_decl_groups: list[dict[str, Any]],
    top_subgraphs: list[dict[str, Any]],
    triple_count: int = 0,
    binder_incidence_count: int = 0,
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
    lines.append(f"- rdf_triples_emitted: `{triple_count}`")
    lines.append(f"- binder_incidence_records: `{binder_incidence_count}`")
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
        lines.append("|---|---|---:|---|---|")
        for idx, row in enumerate(top_subgraphs, start=1):
            lines.append(
                f"| {idx} | `{row.get('expr_tag', '')}` | {int(row.get('occurrences', 0))} | "
                f"{int(row.get('declaration_count', 0))} | `{str(row.get('fingerprint', ''))[:16]}` |"
            )
    lines.append("")
    lines.append("## De Bruijn Incidence Summary")
    lines.append("")
    lines.append(f"- Total RDF triples emitted: `{triple_count}`")
    lines.append(f"- Binder incidence records: `{binder_incidence_count}`")
    lines.append("")
    lines.append("Triple format (RDF-style):")
    lines.append("  subject | predicate | object | triple_hash | kind | decl")
    lines.append("")
    lines.append("Binder incidence format:")
    lines.append("  binder_key | decl | bound_bvar_count | binderIncidenceHash")
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


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def main() -> int:
    args = parse_args()
    input_dir = normalize_user_path(args.input_dir, (repo_root() / DEFAULT_INPUT_DIR))
    json_out = normalize_user_path(args.json_out, (repo_root() / DEFAULT_JSON_OUT))
    md_out = normalize_user_path(args.md_out, (repo_root() / DEFAULT_MD_OUT))
    triples_out = normalize_user_path(args.triples_out, (repo_root() / DEFAULT_TRIPLES_OUT))
    binder_incidence_out = normalize_user_path(
        args.binder_incidence_out, (repo_root() / DEFAULT_BINDER_INCIDENCE_OUT)
    )
    enriched_nodes_out = normalize_user_path(
        args.enriched_nodes_out, (repo_root() / DEFAULT_ENRICHED_NODES_OUT)
    )
    enriched_edges_out = normalize_user_path(
        args.enriched_edges_out, (repo_root() / DEFAULT_ENRICHED_EDGES_OUT)
    )

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
                "rdf_triples_emitted": 0,
                "binder_incidence_records": 0,
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

    # --- Compute expression fingerprints (alpha-equivalence aware) ---
    memo_expr_fp: dict[str, str] = {}
    memo_expr_repr: dict[str, str] = {}
    memo_alpha_local: dict[str, str] = {}

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

        child_hashes_for_alpha: list[tuple[str, str]] = []
        for role, child_key in children_sorted:
            child_hash = expr_fp(child_key)
            parts.append(f"{role}:{child_hash}")
            child_hashes_for_alpha.append((role, child_hash))

        rep = "|".join(parts)
        fp = stable_hash(rep)
        memo_expr_fp[key] = fp
        memo_expr_repr[key] = rep

        # Compute alpha-local hash for this node
        expr_tag = str(node.get("exprTag", "")).strip()
        info = str(node.get("info", "")).strip()
        memo_alpha_local[key] = compute_alpha_local_hash(
            key, child_hashes_for_alpha, expr_tag, info
        )

        return fp

    # Force fingerprints for all expr nodes.
    for key in expr_keys:
        expr_fp(key)

    # --- Declaration equivalence groups ---
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

    # --- Repeated subgraphs ---
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
                "sample_alphaLocalHash": memo_alpha_local.get(str(sample.get("_key", "")), ""),
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

    # --- Build RDF triples ---
    triples: list[dict[str, Any]] = []
    if args.emit_triples:
        triples = build_triples(nodes, edges, node_by_key, ast_children, decl_roots)

    # --- Build binder incidence index ---
    binder_incidence: list[dict[str, Any]] = []
    if args.emit_triples:
        binder_incidence = build_binder_incidence_index(edges, node_by_key)

    enriched_nodes, enriched_edges = build_enriched_raw_rows(
        nodes,
        edges,
        node_by_key,
        memo_alpha_local,
        binder_incidence,
    )

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
        "rdf_triples_emitted": len(triples),
        "binder_incidence_records": len(binder_incidence),
        "enriched_nodes_emitted": len(enriched_nodes),
        "enriched_edges_emitted": len(enriched_edges),
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
        build_markdown(
            report,
            top_decl_groups=top_decl_groups,
            top_subgraphs=top_subgraphs,
            triple_count=len(triples),
            binder_incidence_count=len(binder_incidence),
        ),
        encoding="utf-8",
    )

    if triples:
        write_jsonl(triples_out, triples)

    if binder_incidence:
        write_jsonl(binder_incidence_out, binder_incidence)

    if enriched_nodes:
        write_jsonl(enriched_nodes_out, enriched_nodes)

    if enriched_edges:
        write_jsonl(enriched_edges_out, enriched_edges)

    print(
        f"[ExprAlphaDedup] input={input_dir} decl_groups={len(decl_groups)} "
        f"repeated_subgraphs={len(repeated_subgraphs)} "
        f"triples={len(triples)} binder_incidence={len(binder_incidence)} "
        f"wrote {json_out} {md_out} {triples_out} {binder_incidence_out} "
        f"{enriched_nodes_out} {enriched_edges_out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
