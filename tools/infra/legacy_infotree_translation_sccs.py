#!/usr/bin/env python3
"""
LEGACY — infotree declaration-level translation SCC dedup.

This tool operates on the output of legacy_infotree_dual_space.py
(dual_features.jsonl, dual_edges.jsonl, subprogram_fingerprints.jsonl),
NOT on the canonical wire/gate topology from wire_topology_transform.py.

For the canonical expression-level dedup, use:
  - wire_topology_transform.py        (wire/gate incidence graph)
  - materialize_translation_candidates.py  (translation candidates + verified edges)
  - generate_translation_dedup_report.py   (read-only audit report)

This legacy tool is kept for infotree-level analysis only.
Its SCCs are declaration-pattern equivalence candidates induced by exact hash
buckets over the derived feature representation. They are dedup/audit candidates,
NOT proof-level equivalence classes.

Uses the exact dual feature space to:
1. Find candidate equivalent declarations (same shapeHash or translationHash)
2. Check candidates by comparing the derived declaration-feature hashes
3. Build directed derived-pattern translation edges
4. Compute SCCs to get dedup classes
5. Output dedup report
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


DEFAULT_INPUT_DIR = "artifacts/infotree/legacy-dual"
DEFAULT_OUTPUT_DIR = "reports/dag/legacy-infotree-translation-sccs"


def sha256_hex(payload: str) -> str:
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


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


def compute_sccs_directed(
    nodes: list[str],
    edges: list[tuple[str, str]],
) -> list[list[str]]:
    """
    Compute strongly connected components using Tarjan's algorithm.
    Pure Python — no networkx dependency needed.
    """
    index_counter = [0]
    stack: list[str] = []
    lowlink: dict[str, int] = {}
    index: dict[str, int] = {}
    on_stack: dict[str, bool] = {}
    sccs: list[list[str]] = []

    # Build adjacency list
    adj: dict[str, list[str]] = defaultdict(list)
    for src, dst in edges:
        adj[src].append(dst)

    def strongconnect(v: str):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True

        for w in adj.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.append(w)
                if w == v:
                    break
            sccs.append(scc)

    for v in nodes:
        if v not in index:
            strongconnect(v)

    return sccs


def build_translation_sccs(
    fingerprints: list[dict[str, Any]],
    dual_edges: list[dict[str, Any]],
    features: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    """
    Build derived-pattern translation edges and compute SCC candidate classes.

    Strategy:
    1. Group declarations by shapeHash (exact structural match)
    2. Group declarations by translationHash (translation-invariant match)
    3. For each group, check candidates share the same kind and dep pattern
    4. Add derived bidirectional edges within each group
    5. Compute SCCs on the derived-pattern translation graph
    """

    # Build feature lookup
    feature_by_key: dict[str, dict[str, Any]] = {}
    for f in features:
        feature_by_key[f.get("_key", "")] = f

    # Build subprogram -> features map
    subprogram_features: dict[str, set[str]] = defaultdict(set)
    for e in dual_edges:
        sub_name = e.get("_from", "").replace("subprograms/", "")
        feat_key = e.get("_to", "").replace("dual_features/", "")
        if sub_name and feat_key:
            subprogram_features[sub_name].add(feat_key)

    # Group by shapeHash (exact structural match)
    shape_groups: dict[str, list[str]] = defaultdict(list)
    for fp in fingerprints:
        shape_hash = fp.get("shapeHash", "")
        if shape_hash:
            shape_groups[shape_hash].append(fp["name"])

    # Group by translationHash (translation-invariant match)
    translation_groups: dict[str, list[str]] = defaultdict(list)
    for fp in fingerprints:
        trans_hash = fp.get("translationHash", "")
        if trans_hash:
            translation_groups[trans_hash].append(fp["name"])

    # Build derived-pattern translation edges. These are not Lean/kernel proofs.
    verified_edges: list[dict[str, Any]] = []
    edge_set: set[tuple[str, str]] = set()

    def add_verified_edge(src: str, dst: str, edge_type: str, detail: str):
        key = (src, dst)
        if key not in edge_set and src != dst:
            edge_set.add(key)
            verified_edges.append({
                "_from": f"subprograms/{src}",
                "_to": f"subprograms/{dst}",
                "predicate": "derived_pattern_translation",
                "edge_type": edge_type,
                "detail": detail,
                "translationHash": sha256_hex(f"translation:{src}|{dst}|{edge_type}"),
                "verificationTier": "legacy_infotree_pattern",
                "leanVerified": False,
                "safeForAutoRewrite": False,
            })

    # Stage 1: shapeHash groups (exact structural match)
    shape_edge_count = 0
    for shape_hash, members in shape_groups.items():
        if len(members) < 2:
            continue
        # Verify: all members should have same kind
        kinds = set()
        for name in members:
            fp = next((f for f in fingerprints if f["name"] == name), {})
            kinds.add(fp.get("kind", ""))
        if len(kinds) > 1:
            continue  # Different kinds — not a valid translation

        # Add bidirectional edges
        for i in range(len(members)):
            for j in range(i + 1, len(members)):
                add_verified_edge(members[i], members[j], "exact_shape", f"shapeHash={shape_hash[:16]}")
                add_verified_edge(members[j], members[i], "exact_shape", f"shapeHash={shape_hash[:16]}")
                shape_edge_count += 2

    # Stage 2: translationHash groups (translation-invariant match)
    trans_edge_count = 0
    for trans_hash, members in translation_groups.items():
        if len(members) < 2:
            continue
        # Verify: all members should have same kind
        kinds = set()
        modules = set()
        for name in members:
            fp = next((f for f in fingerprints if f["name"] == name), {})
            kinds.add(fp.get("kind", ""))
            modules.add(fp.get("module", ""))
        if len(kinds) > 1:
            continue  # Different kinds — skip

        # Only add edges between different modules (cross-module patterns)
        if len(modules) < 2:
            continue

        # Add bidirectional edges (limit to avoid explosion)
        max_members = 50  # Limit group size
        limited_members = members[:max_members]
        for i in range(len(limited_members)):
            for j in range(i + 1, len(limited_members)):
                # Only connect declarations from different modules
                fp_i = next((f for f in fingerprints if f["name"] == limited_members[i]), {})
                fp_j = next((f for f in fingerprints if f["name"] == limited_members[j]), {})
                if fp_i.get("module", "") != fp_j.get("module", ""):
                    add_verified_edge(limited_members[i], limited_members[j], "translation_invariant",
                                      f"translationHash={trans_hash[:16]}")
                    add_verified_edge(limited_members[j], limited_members[i], "translation_invariant",
                                      f"translationHash={trans_hash[:16]}")
                    trans_edge_count += 2

    # Compute SCCs
    all_nodes = list(set(fp["name"] for fp in fingerprints))
    edge_list = [(e["_from"].replace("subprograms/", ""), e["_to"].replace("subprograms/", ""))
                 for e in verified_edges]

    print(f"  Computing SCCs on {len(all_nodes)} nodes, {len(edge_list)} edges...")
    sccs = compute_sccs_directed(all_nodes, edge_list)

    # Build SCC nodes
    scc_nodes: list[dict[str, Any]] = []
    scc_members_map: dict[str, str] = {}  # member name -> scc key

    for i, scc in enumerate(sccs):
        scc_key = f"scc_{i:06d}"
        scc_size = len(scc)

        # Get representative (prefer theorem > def > others, then alphabetical)
        scc_fps = [next((f for f in fingerprints if f["name"] == name), {}) for name in scc]
        scc_fps = [fp for fp in scc_fps if fp]

        if not scc_fps:
            continue

        # Representative selection: prefer theorems, then shortest name
        representative = sorted(
            scc_fps,
            key=lambda fp: (
                0 if fp.get("kind") == "theorem" else 1,
                fp.get("dep_count", 0),
                len(fp.get("name", "")),
                fp.get("name", ""),
            )
        )[0]["name"]

        scc_node = {
            "_key": scc_key,
            "kind": "scc",
            "size": scc_size,
            "representative": representative,
            "members": scc,
            "member_kinds": dict(Counter(fp.get("kind", "?") for fp in scc_fps)),
            "member_modules": dict(Counter(fp.get("module", "?") for fp in scc_fps).most_common(5)),
            "is_trivial": scc_size == 1,
        }
        scc_nodes.append(scc_node)

        for name in scc:
            scc_members_map[name] = scc_key

    # Add SCC membership to verified edges
    for e in verified_edges:
        src = e["_from"].replace("subprograms/", "")
        dst = e["_to"].replace("subprograms/", "")
        e["src_scc"] = scc_members_map.get(src, "")
        e["dst_scc"] = scc_members_map.get(dst, "")

    print(f"  Shape edges: {shape_edge_count}")
    print(f"  Translation edges: {trans_edge_count}")
    print(f"  Total verified edges: {len(verified_edges)}")
    print(f"  SCCs: {len(scc_nodes)}")
    non_trivial = [s for s in scc_nodes if not s["is_trivial"]]
    print(f"  Non-trivial SCCs (size > 1): {len(non_trivial)}")
    if non_trivial:
        sizes = sorted([s["size"] for s in non_trivial], reverse=True)
        print(f"  Top SCC sizes: {sizes[:10]}")

    return verified_edges, scc_nodes, scc_members_map


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")


def build_dedup_report(
    scc_nodes: list[dict[str, Any]],
    fingerprints: list[dict[str, Any]],
) -> str:
    """Build a Markdown report of derived-pattern candidate classes."""

    lines: list[str] = []
    lines.append("# Legacy Infotree Translation-Pattern SCC Report")
    lines.append("")
    lines.append(f"- Generated: `{datetime.now(timezone.utc).isoformat()}`")
    lines.append(f"- Total SCCs: {len(scc_nodes)}")

    non_trivial = [s for s in scc_nodes if not s["is_trivial"]]
    lines.append(f"- Non-trivial SCCs (size > 1): {len(non_trivial)}")
    lines.append("")

    # Summary by kind
    lines.append("## SCC Size Distribution")
    lines.append("")
    size_dist = Counter(s["size"] for s in non_trivial)
    lines.append("| Size | Count |")
    lines.append("|------|------:|")
    for size, count in sorted(size_dist.items()):
        lines.append(f"| {size} | {count} |")
    lines.append("")

    # Top non-trivial SCCs
    lines.append("## Top Non-Trivial SCCs")
    lines.append("")
    lines.append("| Rank | Size | Representative | Kinds | Modules |")
    lines.append("|------|------|----------------|-------|---------|")

    sorted_sccs = sorted(non_trivial, key=lambda s: -s["size"])
    for i, scc in enumerate(sorted_sccs[:50], 1):
        kinds = ", ".join(f"{k}:{v}" for k, v in list(scc["member_kinds"].items())[:3])
        modules = ", ".join(list(scc["member_modules"].keys())[:3])
        lines.append(f"| {i} | {scc['size']} | `{scc['representative'][:60]}` | {kinds} | {modules} |")

    lines.append("")

    # Sample members of top SCCs
    lines.append("## Sample SCC Members (Top 10)")
    lines.append("")
    for i, scc in enumerate(sorted_sccs[:10], 1):
        lines.append(f"### SCC {i} (size={scc['size']})")
        lines.append(f"- Representative: `{scc['representative']}`")
        lines.append(f"- Kinds: {scc['member_kinds']}")
        lines.append(f"- Modules: {list(scc['member_modules'].keys())}")
        lines.append("- Members:")
        for member in scc["members"][:20]:
            lines.append(f"  - `{member}`")
        if len(scc["members"]) > 20:
            lines.append(f"  - ... and {len(scc['members']) - 20} more")
        lines.append("")

    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Build legacy infotree derived-pattern translation SCC candidates"
    )
    ap.add_argument("--input-dir", default=DEFAULT_INPUT_DIR)
    ap.add_argument("--output-dir", default=DEFAULT_OUTPUT_DIR)
    args = ap.parse_args()

    input_dir = normalize_user_path(args.input_dir, (repo_root() / DEFAULT_INPUT_DIR))
    output_dir = normalize_user_path(args.output_dir, (repo_root() / DEFAULT_OUTPUT_DIR))

    fingerprints_path = input_dir / "subprogram_fingerprints.jsonl"
    dual_edges_path = input_dir / "dual_edges.jsonl"
    features_path = input_dir / "dual_features.jsonl"

    if not fingerprints_path.exists():
        print(f"[dedup-scc] input not found: {fingerprints_path}", file=sys.stderr)
        print("[dedup-scc] run generate_expr_dual_space.py first", file=sys.stderr)
        return 1

    print(f"[dedup-scc] reading {fingerprints_path}")
    fingerprints = iter_jsonl(fingerprints_path)
    print(f"[dedup-scc] reading {dual_edges_path}")
    dual_edges = iter_jsonl(dual_edges_path)
    print(f"[dedup-scc] reading {features_path}")
    features = iter_jsonl(features_path)

    print(f"[dedup-scc] building translation SCCs from {len(fingerprints)} fingerprints...")
    verified_edges, scc_nodes, scc_members = build_translation_sccs(
        fingerprints, dual_edges, features
    )

    print(f"[dedup-scc] writing output to {output_dir}")
    write_jsonl(output_dir / "verified_translation_edges.jsonl", verified_edges)
    write_jsonl(output_dir / "dedup_scc_nodes.jsonl", scc_nodes)

    # Build and write report
    report = build_dedup_report(scc_nodes, fingerprints)
    (output_dir / "dedup_scc_report.md").write_text(report, encoding="utf-8")

    # Summary stats
    non_trivial = [s for s in scc_nodes if not s["is_trivial"]]
    total_in_non_trivial = sum(s["size"] for s in non_trivial)

    print(f"\n[dedup-scc] === Summary ===")
    print(f"  Verified translation edges: {len(verified_edges)}")
    print(f"  SCCs: {len(scc_nodes)}")
    print(f"  Non-trivial SCCs: {len(non_trivial)}")
    print(f"  Declarations in non-trivial SCCs: {total_in_non_trivial}")
    print(f"  Output: {output_dir}/dedup_scc_report.md")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
