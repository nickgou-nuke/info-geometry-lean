#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict, deque
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    _ROOT = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(_ROOT))
    from tools.infra import causal_cone_spectrum as cone
    from tools.pathing import repo_root
else:
    from tools.infra import causal_cone_spectrum as cone
    from tools.pathing import repo_root


SCHEMA = "info_geometry.causal_chiral_prompt_packet.v1"


def iter_jsonl(path: Path):
    if not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            try:
                yield json.loads(line)
            except json.JSONDecodeError:
                continue


def load_decl_index(path: Path) -> dict[str, dict[str, Any]]:
    by_name: dict[str, dict[str, Any]] = {}
    for row in iter_jsonl(path):
        name = row.get("name")
        if isinstance(name, str) and name:
            by_name[name] = row
    return by_name


def load_expr_fingerprints(path: Path) -> dict[str, dict[str, Any]]:
    by_name: dict[str, dict[str, Any]] = {}
    for row in iter_jsonl(path):
        name = row.get("decl_name")
        if isinstance(name, str) and name:
            by_name[name] = row
    return by_name


def repo_path(value: Any, root: Path) -> Path | None:
    if not isinstance(value, str) or not value:
        return None
    path = Path(value)
    if path.is_absolute():
        return path
    return root / path


def source_excerpt(decl: dict[str, Any], root: Path, radius: int = 8) -> dict[str, Any]:
    path = repo_path(decl.get("file"), root)
    line = decl.get("line")
    if path is None or not isinstance(line, int) or not path.exists():
        return {"available": False, "file": str(path) if path else "", "line": line, "text": ""}
    lines = path.read_text(encoding="utf-8").splitlines()
    start = max(1, line - radius)
    end = min(len(lines), line + radius)
    text = "\n".join(f"{idx}: {lines[idx - 1]}" for idx in range(start, end + 1))
    return {"available": True, "file": str(path), "line": line, "start": start, "end": end, "text": text}


def weak_cone_bfs(apex_cid: str, comp_by_id: dict[str, dict[str, Any]]) -> dict[str, int]:
    dist = {apex_cid: 0}
    queue = deque([apex_cid])
    while queue:
        u = queue.popleft()
        row = comp_by_id.get(u, {})
        neighbors = list(row.get("dependencyComponentIds", [])) + list(row.get("reverseDependentComponentIds", []))
        for v in neighbors:
            if isinstance(v, str) and v in comp_by_id and v not in dist:
                dist[v] = dist[u] + 1
                queue.append(v)
    return dist


def shell_sample(
    dist: dict[str, int],
    comp_by_id: dict[str, dict[str, Any]],
    decl_index: dict[str, dict[str, Any]],
    *,
    max_shells: int,
    per_shell: int,
) -> list[dict[str, Any]]:
    by_shell: dict[int, list[str]] = defaultdict(list)
    for cid, depth in dist.items():
        by_shell[depth].append(cid)
    rows: list[dict[str, Any]] = []
    for depth in sorted(by_shell)[:max_shells]:
        members: list[dict[str, Any]] = []
        for cid in sorted(by_shell[depth], key=lambda c: comp_by_id.get(c, {}).get("representative", c))[:per_shell]:
            comp = comp_by_id.get(cid, {})
            rep = str(comp.get("representative", cid))
            decl = decl_index.get(rep, {})
            members.append(
                {
                    "componentId": cid,
                    "representative": rep,
                    "member_count": len(cone._iter_component_members(comp)),
                    "kind": decl.get("kind", ""),
                    "module": decl.get("module", ""),
                    "file": decl.get("file", ""),
                    "line": decl.get("line", None),
                }
            )
        rows.append({"shell": depth, "size": len(by_shell[depth]), "sample": members})
    return rows


def resolve_apex(
    name: str,
    comp_by_id: dict[str, dict[str, Any]],
    comp_by_rep: dict[str, dict[str, Any]],
    comp_by_member: dict[str, dict[str, Any]],
) -> tuple[str, dict[str, Any]]:
    if name in comp_by_id:
        return name, comp_by_id[name]
    if name in comp_by_rep:
        row = comp_by_rep[name]
        return str(row["componentId"]), row
    if name in comp_by_member:
        row = comp_by_member[name]
        return str(row["componentId"]), row
    raise SystemExit(f"[prompt] could not resolve declaration/component apex: {name}")


def expr_context(name: str, expr_fingerprints: dict[str, dict[str, Any]]) -> dict[str, Any]:
    row = expr_fingerprints.get(name)
    if not row:
        return {
            "available": False,
            "mode": "unavailable",
            "authority": "no expression fingerprint or exact ExprArango root found in current artifacts",
        }
    return {
        "available": True,
        "mode": "metadata_fingerprint_proxy",
        "authority": "diagnostic only; not exact De Bruijn/AST traversal",
        "feature_counts": row.get("feature_counts", {}),
        "feature_kind": row.get("feature_kind", {}),
        "flags": row.get("flags", {}),
        "provenance": row.get("provenance", {}),
        "hashes": {
            "level_0_decl_hash": row.get("level_0_decl_hash"),
            "level_1_local_hash": row.get("level_1_local_hash"),
        },
    }


def render_prompt(packet: dict[str, Any]) -> str:
    apex = packet["apex"]
    lines = [
        "# Causal-chiral proof prompt packet",
        "",
        "Authority boundary: graph/cone/expression diagnostics are navigation only. Lean remains proof authority.",
        "",
        "## Apex",
        "",
        f"- declaration: `{apex['decl']}`",
        f"- component: `{apex['componentId']}`",
        f"- module: `{apex.get('module', '')}`",
        f"- kind: `{apex.get('kind', '')}`",
        "",
    ]
    excerpt = packet.get("source_excerpt", {})
    if excerpt.get("available"):
        lines.extend(["```lean", str(excerpt.get("text", "")), "```", ""])

    cone_summary = packet["cone_summary"]
    lines.extend(
        [
            "## Cone summary",
            "",
            f"- past/prerequisite cone size: `{cone_summary['past_cone_size']}`",
            f"- future/impact cone size: `{cone_summary['future_cone_size']}`",
            f"- weak basin size: `{cone_summary['weak_basin_size']}`",
            f"- max past shell: `{cone_summary['max_past_shell']}`",
            f"- binding witnesses: `{cone_summary['binding_witnesses']}`",
            f"- declaration mass: `{cone_summary['declaration_mass']}`",
            f"- binding mass: `{cone_summary['binding_mass']}`",
            "",
            "## Past cone sample",
            "",
        ]
    )
    for shell in packet["past_cone"]["shells"]:
        lines.append(f"### shell {shell['shell']} / size {shell['size']}")
        for item in shell["sample"]:
            lines.append(f"- `{item['representative']}` ({item.get('kind', '')})")
        lines.append("")

    lines.extend(["## Future cone sample", ""])
    for shell in packet["future_cone"]["shells"]:
        lines.append(f"### shell {shell['shell']} / size {shell['size']}")
        for item in shell["sample"]:
            lines.append(f"- `{item['representative']}` ({item.get('kind', '')})")
        lines.append("")

    expr = packet.get("expr_context", {})
    lines.extend(
        [
            "## Expression context",
            "",
            f"- mode: `{expr.get('mode', 'unavailable')}`",
            f"- authority: {expr.get('authority', '')}",
            f"- feature counts: `{json.dumps(expr.get('feature_counts', {}), sort_keys=True)}`",
            "",
            "## Task",
            "",
            "Use the source excerpt and cone samples to propose or repair a Lean proof for the apex declaration.",
            "Do not treat graph proximity, shell position, spectral mass, or expression fingerprints as proof.",
            "Every mathematical relation suggested by the packet must descend to an owner theorem or be encoded as an explicit hypothesis.",
            "",
        ]
    )
    return "\n".join(lines)


def build_packet(args: argparse.Namespace) -> dict[str, Any]:
    root = repo_root()
    payload, comp_by_id, comp_by_rep, comp_by_member = cone.load_structure(root / args.structure)
    cone.verify_edge_pair_consistency(comp_by_id)
    cone.verify_edge_semantics(payload, comp_by_id)

    depth_tags = cone.load_depth_tags(root / args.depth_tags)
    decl_index = load_decl_index(root / args.decls)
    expr_fingerprints = load_expr_fingerprints(root / args.expr_fingerprints)

    apex_cid, apex_row = resolve_apex(args.decl, comp_by_id, comp_by_rep, comp_by_member)
    apex_rep = str(apex_row.get("representative", args.decl))
    apex_decl = decl_index.get(args.decl) or decl_index.get(apex_rep) or {}

    sig_cache = cone.precompute_signatures(comp_by_id, depth_tags)
    own_parity_cache = cone.precompute_own_parities(comp_by_id, depth_tags)
    analysis = cone.analyze_apex(apex_cid, comp_by_id, depth_tags, sig_cache, own_parity_cache)

    past = cone.past_cone_bfs(apex_cid, comp_by_id)
    future = cone.forward_cone_bfs(apex_cid, comp_by_id)
    weak = weak_cone_bfs(apex_cid, comp_by_id)

    return {
        "schema": SCHEMA,
        "authority": {
            "graph_is_navigation_only": True,
            "diagnostics_are_not_certificates": True,
            "lean_remains_proof_authority": True,
        },
        "graph_source": {
            "scope": "SCC-condensed declaration DAG from current artifacts",
            "structure": args.structure,
            "depth_tags": args.depth_tags,
            "decls": args.decls,
            "expr_fingerprints": args.expr_fingerprints,
            "orientation": "declaration -> dependency; past follows dependencyComponentIds",
        },
        "apex": {
            "decl": args.decl,
            "representative": apex_rep,
            "componentId": apex_cid,
            "kind": apex_decl.get("kind", ""),
            "module": apex_decl.get("module", ""),
            "file": apex_decl.get("file", ""),
            "line": apex_decl.get("line", None),
        },
        "source_excerpt": source_excerpt(apex_decl, root, radius=args.source_radius),
        "cone_summary": {
            "past_cone_size": len(past),
            "future_cone_size": len(future),
            "weak_basin_size": len(weak),
            "max_past_shell": max(past.values()) if past else 0,
            "binding_witnesses": analysis.get("binding_witnesses", 0),
            "declaration_mass": analysis.get("declaration_mass", 0.0),
            "binding_mass": analysis.get("binding_mass", 0.0),
            "boundary_nodes": analysis.get("boundary_nodes", 0),
        },
        "past_cone": {
            "definition": "components reachable from apex by dependencyComponentIds",
            "shells": shell_sample(
                past, comp_by_id, decl_index, max_shells=args.max_shells, per_shell=args.per_shell
            ),
        },
        "future_cone": {
            "definition": "components reachable from apex by reverseDependentComponentIds",
            "shells": shell_sample(
                future, comp_by_id, decl_index, max_shells=args.max_shells, per_shell=args.per_shell
            ),
        },
        "weak_basin": {
            "definition": "components reachable from apex ignoring direction",
            "size": len(weak),
        },
        "hodge_chiral_context": {
            "available": False,
            "mode": "not_materialized_by_this_builder",
            "authority": "use bounded Hodge/chiral tools as diagnostics only, then descend to Lean owners",
        },
        "expr_context": expr_context(args.decl, expr_fingerprints),
        "diagnostic_samples": {
            "binding_witness_sample": analysis.get("binding_witness_sample", []),
            "boundary_sample": analysis.get("boundary_sample", []),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Build a causal/chiral prompt packet for one Lean declaration.")
    parser.add_argument("--decl", required=True, help="Declaration name, representative, or component id.")
    parser.add_argument("--structure", default="artifacts/dag/structural-topology.json")
    parser.add_argument("--depth-tags", default="artifacts/dag/representation-depth-tags.json")
    parser.add_argument("--decls", default="artifacts/dag/index/decls.jsonl")
    parser.add_argument("--expr-fingerprints", default="artifacts/dag/index/expr_fingerprints.jsonl")
    parser.add_argument("--json-out", type=Path, default=Path("reports/dag/causal-chiral-prompt-packet.json"))
    parser.add_argument("--md-out", type=Path, default=Path("reports/dag/causal-chiral-prompt-packet.md"))
    parser.add_argument("--max-shells", type=int, default=4)
    parser.add_argument("--per-shell", type=int, default=8)
    parser.add_argument("--source-radius", type=int, default=8)
    args = parser.parse_args()

    root = repo_root()
    packet = build_packet(args)

    json_out = args.json_out if args.json_out.is_absolute() else root / args.json_out
    md_out = args.md_out if args.md_out.is_absolute() else root / args.md_out
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_out.write_text(render_prompt(packet), encoding="utf-8")
    print(f"[prompt] wrote {json_out}")
    print(f"[prompt] wrote {md_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
