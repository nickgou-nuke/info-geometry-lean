#!/usr/bin/env python3
"""Extract an SCC-compressed causal cone packet for LLM ensemble infusion.

This is the "epistemic reactor" context builder:

    declaration
      -> SCC anchor
      -> compressed backward/forward cone
      -> deduplicated quotient edges
      -> raw Lean witness excerpts
      -> ensemble prompt payload

The output is navigation/prompt context only.  It is not proof authority and
must descend back to raw Lean files before any theorem claim is promoted.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.infra.arango_causal_chiral_cone_prompt import (  # noqa: E402
    add_source_excerpts,
    arango_target,
    component_members,
    resolve_decl,
    traverse_cone,
)
from tools.infra.arango_dag_algorithms import run_aql  # noqa: E402
from tools.infra.arango_raw_infotree_ingest import ArangoTarget  # noqa: E402


SCHEMA = "info_geometry.epistemic_reactor.compressed_cone.v1"

AUTHORITY_BOUNDARY = {
    "packet_is_navigation_only": True,
    "scc_compression_is_not_proof": True,
    "ensemble_consensus_is_not_proof": True,
    "hive_purified_is_not_lean_checked": True,
    "lean_remains_proof_authority": True,
    "audits_remain_admission_authority": True,
}

FORBIDDEN_AUTHORITY_CLAIMS = [
    "graph_is_proof",
    "scc_component_is_theorem",
    "ensemble_consensus_is_truth",
    "hive_purified_is_admitted",
    "triple_is_theorem",
]


def stable_hash(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def component_id(row: dict[str, Any]) -> str:
    return str(row.get("_id") or "")


def component_key(row: dict[str, Any]) -> str:
    return str(row.get("_key") or component_id(row).split("/", 1)[-1])


def compact_component(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": row.get("_id"),
        "key": row.get("_key"),
        "representative": row.get("representative"),
        "size": row.get("size") or row.get("member_count") or row.get("cardinality"),
        "dominant_layer": row.get("dominant_layer") or row.get("layer"),
        "dominant_depth": row.get("dominant_depth") or row.get("depth"),
        "labels": row.get("labels") or [],
    }


def dedup_component_edges(
    target: ArangoTarget,
    *,
    component_ids: list[str],
    component_edges: str,
) -> list[dict[str, Any]]:
    if not component_ids:
        return []
    rows = run_aql(
        target,
        """
        FOR e IN @@edges
          FILTER e._from IN @component_ids && e._to IN @component_ids
          COLLECT from = e._from, to = e._to INTO grouped
          LET edge_keys = grouped[*].e._key
          LET flow_polarities = UNIQUE(grouped[*].e.flow_polarity)
          LET roles = UNIQUE(grouped[*].e.role)
          RETURN {
            from: from,
            to: to,
            multiplicity: LENGTH(grouped),
            source_multiplicity: SUM(grouped[*].e.multiplicity),
            witness_count: SUM(grouped[*].e.witness_count),
            edge_keys: edge_keys,
            flow_polarities: flow_polarities,
            roles: roles
          }
        """,
        {"@edges": component_edges, "component_ids": component_ids},
    )
    return rows


def group_member_counts(member_groups: list[dict[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for group in member_groups:
        counts[str(group.get("component_id") or "")] = len(group.get("members") or [])
    return counts


def build_ensemble_payload(
    *,
    target_decl: str,
    temperatures: list[float],
    samples: int,
    compressed_components: list[dict[str, Any]],
    compressed_edges: list[dict[str, Any]],
    source_excerpts: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "schema": "info_geometry.epistemic_reactor.ensemble_payload.v1",
        "authority": "navigation",
        "target_decl": target_decl,
        "sampling": {
            "samples": samples,
            "temperatures": temperatures,
            "consensus_threshold": 0.9,
        },
        "context": {
            "compressed_components": compressed_components,
            "compressed_edges": compressed_edges,
            "source_excerpts": source_excerpts,
        },
        "instructions": [
            "Use SCC components as compressed context, not as proof.",
            "Regenerate only candidate Lean proof plans or local patch suggestions.",
            "Every proposed theorem step must name raw Lean declarations or source excerpts.",
            "Do not promote ensemble consensus above proposal authority.",
            "Classify missing analytic content as an explicit hypothesis packet.",
        ],
        "required_descent": "raw_lean_witness",
        "forbidden_authority_claims": list(FORBIDDEN_AUTHORITY_CLAIMS),
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }


def shadow_merge_template(packet_id: str) -> dict[str, Any]:
    return {
        "schema": "info_geometry.epistemic_reactor.shadow_merge_template.v1",
        "authority": "documentation_only",
        "packet_id": packet_id,
        "aql_shape": [
            "FOR item IN @purified_batch",
            "  LET node_key = SHA256(CONCAT(item.original_id, item.purification_round, item.content_hash))",
            "  UPSERT { _key: node_key }",
            "  INSERT { _key: node_key, authority: 'hive_purified', packet_id: @packet_id }",
            "  UPDATE { refinement_count: OLD.refinement_count + 1, last_refined: DATE_NOW() }",
            "  IN hive_purified_shadow_nodes",
            "  INSERT { _from: item.original_ref, _to: CONCAT('hive_purified_shadow_nodes/', node_key), type: 'REFINED_INTO' }",
            "  INTO hive_purified_shadow_edges",
        ],
        "forbidden_authority_claims": list(FORBIDDEN_AUTHORITY_CLAIMS),
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }


def parse_temperatures(raw: str) -> list[float]:
    values = [float(piece.strip()) for piece in raw.split(",") if piece.strip()]
    if not values:
        raise SystemExit("--temperatures must contain at least one value")
    return values


def build_packet(args: argparse.Namespace) -> dict[str, Any]:
    repo_root = args.repo_root.resolve()
    target = arango_target(repo_root)
    resolved = resolve_decl(
        target,
        decl=args.decl,
        raw_nodes=args.raw_nodes_collection,
        overlay_nodes=args.overlay_nodes_collection,
        overlay_edges=args.overlay_edges_collection,
    )
    apex_node = resolved["node"]
    apex_component = resolved["component"]
    seed_id = str(apex_component["_id"])

    backward = traverse_cone(
        target,
        seed_component_id=seed_id,
        component_edges=args.component_edges_collection,
        direction="OUTBOUND",
        depth=args.backward_depth,
        limit=args.cone_limit,
    )
    forward = traverse_cone(
        target,
        seed_component_id=seed_id,
        component_edges=args.component_edges_collection,
        direction="INBOUND",
        depth=args.forward_depth,
        limit=args.cone_limit,
    )

    components_by_id: dict[str, dict[str, Any]] = {seed_id: apex_component}
    for row in backward + forward:
        component = row.get("component") or {}
        cid = component_id(component)
        if cid:
            components_by_id[cid] = component

    component_ids = sorted(components_by_id)
    compressed_components = [compact_component(components_by_id[cid]) for cid in component_ids]
    compressed_edges = dedup_component_edges(
        target,
        component_ids=component_ids,
        component_edges=args.component_edges_collection,
    )

    members = component_members(
        target,
        component_ids=component_ids,
        raw_nodes=args.raw_nodes_collection,
        overlay_edges=args.overlay_edges_collection,
        per_component_limit=args.members_per_component,
    )
    member_counts = group_member_counts(members)
    excerpts = add_source_excerpts(
        members,
        repo_root=repo_root,
        radius=args.source_radius,
        max_total=args.max_source_excerpts,
    )
    temperatures = parse_temperatures(args.temperatures)
    ensemble_payload = build_ensemble_payload(
        target_decl=args.decl,
        temperatures=temperatures,
        samples=args.samples,
        compressed_components=compressed_components,
        compressed_edges=compressed_edges,
        source_excerpts=excerpts,
    )

    packet_core = {
        "schema": SCHEMA,
        "authority": "navigation",
        "target_decl": args.decl,
        "apex": {
            "raw_node_id": apex_node.get("_id"),
            "raw_node_key": apex_node.get("_key"),
            "component_id": apex_component.get("_id"),
            "component_key": apex_component.get("_key"),
            "representative": apex_component.get("representative"),
        },
        "compression": {
            "method": "scc_quotient_cone",
            "cycle_handling": "SCCs are already compressed into topology/arango_dag components",
            "edge_deduplication": "component edge endpoints are collected with multiplicity",
        },
        "orientation": {
            "edge_orientation": "declaration -> dependency",
            "backward_cone": "OUTBOUND prerequisites/dependencies from the apex SCC",
            "forward_cone": "INBOUND users/consequences into the apex SCC",
        },
        "parameters": {
            "backward_depth": args.backward_depth,
            "forward_depth": args.forward_depth,
            "cone_limit": args.cone_limit,
            "members_per_component": args.members_per_component,
            "source_radius": args.source_radius,
            "samples": args.samples,
            "temperatures": temperatures,
        },
        "compressed_components": compressed_components,
        "compressed_edges": compressed_edges,
        "member_counts_sampled": member_counts,
        "source_excerpts": excerpts,
        "ensemble_payload": ensemble_payload,
        "forbidden_authority_claims": list(FORBIDDEN_AUTHORITY_CLAIMS),
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }
    packet_id = stable_hash(packet_core)
    packet_core["id"] = packet_id
    packet_core["shadow_merge_template"] = shadow_merge_template(packet_id)
    packet_core["counts"] = {
        "compressed_components": len(compressed_components),
        "compressed_edges": len(compressed_edges),
        "member_groups": len(members),
        "source_excerpts": len(excerpts),
    }
    return packet_core


def render_markdown(packet: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Epistemic Reactor Compressed Cone")
    lines.append("")
    lines.append(f"- Target: `{packet['target_decl']}`")
    lines.append(f"- Authority: `{packet['authority']}`")
    lines.append(f"- Apex component: `{packet['apex'].get('component_key')}`")
    lines.append("")
    lines.append("## Boundary")
    lines.append("")
    for key, value in packet["authority_boundary"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    lines.append("## Counts")
    lines.append("")
    for key, value in packet["counts"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    lines.append("## Compressed components")
    lines.append("")
    for row in packet["compressed_components"][:50]:
        lines.append(
            f"- `{row.get('key')}` rep `{row.get('representative')}` "
            f"layer `{row.get('dominant_layer')}`"
        )
    lines.append("")
    lines.append("## Deduplicated edges")
    lines.append("")
    for row in packet["compressed_edges"][:80]:
        lines.append(
            f"- `{row.get('from')}` -> `{row.get('to')}` "
            f"multiplicity `{row.get('multiplicity')}`"
        )
    lines.append("")
    lines.append("## Ensemble rule")
    lines.append("")
    lines.append("Ensemble output may become `hive_purified` shadow material only.")
    lines.append("It is not Lean proof authority until raw Lean verification succeeds.")
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--decl", required=True, help="Fully qualified Lean declaration name.")
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--raw-nodes-collection", default="raw_info_nodes")
    parser.add_argument("--overlay-nodes-collection", default="topology_overlay")
    parser.add_argument("--overlay-edges-collection", default="topology_overlay_edges")
    parser.add_argument("--component-edges-collection", default="arango_dag_component_edges")
    parser.add_argument("--backward-depth", type=int, default=4)
    parser.add_argument("--forward-depth", type=int, default=4)
    parser.add_argument("--cone-limit", type=int, default=180)
    parser.add_argument("--members-per-component", type=int, default=4)
    parser.add_argument("--source-radius", type=int, default=8)
    parser.add_argument("--max-source-excerpts", type=int, default=80)
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument("--temperatures", default="0.0,0.2,0.5,0.8")
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--md-out", type=Path)
    args = parser.parse_args(argv)

    if args.backward_depth < 0 or args.forward_depth < 0:
        raise SystemExit("cone depths must be non-negative")
    if args.cone_limit <= 0:
        raise SystemExit("--cone-limit must be positive")
    if args.samples <= 0:
        raise SystemExit("--samples must be positive")

    packet = build_packet(args)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        print(json.dumps(packet, indent=2, sort_keys=True))
    if args.md_out:
        args.md_out.parent.mkdir(parents=True, exist_ok=True)
        args.md_out.write_text(render_markdown(packet), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

