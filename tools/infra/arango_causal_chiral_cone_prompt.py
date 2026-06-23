#!/usr/bin/env python3
"""Emit a causal/chiral cone prompt packet for one Lean declaration.

This tool is a prompt-shaping layer over the existing Arango-DAG overlays.
It does not prove anything.  It performs the graph-theoretic navigation step:

    raw Lean declaration
      -> SCC component anchor
      -> backward dependency cone (OUTBOUND in declaration->dependency DAG)
      -> forward consequence cone (INBOUND in declaration->dependency DAG)
      -> optional Hodge/chiral/Dirac/motif/process overlays
      -> raw source snippets for Lean-grounded prompt input

Lean remains the proof authority.  The emitted packet is intended as LLM
"diamond anvil" context: dependencies squeeze from one side, consequences from
the other, and the apex declaration remains the formal target.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.infra.arango_dag_algorithms import run_aql  # noqa: E402
from tools.infra.arango_env import (  # noqa: E402
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.arango_gravity_context import source_excerpt  # noqa: E402
from tools.infra.arango_raw_infotree_ingest import ArangoTarget  # noqa: E402


SCHEMA = "info_geometry.causal_chiral_cone_prompt.v1"


def arango_target(repo_root: Path) -> ArangoTarget:
    load_repo_arango_env(repo_root)
    return ArangoTarget(
        endpoint=arango_endpoint().rstrip("/"),
        database=arango_database(),
        username=arango_username(),
        password=arango_password(),
    )


def resolve_decl(
    target: ArangoTarget,
    *,
    decl: str,
    raw_nodes: str,
    overlay_nodes: str,
    overlay_edges: str,
) -> dict[str, Any]:
    rows = run_aql(
        target,
        """
        FOR n IN @@raw_nodes
          FILTER n.raw_name == @decl
            OR n.name == @decl
            OR (HAS(n, "decl") && n.decl.name == @decl)
          LIMIT 1
          LET memberships = (
            FOR m IN @@overlay_edges
              FILTER m.role == "member_of_scc" && m._from == n._id
              LIMIT 1
              FOR c IN @@overlay_nodes
                FILTER c._id == m._to
                RETURN { component: c, membership: m }
          )
          RETURN {
            node: n,
            component: memberships[0].component,
            membership: memberships[0].membership
          }
        """,
        {
            "@raw_nodes": raw_nodes,
            "@overlay_nodes": overlay_nodes,
            "@overlay_edges": overlay_edges,
            "decl": decl,
        },
    )
    if not rows:
        raise SystemExit(f"declaration not found in {raw_nodes}: {decl}")
    row = rows[0]
    print(f"DEBUG: row = {row}")
    if not row.get("component"):
        raise SystemExit(f"declaration has no SCC membership in {overlay_edges}: {decl}")
    return row


def traverse_cone(
    target: ArangoTarget,
    *,
    seed_component_id: str,
    component_edges: str,
    direction: str,
    depth: int,
    limit: int,
) -> list[dict[str, Any]]:
    if direction not in {"OUTBOUND", "INBOUND"}:
        raise ValueError(f"invalid traversal direction: {direction}")
    if depth <= 0:
        return []
    return run_aql(
        target,
        f"""
        FOR v, e, p IN 1..@depth {direction} @seed @@component_edges
          OPTIONS {{ bfs: true, uniqueVertices: "global" }}
          LIMIT @limit
          RETURN {{
            component: v,
            edge: e,
            depth: LENGTH(p.edges),
            path_keys: p.vertices[*]._key,
            path_ids: p.vertices[*]._id
          }}
        """,
        {
            "@component_edges": component_edges,
            "seed": seed_component_id,
            "depth": depth,
            "limit": limit,
        },
    )


def component_members(
    target: ArangoTarget,
    *,
    component_ids: list[str],
    raw_nodes: str,
    overlay_edges: str,
    per_component_limit: int,
) -> list[dict[str, Any]]:
    if not component_ids:
        return []
    return run_aql(
        target,
        """
        FOR cid IN @component_ids
          LET rows = (
            FOR m IN @@overlay_edges
              FILTER m.role == "member_of_scc" && m._to == cid
              FOR n IN @@raw_nodes
                FILTER n._id == m._from
                SORT n.raw_name ASC, n.name ASC, n._key ASC
                LIMIT @per_component_limit
                RETURN { node: n, membership: m }
          )
          RETURN { component_id: cid, members: rows }
        """,
        {
            "@raw_nodes": raw_nodes,
            "@overlay_edges": overlay_edges,
            "component_ids": component_ids,
            "per_component_limit": per_component_limit,
        },
    )


def overlay_rows(
    target: ArangoTarget,
    *,
    component_keys: list[str],
    include_hodge: bool,
    include_chiral: bool,
    include_dirac: bool,
    include_motifs: bool,
    include_process: bool,
    include_dominators: bool,
    limit: int,
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    if include_chiral:
        out["chiral"] = run_aql(
            target,
            """
            FOR c IN arango_dag_chiral
              FILTER c.component_key IN @keys
              LIMIT @limit
              RETURN c
            """,
            {"keys": component_keys, "limit": limit},
        )
    if include_hodge:
        out["hodge"] = run_aql(
            target,
            """
            FOR h IN arango_dag_hodge
              FILTER h._key == "hodge_summary" || h.operator == "laplacian0"
              LIMIT @limit
              RETURN h
            """,
            {"limit": limit},
        )
    if include_dirac:
        out["dirac"] = run_aql(
            target,
            """
            FOR d IN arango_dag_dirac
              LIMIT @limit
              RETURN d
            """,
            {"limit": limit},
        )
    if include_motifs:
        out["motifs"] = run_aql(
            target,
            """
            FOR m IN arango_dag_motifs
              FILTER LENGTH(INTERSECTION(m.mapping_keys, @keys)) > 0
              LIMIT @limit
              RETURN m
            """,
            {"keys": component_keys, "limit": limit},
        )
    if include_process:
        out["process_flows"] = run_aql(
            target,
            """
            FOR f IN arango_dag_process_flows
              FILTER f.source_key IN @keys || f.target_key IN @keys
              LIMIT @limit
              RETURN f
            """,
            {"keys": component_keys, "limit": limit},
        )
    if include_dominators:
        out["dominators"] = run_aql(
            target,
            """
            FOR d IN arango_dag_dominators
              FILTER d.component_key IN @keys
              LIMIT @limit
              RETURN d
            """,
            {"keys": component_keys, "limit": limit},
        )
    return out


def node_name(node: dict[str, Any]) -> str:
    decl = node.get("decl") if isinstance(node.get("decl"), dict) else {}
    return str(node.get("raw_name") or node.get("name") or decl.get("name") or node.get("_key"))


def add_source_excerpts(
    member_groups: list[dict[str, Any]],
    *,
    repo_root: Path,
    radius: int,
    max_total: int,
) -> list[dict[str, Any]]:
    excerpts: list[dict[str, Any]] = []
    for group in member_groups:
        cid = group.get("component_id")
        for member in group.get("members") or []:
            node = member.get("node") or {}
            excerpt = source_excerpt(node, repo_root, radius)
            if not excerpt:
                continue
            excerpts.append(
                {
                    "component_id": cid,
                    "name": node_name(node),
                    "file": node.get("file") or (node.get("decl") or {}).get("file"),
                    "line": node.get("line") or (node.get("decl") or {}).get("line"),
                    "source_excerpt": excerpt,
                }
            )
            if len(excerpts) >= max_total:
                return excerpts
    return excerpts


def render_markdown(packet: dict[str, Any]) -> str:
    lines: list[str] = []
    apex = packet["apex"]
    lines.append("# Causal Chiral Cone Prompt Packet")
    lines.append("")
    lines.append("## Apex")
    lines.append("")
    lines.append(f"- Declaration: `{apex['name']}`")
    lines.append(f"- Raw node: `{apex['raw_node_id']}`")
    lines.append(f"- SCC component: `{apex['component_key']}`")
    lines.append("")
    lines.append("## Graph semantics")
    lines.append("")
    lines.append("- DAG orientation: `declaration -> dependency`.")
    lines.append("- Backward cone: `OUTBOUND` from apex SCC, i.e. prerequisites.")
    lines.append("- Forward cone: `INBOUND` to apex SCC, i.e. users/consequences.")
    lines.append("- Hodge/chiral/Dirac rows are navigation priors, not proof.")
    lines.append("- Every mathematical claim must descend back to Lean source.")
    lines.append("")
    for label in ["backward_cone", "forward_cone"]:
        rows = packet[label]
        lines.append(f"## {label.replace('_', ' ').title()}")
        lines.append("")
        for row in rows[:50]:
            component = row.get("component") or {}
            lines.append(
                f"- depth `{row.get('depth')}` component `{component.get('_key')}` "
                f"rep `{component.get('representative')}`"
            )
        if not rows:
            lines.append("- empty")
        lines.append("")
    lines.append("## Source excerpts")
    lines.append("")
    for item in packet.get("source_excerpts", [])[:40]:
        lines.append(f"### `{item.get('name')}`")
        lines.append("")
        excerpt = item.get("source_excerpt") or {}
        path = excerpt.get("path") or item.get("file")
        lines.append(f"- File: `{path}`")
        lines.append(f"- Line: `{item.get('line')}`")
        lines.append("")
        lines.append("```lean")
        for line in excerpt.get("lines") or []:
            lines.append(f"{line.get('line')}: {line.get('text')}")
        lines.append("```")
        lines.append("")
    lines.append("## LLM instruction")
    lines.append("")
    lines.append(
        "Use the backward cone as prerequisites, the apex as the target, and "
        "the forward cone as consequence pressure. Generate only Lean code or "
        "proof plans that can be checked by Lean; do not treat graph proximity "
        "or Hodge/chiral overlays as proof."
    )
    lines.append("")
    return "\n".join(lines)


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

    component_by_id: dict[str, dict[str, Any]] = {seed_id: apex_component}
    for row in backward + forward:
        component = row.get("component") or {}
        cid = component.get("_id")
        if cid:
            component_by_id[str(cid)] = component
    component_ids = list(component_by_id)
    component_keys = [str(c.get("_key")) for c in component_by_id.values() if c.get("_key")]

    members = component_members(
        target,
        component_ids=component_ids,
        raw_nodes=args.raw_nodes_collection,
        overlay_edges=args.overlay_edges_collection,
        per_component_limit=args.members_per_component,
    )
    excerpts = add_source_excerpts(
        members,
        repo_root=repo_root,
        radius=args.source_radius,
        max_total=args.max_source_excerpts,
    )

    overlays = overlay_rows(
        target,
        component_keys=component_keys,
        include_hodge=args.include_hodge,
        include_chiral=args.include_chiral,
        include_dirac=args.include_dirac,
        include_motifs=args.include_motifs,
        include_process=args.include_process,
        include_dominators=args.include_dominators,
        limit=args.overlay_limit,
    )

    return {
        "schema": SCHEMA,
        "apex": {
            "name": args.decl,
            "raw_node_id": apex_node.get("_id"),
            "raw_node_key": apex_node.get("_key"),
            "component_id": apex_component.get("_id"),
            "component_key": apex_component.get("_key"),
            "representative": apex_component.get("representative"),
            "node": apex_node,
            "component": apex_component,
        },
        "orientation": {
            "edge_orientation": "declaration -> dependency",
            "backward_cone": "OUTBOUND prerequisites/dependencies from the apex SCC",
            "forward_cone": "INBOUND users/consequences into the apex SCC",
            "graph_is_navigation_not_proof": True,
        },
        "parameters": {
            "backward_depth": args.backward_depth,
            "forward_depth": args.forward_depth,
            "cone_limit": args.cone_limit,
            "members_per_component": args.members_per_component,
            "source_radius": args.source_radius,
        },
        "backward_cone": backward,
        "forward_cone": forward,
        "component_ids": component_ids,
        "component_keys": component_keys,
        "members": members,
        "source_excerpts": excerpts,
        "overlays": overlays,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--decl", required=True, help="Fully qualified Lean declaration/proposition name.")
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--raw-nodes-collection", default="raw_info_nodes")
    parser.add_argument("--overlay-nodes-collection", default="topology_overlay")
    parser.add_argument("--overlay-edges-collection", default="topology_overlay_edges")
    parser.add_argument("--component-edges-collection", default="arango_dag_component_edges")
    parser.add_argument("--backward-depth", type=int, default=6)
    parser.add_argument("--forward-depth", type=int, default=6)
    parser.add_argument("--cone-limit", type=int, default=250)
    parser.add_argument("--members-per-component", type=int, default=5)
    parser.add_argument("--source-radius", type=int, default=8)
    parser.add_argument("--max-source-excerpts", type=int, default=80)
    parser.add_argument("--overlay-limit", type=int, default=200)
    parser.add_argument("--include-hodge", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--include-chiral", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--include-dirac", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("--include-motifs", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--include-process", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--include-dominators", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--md-out", type=Path)
    args = parser.parse_args(argv)

    packet = build_packet(args)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(packet, indent=2, sort_keys=True), encoding="utf-8")
    else:
        print(json.dumps(packet, indent=2, sort_keys=True))
    if args.md_out:
        args.md_out.parent.mkdir(parents=True, exist_ok=True)
        args.md_out.write_text(render_markdown(packet), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
