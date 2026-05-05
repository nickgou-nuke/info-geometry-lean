#!/usr/bin/env python3
"""Join proof forests with Arango causal cone packets.

This builds a two-sided proof-geometry artifact:

  backward owner/dependency cone
      glued through declarations/files/references
  local proof apex states
      tactic/goal nodes
  forward proof forest
      goal branches and closures

The result is prompt/training/navigation context, not proof authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.bidirectional_proof_cone.v1"


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    if not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                yield row


def stable_hash(*parts: Any) -> str:
    text = json.dumps(parts, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    return hashlib.sha1(text.encode("utf-8")).hexdigest()[:16]


def normalize(text: Any) -> str:
    return re.sub(r"\s+", " ", str(text or "")).strip()


def add_node(nodes: dict[str, dict[str, Any]], node: dict[str, Any]) -> str:
    nodes.setdefault(str(node["id"]), node)
    return str(node["id"])


def add_edge(edges: list[dict[str, Any]], src: str, dst: str, role: str, **extra: Any) -> None:
    edges.append({"from": src, "to": dst, "role": role, **extra})


def decl_name_from_node(node: dict[str, Any]) -> str:
    decl = node.get("decl") if isinstance(node.get("decl"), dict) else {}
    return normalize(node.get("raw_name") or node.get("name") or decl.get("name") or node.get("_key"))


def decl_file_from_node(node: dict[str, Any]) -> str:
    decl = node.get("decl") if isinstance(node.get("decl"), dict) else {}
    return normalize(node.get("file") or decl.get("file"))


def component_key(component: dict[str, Any]) -> str:
    return normalize(component.get("_key") or component.get("key") or component.get("component_key") or component.get("representative"))


def cone_component_node(component: dict[str, Any]) -> dict[str, Any]:
    key = component_key(component)
    return {
        "id": f"scc:{stable_hash(key)}",
        "kind": "scc_component",
        "component_key": key,
        "representative": component.get("representative"),
        "layer": component.get("rep_layer") or component.get("layer"),
        "raw": component,
    }


def cone_decl_node(raw_node: dict[str, Any]) -> dict[str, Any]:
    name = decl_name_from_node(raw_node)
    return {
        "id": f"decl:{stable_hash(name)}",
        "kind": "declaration",
        "name": name,
        "file": decl_file_from_node(raw_node),
        "line": raw_node.get("line") or (raw_node.get("decl") or {}).get("line") if isinstance(raw_node.get("decl"), dict) else raw_node.get("line"),
        "raw": raw_node,
    }


def proof_node_id(node: dict[str, Any]) -> str:
    return "proofnode:" + stable_hash(node.get("id"), node.get("kind"), node.get("text"), node.get("name"))


def load_cone_packet(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def build_cone_indexes(cone: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], dict[str, str], dict[str, list[str]]]:
    """Return cone nodes, declaration-name index, and file index."""
    nodes: dict[str, dict[str, Any]] = {}
    decl_by_name: dict[str, str] = {}
    decls_by_file: dict[str, list[str]] = {}

    apex = cone.get("apex") if isinstance(cone.get("apex"), dict) else {}
    component = apex.get("component") if isinstance(apex.get("component"), dict) else {}
    raw_node = apex.get("node") if isinstance(apex.get("node"), dict) else {}
    if component:
        add_node(nodes, cone_component_node(component))
    if raw_node:
        did = add_node(nodes, cone_decl_node(raw_node))
        name = nodes[did].get("name")
        file = nodes[did].get("file")
        if name:
            decl_by_name[str(name)] = did
        if file:
            decls_by_file.setdefault(str(file), []).append(did)

    for label, direction in (("backward_cone", "backward_dependency"), ("forward_cone", "forward_user")):
        for row in cone.get(label) or []:
            if not isinstance(row, dict):
                continue
            comp = row.get("component")
            if isinstance(comp, dict):
                cid = add_node(nodes, cone_component_node(comp))
                nodes[cid]["cone_direction"] = direction

    for group in cone.get("members") or []:
        if not isinstance(group, dict):
            continue
        comp_id = normalize(group.get("component_id"))
        for member in group.get("members") or []:
            if not isinstance(member, dict):
                continue
            raw = member.get("node")
            if not isinstance(raw, dict):
                continue
            did = add_node(nodes, cone_decl_node(raw))
            nodes[did]["component_id"] = comp_id
            name = nodes[did].get("name")
            file = nodes[did].get("file")
            if name:
                decl_by_name[str(name)] = did
            if file:
                decls_by_file.setdefault(str(file), []).append(did)

    for item in cone.get("source_excerpts") or []:
        if not isinstance(item, dict):
            continue
        name = normalize(item.get("name"))
        path = normalize(item.get("file") or (item.get("source_excerpt") or {}).get("path") if isinstance(item.get("source_excerpt"), dict) else item.get("file"))
        if not name:
            continue
        did = f"decl:{stable_hash(name)}"
        add_node(
            nodes,
            {
                "id": did,
                "kind": "declaration",
                "name": name,
                "file": path,
                "line": item.get("line"),
                "source_excerpt": item.get("source_excerpt"),
            },
        )
        decl_by_name[name] = did
        if path:
            decls_by_file.setdefault(path, []).append(did)

    return nodes, decl_by_name, decls_by_file


def build_bidirectional_cone(forest: dict[str, Any], cone: dict[str, Any], *, apex_decl: str = "") -> dict[str, Any]:
    nodes: dict[str, dict[str, Any]] = {}
    edges: list[dict[str, Any]] = []

    proof_root = add_node(
        nodes,
        {
            "id": f"bidirectional:{stable_hash(forest.get('id'), cone.get('apex'))}",
            "kind": "bidirectional_root",
            "proof_forest_id": forest.get("id"),
            "cone_schema": cone.get("schema"),
        },
    )

    proof_id_map: dict[str, str] = {}
    for node in forest.get("nodes") or []:
        if not isinstance(node, dict):
            continue
        nid = proof_node_id(node)
        proof_id_map[str(node.get("id"))] = nid
        add_node(nodes, {"id": nid, "kind": f"proof_{node.get('kind')}", "proof_node_id": node.get("id"), **node})
        if node.get("kind") in {"goal", "tactic"}:
            add_edge(edges, proof_root, nid, "apex_state" if node.get("kind") == "goal" else "apex_tactic")

    for edge in forest.get("edges") or []:
        if not isinstance(edge, dict):
            continue
        src = proof_id_map.get(str(edge.get("from")))
        dst = proof_id_map.get(str(edge.get("to")))
        if src and dst:
            add_edge(edges, src, dst, "forward_" + str(edge.get("role") or "edge"), original_role=edge.get("role"))

    cone_nodes, decl_by_name, decls_by_file = build_cone_indexes(cone)
    for node in cone_nodes.values():
        cid = add_node(nodes, {**node, "id": "cone:" + str(node["id"])})
        add_edge(edges, proof_root, cid, "backward_cone_context")

    apex = cone.get("apex") if isinstance(cone.get("apex"), dict) else {}
    apex_name = apex_decl or normalize(apex.get("name") or apex.get("representative"))
    if apex_name and apex_name in decl_by_name:
        add_edge(edges, proof_root, "cone:" + decl_by_name[apex_name], "apex_declaration")

    for node in forest.get("nodes") or []:
        if not isinstance(node, dict):
            continue
        local_id = proof_id_map.get(str(node.get("id")))
        if not local_id:
            continue
        if node.get("kind") == "reference":
            ref = normalize(node.get("text"))
            did = decl_by_name.get(ref)
            if did:
                add_edge(edges, local_id, "cone:" + did, "grounded_by_decl", match="reference")
        if node.get("kind") in {"proof", "goal", "tactic"}:
            file = normalize(node.get("source_file") or forest.get("source_file"))
            for did in decls_by_file.get(file, [])[:8]:
                add_edge(edges, local_id, "cone:" + did, "grounded_by_file", match="source_file")

    return {
        "schema": SCHEMA,
        "id": str(nodes[proof_root]["id"]),
        "proof_forest_id": forest.get("id"),
        "cone_apex": apex.get("name") or apex.get("representative"),
        "nodes": list(nodes.values()),
        "edges": edges,
        "summary": {
            "nodes": len(nodes),
            "edges": len(edges),
            "proof_nodes": sum(1 for node in nodes.values() if str(node.get("kind", "")).startswith("proof_")),
            "cone_nodes": sum(1 for node in nodes.values() if str(node.get("id", "")).startswith("cone:")),
            "grounding_edges": sum(1 for edge in edges if str(edge.get("role", "")).startswith("grounded_by")),
        },
        "authority": {
            "bidirectional_prompt_context": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
            count += 1
    return count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof-forest", type=Path, required=True)
    parser.add_argument("--cone-packet", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--apex-decl", default="")
    args = parser.parse_args()

    cone = load_cone_packet(args.cone_packet)
    rows = [build_bidirectional_cone(forest, cone, apex_decl=args.apex_decl) for forest in iter_jsonl(args.proof_forest)]
    count = write_jsonl(args.out, rows)
    print(
        json.dumps(
            {
                "schema": SCHEMA + ".summary",
                "out": str(args.out),
                "bidirectional_cones": count,
                "nodes": sum(row["summary"]["nodes"] for row in rows),
                "edges": sum(row["summary"]["edges"] for row in rows),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
