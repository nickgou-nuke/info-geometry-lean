#!/usr/bin/env python3
"""Hydrate raw Arango JSONL graph exports with topology labels.

This is deliberately topology-first. It does not infer semantic synonyms. It
reads raw node/edge JSONL, computes graph labels from the actual edge topology,
and writes a lossless copy with added labels/metrics.
"""

from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
from typing import Any


# [lossless-compact] read_jsonl folded into igf.common.json_io.read_jsonl
from igf.common.json_io import read_jsonl


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def node_key(row: dict[str, Any]) -> str:
    return str(row.get("name") or row.get("_key") or row.get("id") or "")


def edge_endpoint_key(value: Any) -> str:
    text = str(value or "")
    if "/" in text:
        return text.split("/", 1)[1]
    return text


def collection_name(from_to: Any, fallback: str) -> str:
    text = str(from_to or "")
    if "/" in text:
        return text.split("/", 1)[0]
    return fallback


def tarjan(nodes: list[str], forward: dict[str, list[str]]) -> tuple[dict[str, int], dict[int, list[str]]]:
    index = 0
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    scc_of: dict[str, int] = {}
    sccs: dict[int, list[str]] = {}

    def strongconnect(v: str) -> None:
        nonlocal index
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)

        for w in forward.get(v, []):
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])

        if lowlink[v] == indices[v]:
            scc_id = len(sccs)
            members: list[str] = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                scc_of[w] = scc_id
                members.append(w)
                if w == v:
                    break
            sccs[scc_id] = members

    for node in nodes:
        if node not in indices:
            strongconnect(node)
    return scc_of, sccs


def hydrate(
    nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    *,
    raw_layer_policy: str,
    raw_node_collection: str,
    topology_overlay_collection: str,
) -> dict[str, Any]:
    keys = [node_key(row) for row in nodes if node_key(row)]
    key_set = set(keys)
    forward: dict[str, list[str]] = collections.defaultdict(list)
    reverse: dict[str, list[str]] = collections.defaultdict(list)
    edge_loss: list[dict[str, Any]] = []

    for edge in edges:
        src = edge_endpoint_key(edge.get("_from") or edge.get("src"))
        dst = edge_endpoint_key(edge.get("_to") or edge.get("dst"))
        if src in key_set and dst in key_set:
            forward[src].append(dst)
            reverse[dst].append(src)
        else:
            edge_loss.append(
                {
                    "edge_key": edge.get("_key"),
                    "src": src,
                    "dst": dst,
                    "reason": "endpoint_missing_from_node_set",
                }
            )

    scc_of, sccs = tarjan(keys, forward)
    indegree = {key: len(reverse.get(key, [])) for key in keys}
    outdegree = {key: len(forward.get(key, [])) for key in keys}

    hydrated_nodes: list[dict[str, Any]] = []
    for row in nodes:
        key = node_key(row)
        labels = set(str(label) for label in row.get("labels", []) if label)
        graph_kind = str(row.get("graphKind") or row.get("kind") or "")
        expr_tag = str(row.get("exprTag") or "")
        section_tag = str(row.get("sectionTag") or "")
        quality = str(row.get("quality") or "ok")
        if graph_kind:
            labels.add(f"graph:{graph_kind}")
        if expr_tag:
            labels.add(f"expr:{expr_tag}")
        if section_tag:
            labels.add(f"section:{section_tag}")
        labels.add(f"quality:{quality}")
        labels.add("layer:raw")
        labels.add("grain:fine")
        labels.add("policy:lossless_preserved")
        if indegree.get(key, 0) == 0:
            labels.add("topology:source")
        if outdegree.get(key, 0) == 0:
            labels.add("topology:sink")
        scc_id = scc_of.get(key, -1)
        scc_size = len(sccs.get(scc_id, []))
        labels.add("topology:cyclic" if scc_size > 1 else "topology:acyclic_singleton")
        next_row = dict(row)
        
        # ⚖️ PAULI REFACTOR: Handle list-based attrs from dagIndexer
        raw_attrs = next_row.get("attrs")
        if isinstance(raw_attrs, list):
            # Keep as list but add new ones
            raw_attrs.extend([
                f"hydration_policy:{raw_layer_policy}",
                "layer:raw",
                "grain:fine",
                "overlay_model:layered_tensor_network",
                f"scc_id_nat:{scc_id}",
                f"scc_size_nat:{scc_size}",
                f"indegree_nat:{indegree.get(key, 0)}",
                f"outdegree_nat:{outdegree.get(key, 0)}",
            ])
        else:
            next_row["attrs"] = {
                "hydration_policy": raw_layer_policy,
                "layer": "raw",
                "grain": "fine",
                "overlay_model": "layered_tensor_network",
                "scc_id": scc_id,
                "scc_size": scc_size,
                "indegree": indegree.get(key, 0),
                "outdegree": outdegree.get(key, 0),
            }
        
        next_row["labels"] = sorted(labels)
        hydrated_nodes.append(next_row)

    hydrated_edges: list[dict[str, Any]] = []
    for edge in edges:
        next_edge = dict(edge)
        labels = set(str(label) for label in next_edge.get("labels", []) if label)
        kind = str(next_edge.get("kind") or "")
        role = str(next_edge.get("role") or "")
        quality = str(next_edge.get("quality") or "ok")
        if kind:
            labels.add(f"edge:{kind}")
        if role:
            labels.add(f"role:{role}")
        labels.add(f"quality:{quality}")
        labels.add("layer:raw")
        labels.add("grain:fine")
        labels.add("policy:lossless_preserved")
        next_edge["labels"] = sorted(labels)
        attrs = dict(next_edge.get("attrs") or {})
        attrs.update(
            {
                "layer": "raw",
                "grain": "fine",
                "overlay_model": "layered_tensor_network",
                "preserved_one_for_one": True,
            }
        )
        next_edge["attrs"] = attrs
        hydrated_edges.append(next_edge)

    overlay_nodes: list[dict[str, Any]] = []
    overlay_edges: list[dict[str, Any]] = []
    overlay_edge_index = 0

    for scc_id, members in sorted(sccs.items()):
        scc_key = f"scc_{scc_id}"
        overlay_nodes.append(
            {
                "_key": scc_key,
                "id": f"topology/scc/{scc_id}",
                "graphKind": "topology_overlay",
                "kind": "scc_component",
                "layer": "topology_overlay",
                "grain": "scc",
                "scc_id": scc_id,
                "scc_size": len(members),
                "members": members,
                "labels": [
                    "layer:topology_overlay",
                    "overlay:scc",
                    "grain:scc",
                    "topology:coarse_grain",
                    "topology:preserving_overlay",
                    "policy:lossless_additive",
                ],
                "attrs": {
                    "raw_layer_policy": raw_layer_policy,
                    "layer": "topology_overlay",
                    "grain": "scc",
                    "coarse_graining": "scc",
                    "overlay_model": "layered_tensor_network",
                    "preserves_raw_topology": True,
                },
            }
        )
        for order, member in enumerate(members):
            overlay_edges.append(
                {
                    "_key": f"overlay_e_{overlay_edge_index}",
                    "_from": f"{raw_node_collection}/{member}",
                    "_to": f"topology_overlay/{scc_key}",
                    "kind": "projection",
                    "role": "member_of_scc",
                    "layer": "projection",
                    "grain": "cross_layer",
                    "scc_id": scc_id,
                    "member_key": member,
                    "member_order": order,
                    "labels": [
                        "layer:projection",
                        "overlay:member_of_scc",
                        "role:member_of_scc",
                        "topology:witness",
                        "policy:lossless_additive",
                    ],
                    "attrs": {
                        "layer": "projection",
                        "grain": "cross_layer",
                        "direction": "raw_to_scc",
                        "overlay_model": "layered_tensor_network",
                        "preserves_raw_topology": True,
                    },
                }
            )
            overlay_edge_index += 1


    scc_edge_witnesses: dict[tuple[int, int, str], list[str]] = collections.defaultdict(list)
    for edge in edges:
        src = edge_endpoint_key(edge.get("_from") or edge.get("src"))
        dst = edge_endpoint_key(edge.get("_to") or edge.get("dst"))
        src_scc = scc_of.get(src)
        dst_scc = scc_of.get(dst)
        if src_scc is None or dst_scc is None:
            continue
        kind = str(edge.get("kind") or "")
        scc_edge_witnesses[(src_scc, dst_scc, kind)].append(str(edge.get("_key") or ""))

    for (src_scc, dst_scc, kind), witnesses in sorted(scc_edge_witnesses.items()):
        overlay_edges.append(
            {
                "_key": f"overlay_e_{overlay_edge_index}",
                "_from": f"{topology_overlay_collection}/scc_{src_scc}",
                "_to": f"{topology_overlay_collection}/scc_{dst_scc}",
                "kind": kind,
                "role": "scc_quotient",
                "layer": "topology_overlay",
                "grain": "scc",
                "src_scc": src_scc,
                "dst_scc": dst_scc,
                "src_scc_id": src_scc,
                "dst_scc_id": dst_scc,
                "multiplicity": len(witnesses),
                "witness_raw_edge_keys": witnesses,
                "labels": [
                    "layer:topology_overlay",
                    "overlay:scc_quotient",
                    "role:scc_quotient",
                    f"edge:{kind}",
                    "grain:scc",
                    "topology:coarse_grain",
                    "topology:witnessed_by_raw_edges",
                    "policy:lossless_additive",
                ],
                "attrs": {
                    "layer": "topology_overlay",
                    "grain": "scc",
                    "overlay_model": "layered_tensor_network",
                    "witness_count": len(witnesses),
                    "raw_edge_kind": kind,
                    "preserves_raw_topology": True,
                },
            }
        )
        overlay_edge_index += 1

    return {
        "nodes": hydrated_nodes,
        "edges": hydrated_edges,
        "overlay_nodes": overlay_nodes,
        "overlay_edges": overlay_edges,
        "metadata": {
            "schema": "info_geometry.arango_topology_hydration.v1",
            "raw_layer_policy": raw_layer_policy,
            "scc_labels_policy": "LOSSLESS_ADDITIVE",
            "scc_labels_are_additive": True,
            "overlay_policy": "TOPOLOGY_PRESERVING_COARSE_GRAINING",
            "overlay_model": "layered_tensor_network",
            "projection_edge_roles": ["member_of_scc", "scc_quotient"],
            "raw_nodes_preserved": len(hydrated_nodes) == len(nodes),
            "raw_edges_preserved": len(hydrated_edges) == len(edges),
            "node_count": len(nodes),
            "edge_count": len(edges),
            "scc_count": len(sccs),
            "overlay_node_count": len(overlay_nodes),
            "overlay_edge_count": len(overlay_edges),
            "edge_loss_count": len(edge_loss),
            "edge_loss": edge_loss[:100],
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--raw-layer-policy", default="LOSSLESS")
    parser.add_argument("--raw-node-collection", default="ig_nodes")
    parser.add_argument("--topology-overlay-collection", default="topology_overlay")
    parser.add_argument("--strict-lossless", action=argparse.BooleanOptionalAction, default=True)
    args = parser.parse_args()

    nodes = read_jsonl(args.input_dir / "decls.jsonl")
    edges = read_jsonl(args.input_dir / "edges.jsonl")
    result = hydrate(
        nodes,
        edges,
        raw_layer_policy=args.raw_layer_policy,
        raw_node_collection=args.raw_node_collection,
        topology_overlay_collection=args.topology_overlay_collection,
    )
    metadata = result["metadata"]
    if args.strict_lossless and metadata["edge_loss_count"]:
        print(
            f"error: strict lossless hydration found {metadata['edge_loss_count']} edge(s) "
            "whose endpoints are missing from the raw node set",
        )
        return 2
    write_jsonl(args.output_dir / "ig_nodes.jsonl", result["nodes"])
    write_jsonl(args.output_dir / "ig_edges.jsonl", result["edges"])
    write_jsonl(args.output_dir / "topology_overlay_nodes.jsonl", result["overlay_nodes"])
    write_jsonl(args.output_dir / "topology_overlay_edges.jsonl", result["overlay_edges"])
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "metadata.json").write_text(
        json.dumps(result["metadata"], indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
