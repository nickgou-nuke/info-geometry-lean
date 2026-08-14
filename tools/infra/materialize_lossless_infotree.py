#!/usr/bin/env python3
"""Materialize a topology-preserving raw DAG graph for ArangoDB.

This builds a layered graph, not a replacement projection:

* raw layer: every declaration endpoint and every raw dependency edge from the
  Lean indexer is preserved one-for-one.
* SCC layer: coarse-grained SCC nodes are added as a separate overlay.
* projection edges: raw nodes are connected to SCC nodes by `member_of_scc`.
* quotient edges: SCC-to-SCC edges summarize cross-component raw edges and
  carry bounded witness keys plus queryable raw-witness coordinates.

The invariant is that raw topology is never filtered to create the overlay.
Coarse graining is additive and connected back to the raw layer.

This is not the compiler `raw_infotree_*` exporter. It is lossless relative to
the current raw DAG dependency export only.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.lossless_raw_dag_arango.v1"


@dataclass(frozen=True)
class RawEdge:
    index: int
    src: str
    dst: str
    kind: str


def read_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if line:
                yield json.loads(line)


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
            count += 1
    return count


def stable_key(prefix: str, value: str) -> str:
    digest = hashlib.sha256(f"{prefix}:{value}".encode("utf-8")).hexdigest()
    return f"{prefix}_{digest[:40]}"


def edge_key(prefix: str, *parts: object) -> str:
    payload = "\x1f".join(str(part) for part in parts)
    digest = hashlib.sha256(f"{prefix}:{payload}".encode("utf-8")).hexdigest()
    return f"{prefix}_{digest[:40]}"


def module_of(name: str) -> str:
    pieces = name.split(".")
    if len(pieces) <= 1:
        return ""
    return ".".join(pieces[:-1])


def endpoint_class(name: str, decls: dict[str, dict[str, Any]], ns_prefix: str) -> str:
    if name in decls:
        return "indexed_declaration"
    if name.startswith(ns_prefix):
        return "internal_unindexed_endpoint"
    return "external_endpoint"


def decl_attr_strings(decl: dict[str, Any] | None) -> list[str]:
    attrs = (decl or {}).get("attrs") or []
    return [str(attr) for attr in attrs if attr]


def representation_attrs(decl: dict[str, Any] | None) -> dict[str, Any]:
    out: dict[str, Any] = {}
    rep_tags: list[str] = []
    for attr in decl_attr_strings(decl):
        if attr.startswith("rep_depth:"):
            out["rep_depth_slug"] = attr.split(":", 1)[1]
            rep_tags.append(attr)
        elif attr.startswith("rep_depth_nat:"):
            raw = attr.split(":", 1)[1]
            try:
                out["rep_depth_nat"] = int(raw)
            except ValueError:
                out["rep_depth_nat"] = raw
            rep_tags.append(attr)
        elif attr.startswith("rep_layer:"):
            out["rep_layer"] = attr.split(":", 1)[1]
            rep_tags.append(attr)
        elif attr.startswith("rep_layer_description:"):
            out["rep_layer_description"] = attr.split(":", 1)[1]
            rep_tags.append(attr)
    if rep_tags:
        out["rep_tags"] = sorted(set(rep_tags))
    return out


EDGE_KINDS = {
    "theorem",
    "equivalence",
    "representation",
    "analogy",
    "conjectural_bridge",
}


def semantic_edge_attrs(decl: dict[str, Any] | None) -> dict[str, Any]:
    """Normalize Lean ``@[edge_kind ...]`` tags for graph consumers.

    This is metadata projection only: it never upgrades a dependency edge into
    a proved theorem or changes Lean's authority status.
    """
    values = [
        attr.split(":", 1)[1]
        for attr in decl_attr_strings(decl)
        if attr.startswith("edge_kind:")
    ]
    values = sorted({value for value in values if value in EDGE_KINDS})
    if not values:
        return {}
    return {
        "edge_kind": values[0] if len(values) == 1 else values,
        "edge_kinds": values,
        "edge_kind_tags": [f"edge_kind:{value}" for value in values],
    }


def representation_labels(name: str, decl: dict[str, Any] | None, ns_prefix: str) -> list[str]:
    labels = {
        "lossless:raw_dag",
        "layer:raw_dag",
        f"endpoint:{endpoint_class(name, {} if decl is None else {name: decl}, ns_prefix)}",
    }
    for attr in decl_attr_strings(decl):
        if attr.startswith("rep_depth:") or attr.startswith("rep_depth_nat:") or attr.startswith("rep_layer:"):
            labels.add(attr)
        else:
            labels.add(f"attr:{attr}")
    mod = str((decl or {}).get("module") or module_of(name))
    kind = str((decl or {}).get("kind") or "endpoint_stub")
    if mod:
        labels.add(f"module:{mod}")
    if kind:
        labels.add(f"decl_kind:{kind}")
    if name.startswith(ns_prefix):
        labels.add("namespace:local")
    else:
        labels.add("namespace:external")
    return sorted(labels)


def load_decl_map(path: Path) -> dict[str, dict[str, Any]]:
    return {str(row["name"]): row for row in read_jsonl(path)}


def load_raw_edges(path: Path) -> list[RawEdge]:
    edges: list[RawEdge] = []
    for index, row in enumerate(read_jsonl(path)):
        edges.append(
            RawEdge(
                index=index,
                src=str(row.get("src") or ""),
                dst=str(row.get("dst") or ""),
                kind=str(row.get("kind") or "dependency"),
            )
        )
    return edges


def load_lean_structural_topology(
    path: Path,
    names: list[str],
    key_of: dict[str, str],
) -> tuple[dict[str, int], dict[int, list[str]], dict[int, str], dict[int, dict[str, Any]], str]:
    """Transfer Lean-produced SCC/component labels onto raw endpoint keys.

    Indexed declarations use `structural-topology.json` directly. External or
    otherwise unindexed raw endpoints are kept losslessly as explicit endpoint
    stub components; those stubs are overlays for storage, not Lean-computed SCC
    truth.
    """
    if not path.exists():
        raise FileNotFoundError(f"Lean structural topology file not found: {path}")
    data = json.loads(path.read_text(encoding="utf-8"))
    members = data.get("membership") or []
    components = data.get("components") or []
    component_by_index: dict[int, dict[str, Any]] = {}
    for component in components:
        index = component.get("componentIndex")
        if isinstance(index, int):
            component_by_index[index] = component

    index_by_name: dict[str, int] = {}
    component_id_by_index: dict[int, str] = {}
    for row in members:
        name = row.get("declName")
        index = row.get("componentIndex")
        component_id = row.get("componentId")
        if isinstance(name, str) and isinstance(index, int):
            index_by_name[name] = index
            if isinstance(component_id, str):
                component_id_by_index[index] = component_id

    next_stub_index = (max(component_by_index) + 1) if component_by_index else 0
    scc_of: dict[str, int] = {}
    sccs: dict[int, list[str]] = collections.defaultdict(list)
    scc_key_of: dict[int, str] = {}
    scc_meta: dict[int, dict[str, Any]] = {}

    for name in names:
        key = key_of[name]
        if name in index_by_name:
            scc_id = index_by_name[name]
            component_id = component_id_by_index.get(scc_id, f"component:{scc_id}")
            scc_key_of[scc_id] = stable_key("scc", component_id)
            scc_meta[scc_id] = {
                "component_id": component_id,
                "source": "lean_structural_topology",
                **component_by_index.get(scc_id, {}),
            }
        else:
            scc_id = next_stub_index
            next_stub_index += 1
            component_id = f"endpoint-stub:{name}"
            scc_key_of[scc_id] = stable_key("scc", component_id)
            scc_meta[scc_id] = {
                "component_id": component_id,
                "componentIndex": scc_id,
                "representative": name,
                "source": "endpoint_stub_overlay",
                "members": [name],
                "size": 1,
            }
        scc_of[key] = scc_id
        sccs[scc_id].append(key)

    for scc_id, member_keys in list(sccs.items()):
        sccs[scc_id] = sorted(member_keys)
    return scc_of, dict(sccs), scc_key_of, scc_meta, "lean_structural_topology_with_endpoint_stubs"


def build(args: argparse.Namespace) -> dict[str, Any]:
    input_dir = args.input_dir.resolve()
    output_dir = args.output_dir.resolve()
    decls_path = input_dir / "decls.jsonl"
    raw_edges_path = input_dir / "raw_edges.jsonl"
    if not raw_edges_path.exists():
        raise FileNotFoundError(
            f"{raw_edges_path} not found. Re-run the Lean DAG indexer after the raw_edges patch."
        )

    decls = load_decl_map(decls_path)
    raw_edges = load_raw_edges(raw_edges_path)
    semantic_by_name = {
        name: semantic_edge_attrs(decl)
        for name, decl in decls.items()
    }

    endpoint_names = set(decls)
    for edge in raw_edges:
        endpoint_names.add(edge.src)
        endpoint_names.add(edge.dst)
    names = sorted(name for name in endpoint_names if name)

    key_of = {name: stable_key("raw", name) for name in names}
    structural_topology_path = args.structural_topology.resolve()
    scc_of, sccs, scc_key_of, scc_meta, topology_authority = load_lean_structural_topology(
        structural_topology_path,
        names,
        key_of,
    )

    name_by_key = {key: name for name, key in key_of.items()}
    raw_nodes: list[dict[str, Any]] = []
    for name in names:
        decl = decls.get(name)
        key = key_of[name]
        scc_id = scc_of[key]
        rep_attrs = representation_attrs(decl)
        edge_attrs = semantic_edge_attrs(decl)
        attrs = {
            "decl_kind": str((decl or {}).get("kind") or "endpoint_stub"),
            "doc": str((decl or {}).get("doc") or ""),
            **rep_attrs,
            **edge_attrs,
        }
        row = {
            "_key": key,
            "schema": SCHEMA,
            "layer": "raw_dag",
            "raw_name": name,
            "name": name,
            "endpoint_class": endpoint_class(name, decls, args.ns_prefix),
            "module": str((decl or {}).get("module") or module_of(name)),
            "kind": str((decl or {}).get("kind") or "endpoint_stub"),
            "attrs": attrs,
            "rep_depth": rep_attrs.get("rep_depth_nat"),
            "rep_depth_slug": rep_attrs.get("rep_depth_slug"),
            "rep_layer": rep_attrs.get("rep_layer"),
            "edge_kind": edge_attrs.get("edge_kind"),
            "edge_kinds": edge_attrs.get("edge_kinds", []),
            "decl": decl,
            "scc_id": scc_id,
            "scc_key": scc_key_of[scc_id],
            "labels": representation_labels(name, decl, args.ns_prefix),
        }
        raw_nodes.append(row)

    scc_nodes: list[dict[str, Any]] = []
    for scc_id, members in sorted(sccs.items()):
        member_names = [name_by_key[key] for key in members]
        cyclic = len(members) > 1
        meta = scc_meta.get(scc_id, {})
        scc_nodes.append(
            {
                "_key": scc_key_of[scc_id],
                "schema": SCHEMA,
                "layer": "scc_overlay",
                "scc_id": scc_id,
                "component_id": meta.get("component_id"),
                "topology_source": meta.get("source"),
                "representative": meta.get("representative") or (member_names[0] if member_names else None),
                "is_root": meta.get("isRoot"),
                "is_capstone": meta.get("isCapstone"),
                "depth_min": meta.get("depthMin"),
                "depth_max": meta.get("depthMax"),
                "strict_dominator_count": meta.get("strictDominatorCount"),
                "member_count": len(members),
                "cyclic": cyclic,
                "sample_members": member_names[: args.sample_members],
                "labels": [
                    "coarse_grain:scc",
                    "lossless:additive_overlay",
                    "layer:scc_overlay",
                    f"topology_source:{meta.get('source')}",
                    "topology:cyclic" if cyclic else "topology:acyclic_singleton",
                ],
            }
        )

    raw_edge_docs: list[dict[str, Any]] = []
    for edge in raw_edges:
        src_key = key_of[edge.src]
        dst_key = key_of[edge.dst]
        src_semantic = semantic_by_name.get(edge.src, {})
        semantic_kinds = src_semantic.get("edge_kinds", [])
        raw_edge_docs.append(
            {
                "_key": edge_key("rawedge", edge.index, edge.src, edge.dst, edge.kind),
                "_from": f"{args.raw_nodes_collection}/{src_key}",
                "_to": f"{args.raw_nodes_collection}/{dst_key}",
                "schema": SCHEMA,
                "layer": "raw_dag",
                "role": "raw_dependency",
                "raw_index": edge.index,
                "src": edge.src,
                "dst": edge.dst,
                "kind": edge.kind,
                "semantic_kind": src_semantic.get("edge_kind"),
                "semantic_kinds": semantic_kinds,
                "src_scc": scc_of[src_key],
                "dst_scc": scc_of[dst_key],
                "labels": [
                    f"edge_kind:{edge.kind}",
                    "layer:raw_dag",
                    "lossless:raw_dag_edge",
                    "topology:base",
                ] + [f"semantic_edge:{kind}" for kind in semantic_kinds],
            }
        )

    membership_edges: list[dict[str, Any]] = []
    for name in names:
        raw_key = key_of[name]
        scc_id = scc_of[raw_key]
        membership_edges.append(
            {
                "_key": edge_key("member", raw_key, scc_id),
                "_from": f"{args.raw_nodes_collection}/{raw_key}",
                "_to": f"{args.overlay_nodes_collection}/{scc_key_of[scc_id]}",
                "schema": SCHEMA,
                "layer": "projection",
                "role": "member_of_scc",
                "raw_name": name,
                "scc_id": scc_id,
                "labels": [
                    "coarse_grain:projection",
                    "layer:projection",
                    "lossless:additive_overlay",
                    "role:member_of_scc",
                ],
            }
        )

    quotient_counts: collections.Counter[tuple[int, int, str]] = collections.Counter()
    quotient_witnesses: dict[tuple[int, int, str], list[str]] = collections.defaultdict(list)
    for edge in raw_edges:
        src_scc = scc_of[key_of[edge.src]]
        dst_scc = scc_of[key_of[edge.dst]]
        if src_scc != dst_scc:
            qkey = (src_scc, dst_scc, edge.kind)
            quotient_counts[qkey] += 1
            if len(quotient_witnesses[qkey]) < args.max_witness_keys_per_quotient:
                quotient_witnesses[qkey].append(edge_key("rawedge", edge.index, edge.src, edge.dst, edge.kind))

    quotient_edges: list[dict[str, Any]] = []
    for (src_scc, dst_scc, kind), multiplicity in sorted(quotient_counts.items()):
        quotient_edges.append(
            {
                "_key": edge_key("sccedge", src_scc, dst_scc, kind),
                "_from": f"{args.overlay_nodes_collection}/{scc_key_of[src_scc]}",
                "_to": f"{args.overlay_nodes_collection}/{scc_key_of[dst_scc]}",
                "schema": SCHEMA,
                "layer": "scc_quotient",
                "role": "scc_quotient",
                "kind": kind,
                "src_scc": src_scc,
                "dst_scc": dst_scc,
                "multiplicity": multiplicity,
                "witness_raw_edge_keys": quotient_witnesses[(src_scc, dst_scc, kind)],
                "witness_key_limit": args.max_witness_keys_per_quotient,
                "witness_overflow_count": max(0, multiplicity - len(quotient_witnesses[(src_scc, dst_scc, kind)])),
                "witness_query": {
                    "collection": args.raw_edges_collection,
                    "src_scc": src_scc,
                    "dst_scc": dst_scc,
                    "kind": kind,
                },
                "labels": [
                    f"edge_kind:{kind}",
                    "coarse_grain:scc_quotient",
                    "layer:scc_quotient",
                    "lossless:additive_overlay",
                ],
            }
        )

    raw_node_count = write_jsonl(output_dir / "ig_nodes.jsonl", raw_nodes)
    raw_edge_count = write_jsonl(output_dir / "ig_edges.jsonl", raw_edge_docs)
    overlay_node_count = write_jsonl(output_dir / "topology_overlay_nodes.jsonl", scc_nodes)
    overlay_edge_count = write_jsonl(output_dir / "topology_overlay_edges.jsonl", membership_edges + quotient_edges)

    # Compatibility/debug files with explicit names.
    write_jsonl(output_dir / "infotree_raw_nodes.jsonl", raw_nodes)
    write_jsonl(output_dir / "infotree_raw_edges.jsonl", raw_edge_docs)
    write_jsonl(output_dir / "infotree_scc_nodes.jsonl", scc_nodes)
    write_jsonl(output_dir / "infotree_projection_edges.jsonl", membership_edges)
    write_jsonl(output_dir / "infotree_scc_quotient_edges.jsonl", quotient_edges)

    metadata = {
        "schema": SCHEMA,
        "policy": "LOSSLESS_RAW_DAG_LAYER_WITH_ADDITIVE_COARSE_GRAIN_OVERLAYS",
        "input_dir": str(input_dir),
        "output_dir": str(output_dir),
        "raw_nodes_collection": args.raw_nodes_collection,
        "raw_edges_collection": args.raw_edges_collection,
        "overlay_nodes_collection": args.overlay_nodes_collection,
        "overlay_edges_collection": args.overlay_edges_collection,
        "raw_decl_count": len(decls),
        "raw_endpoint_count": len(names),
        "raw_edge_count": len(raw_edges),
        "raw_edges_preserved_one_for_one": len(raw_edge_docs) == len(raw_edges),
        "topology_authority": topology_authority,
        "structural_topology": str(structural_topology_path),
        "lean_structural_component_count": sum(
            1 for row in scc_nodes if row.get("topology_source") == "lean_structural_topology"
        ),
        "endpoint_stub_component_count": sum(
            1 for row in scc_nodes if row.get("topology_source") == "endpoint_stub_overlay"
        ),
        "scc_count": len(sccs),
        "membership_edge_count": len(membership_edges),
        "scc_quotient_edge_count": len(quotient_edges),
        "raw_node_docs": raw_node_count,
        "raw_edge_docs": raw_edge_count,
        "overlay_node_docs": overlay_node_count,
        "overlay_edge_docs": overlay_edge_count,
        "invariant": (
            "SCC/module/coarse-grain layers are overlays. The raw InfoTree "
            "claim is not made here: this materializes the raw DAG dependency "
            "edge layer one-for-one and must not be confused with lossless "
            "compiler InfoTree preservation."
        ),
    }
    (output_dir / "metadata.json").write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return metadata


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=Path("artifacts/dag/index"))
    parser.add_argument("--output-dir", type=Path, default=Path("artifacts/infotree/arango"))
    parser.add_argument("--structural-topology", type=Path, default=Path("artifacts/dag/structural-topology.json"))
    parser.add_argument("--ns-prefix", default="InfoGeometry")
    parser.add_argument("--raw-nodes-collection", default="raw_info_nodes")
    parser.add_argument("--raw-edges-collection", default="raw_info_edges")
    parser.add_argument("--overlay-nodes-collection", default="topology_overlay")
    parser.add_argument("--overlay-edges-collection", default="topology_overlay_edges")
    parser.add_argument("--sample-members", type=int, default=16)
    parser.add_argument("--max-witness-keys-per-quotient", type=int, default=256)
    return parser.parse_args()


def main() -> int:
    metadata = build(parse_args())
    print(json.dumps(metadata, indent=2, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
