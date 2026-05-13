#!/usr/bin/env python3
"""Derive a dual wire/gate topology from ExprArangoExport rows.

Input is the raw Lean evidence layer:

* ``ig_nodes.jsonl``
* ``ig_edges.jsonl``

Output is a derived line-graph style projection:

* ``ig_wires.jsonl``      -- De Bruijn/binder incidence wires
* ``ig_gates.jsonl``      -- expression junction/operator gates
* ``ig_wire_edges.jsonl`` -- traversal edges between gates and wires
* ``ig_scc.jsonl``        -- SCC/topology components of the derived graph
* ``ig_scc_edges.jsonl``  -- member/quotient edges for the SCC overlay

This script does not replace ``ig_nodes`` / ``ig_edges``.  Every derived record
keeps raw ids and hashes so audits can descend back to Lean expression evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


DEFAULT_INPUT_DIR = Path("artifacts/expr-graph/arango")
DEFAULT_OUTPUT_DIR = Path("artifacts/expr-graph/wire-topology")

GATE_EXPR_TAGS = {"app", "lam", "forallE", "letE", "const", "proj", "mdata"}
HASH_KINDS = ("ownerAwareHash", "patternHash", "roleHash")


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def stable_hash(*parts: Any) -> str:
    payload = "|".join(str(part) for part in parts)
    return "sha256:" + hashlib.sha256(payload.encode("utf-8")).hexdigest()


def stable_key(prefix: str, *parts: Any) -> str:
    return prefix + "_" + stable_hash(*parts).split(":", 1)[1][:32]


def parse_doc_id(raw: Any, *, default_collection: str = "ig_nodes") -> str:
    text = str(raw)
    if "/" in text:
        return text
    return f"{default_collection}/{text}"


def parse_doc_key(raw: Any) -> str:
    text = str(raw)
    return text.split("/", 1)[1] if "/" in text else text


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        for line_no, raw in enumerate(handle, start=1):
            line = raw.strip()
            if not line:
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            yield row


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True, ensure_ascii=True) + "\n")
            count += 1
    return count


def load_expr_graph(input_dir: Path) -> tuple[dict[str, dict[str, Any]], list[dict[str, Any]]]:
    nodes_path = input_dir / "ig_nodes.jsonl"
    edges_path = input_dir / "ig_edges.jsonl"
    if not nodes_path.exists() or not edges_path.exists():
        missing = [str(p) for p in [nodes_path, edges_path] if not p.exists()]
        raise FileNotFoundError("missing ExprArangoExport inputs: " + ", ".join(missing))

    nodes: dict[str, dict[str, Any]] = {}
    for row in iter_jsonl(nodes_path):
        key = str(row.get("_key") or "")
        if not key:
            raise ValueError(f"{nodes_path}: row missing _key")
        nodes[f"ig_nodes/{key}"] = row
    edges = list(iter_jsonl(edges_path))
    return nodes, edges


def gate_kind(node: dict[str, Any]) -> str:
    tag = str(node.get("exprTag", "") or "")
    if tag == "const":
        return "const"
    if tag in {"lam", "forallE", "letE"}:
        return "binder"
    if tag == "app":
        return "app"
    if tag in {"proj", "mdata"}:
        return tag
    return "expr"


def build_const_ref_targets(edges: list[dict[str, Any]]) -> dict[str, str]:
    targets: dict[str, str] = {}
    for edge in edges:
        if edge.get("kind") == "const_ref" or edge.get("role") == "const_ref":
            targets[parse_doc_id(edge.get("_from"))] = parse_doc_id(edge.get("_to"))
    return targets


def build_gates(
    nodes: dict[str, dict[str, Any]],
    edges: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    const_ref_targets = build_const_ref_targets(edges)
    raw_to_gate: dict[str, str] = {}
    gates: list[dict[str, Any]] = []
    for raw_id, node in sorted(nodes.items()):
        if node.get("graphKind") != "expr":
            continue
        expr_tag = str(node.get("exprTag", "") or "")
        if expr_tag not in GATE_EXPR_TAGS:
            continue
        operator_name = str(node.get("info", "") or expr_tag)
        gate_hash = stable_hash("gate", raw_id, expr_tag, operator_name, node.get("decl", ""))
        gate_key = stable_key("gate", raw_id, expr_tag, operator_name, node.get("decl", ""))
        raw_to_gate[raw_id] = f"ig_gates/{gate_key}"
        gates.append(
            {
                "_key": gate_key,
                "gateKey": gate_key,
                "kind": "gate",
                "gateKind": gate_kind(node),
                "exprTag": expr_tag,
                "decl": node.get("decl", ""),
                "module": node.get("module", ""),
                "operatorName": operator_name,
                "constName": operator_name if expr_tag == "const" else "",
                "rawExprId": raw_id,
                "constDeclId": const_ref_targets.get(raw_id, ""),
                "gateHash": gate_hash,
                "shapeHash": node.get("shapeHash", 0),
                "quality": node.get("quality", "ok"),
            }
        )
    return gates, raw_to_gate


def build_wires_and_edges(
    nodes: dict[str, dict[str, Any]],
    edges: list[dict[str, Any]],
    raw_to_gate: dict[str, str],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    wires: list[dict[str, Any]] = []
    wire_edges: list[dict[str, Any]] = []
    ast_parent_by_child: dict[str, list[tuple[str, str]]] = defaultdict(list)
    wire_groups: dict[tuple[str, str], dict[str, Any]] = {}
    pattern_groups: dict[tuple[str, Any, str, str], dict[str, Any]] = {}
    occurrence_specs: list[dict[str, Any]] = []

    for edge in edges:
        if edge.get("kind") == "ast":
            ast_parent_by_child[parse_doc_id(edge.get("_to"))].append(
                (parse_doc_id(edge.get("_from")), str(edge.get("role", "") or ""))
            )

    for edge in edges:
        if not (edge.get("kind") == "bind" and edge.get("role") == "bound_by"):
            continue
        raw_bvar_id = parse_doc_id(edge.get("_from"))
        binder_raw_id = parse_doc_id(edge.get("_to"))
        bvar_node = nodes.get(raw_bvar_id, {})
        binder_node = nodes.get(binder_raw_id, {})
        de_bruijn_idx = edge.get("deBruijnIdx", bvar_node.get("deBruijnIdx"))
        incidence_hash = str(edge.get("incidenceHash") or stable_hash("bound_by", raw_bvar_id, binder_raw_id, de_bruijn_idx))
        decl = str(bvar_node.get("decl", edge.get("decl", "")) or "")
        role_path = ".".join(sorted({role for _, role in ast_parent_by_child.get(raw_bvar_id, []) if role})) or "root"
        binder_kind = gate_kind(binder_node) if binder_node else "missing"
        local_shape = str(bvar_node.get("shapeHash", ""))
        group_key = (decl, binder_raw_id)
        group = wire_groups.setdefault(
            group_key,
            {
                "decl": decl,
                "module": bvar_node.get("module", binder_node.get("module", "")),
                "binderRawId": binder_raw_id,
                "binderExpr": binder_raw_id,
                "rawBvarIds": [],
                "deBruijnIdxs": [],
                "deBruijnHashes": [],
                "incidenceHashes": [],
                "quality": "ok",
            },
        )
        group["rawBvarIds"].append(raw_bvar_id)
        group["deBruijnIdxs"].append(de_bruijn_idx)
        group["deBruijnHashes"].append(str(bvar_node.get("deBruijnHash", "") or ""))
        group["incidenceHashes"].append(incidence_hash)
        if bvar_node.get("quality") == "broken" or not binder_node:
            group["quality"] = "broken"

        pattern_key = (binder_kind, de_bruijn_idx, role_path, local_shape)
        pattern = pattern_groups.setdefault(
            pattern_key,
            {
                "binderKind": binder_kind,
                "deBruijnIdx": de_bruijn_idx,
                "rolePath": role_path,
                "localShape": local_shape,
                "decls": [],
                "modules": [],
                "rawBvarIds": [],
            },
        )
        pattern["decls"].append(decl)
        pattern["modules"].append(str(bvar_node.get("module", "") or ""))
        pattern["rawBvarIds"].append(raw_bvar_id)

        occurrence_specs.append(
            {
                "decl": decl,
                "module": bvar_node.get("module", binder_node.get("module", "")),
                "rawBvarId": raw_bvar_id,
                "binderRawId": binder_raw_id,
                "binderExpr": binder_raw_id,
                "deBruijnIdx": de_bruijn_idx,
                "deBruijnHash": str(bvar_node.get("deBruijnHash", "") or ""),
                "incidenceHash": incidence_hash,
                "rolePath": role_path,
                "binderKind": binder_kind,
                "localShape": local_shape,
                "quality": "broken" if bvar_node.get("quality") == "broken" or not binder_node else "ok",
            }
        )

    wire_id_by_group: dict[tuple[str, str], str] = {}
    wire_hash_by_group: dict[tuple[str, str], str] = {}
    wire_id_by_occurrence: dict[str, str] = {}
    wire_hash_by_occurrence: dict[str, str] = {}
    wire_id_by_pattern: dict[tuple[str, Any, str, str], str] = {}
    wire_hash_by_pattern: dict[tuple[str, Any, str, str], str] = {}

    for spec in sorted(occurrence_specs, key=lambda row: (str(row["decl"]), str(row["rawBvarId"]), str(row["incidenceHash"]))):
        wire_hash = stable_hash("wire-occurrence", spec["decl"], spec["rawBvarId"], spec["binderRawId"], spec["deBruijnIdx"], spec["incidenceHash"])
        wire_key = stable_key("wire_occ", spec["decl"], spec["rawBvarId"], spec["binderRawId"], spec["deBruijnIdx"], spec["incidenceHash"])
        wire_id = f"ig_wires/{wire_key}"
        wire_id_by_occurrence[str(spec["incidenceHash"])] = wire_id
        wire_hash_by_occurrence[str(spec["incidenceHash"])] = wire_hash
        wires.append(
            {
                "_key": wire_key,
                "wireKey": wire_key,
                "kind": "wire",
                "type": "causal_string",
                "wireLevel": "occurrence",
                "decl": spec["decl"],
                "module": spec["module"],
                "rawBvarId": spec["rawBvarId"],
                "rawBvarIds": [spec["rawBvarId"]],
                "occurrenceCount": 1,
                "binderRawId": spec["binderRawId"],
                "binderExpr": spec["binderExpr"],
                "binderKind": spec["binderKind"],
                "rolePath": spec["rolePath"],
                "localShape": spec["localShape"],
                "deBruijnIdx": spec["deBruijnIdx"],
                "deBruijnIdxs": [spec["deBruijnIdx"]] if spec["deBruijnIdx"] is not None else [],
                "deBruijnHash": spec["deBruijnHash"],
                "deBruijnHashes": [spec["deBruijnHash"]] if spec["deBruijnHash"] else [],
                "incidenceHash": spec["incidenceHash"],
                "incidenceHashes": [spec["incidenceHash"]],
                "wireHash": wire_hash,
                "quality": spec["quality"],
            }
        )

    for group_key, group in sorted(wire_groups.items()):
        raw_bvar_ids = sorted(set(group["rawBvarIds"]))
        de_bruijn_idx_values = sorted({idx for idx in group["deBruijnIdxs"] if idx is not None})
        de_bruijn_hashes = sorted({h for h in group["deBruijnHashes"] if h})
        incidence_hashes = sorted({h for h in group["incidenceHashes"] if h})
        wire_hash = stable_hash("wire-group", group["decl"], group["binderRawId"], ",".join(raw_bvar_ids), ",".join(incidence_hashes))
        wire_key = stable_key("wire", group["decl"], group["binderRawId"], ",".join(raw_bvar_ids), ",".join(incidence_hashes))
        wire_id = f"ig_wires/{wire_key}"
        wire_id_by_group[group_key] = wire_id
        wire_hash_by_group[group_key] = wire_hash
        wires.append(
            {
                "_key": wire_key,
                "wireKey": wire_key,
                "kind": "wire",
                "type": "causal_string",
                "wireLevel": "fiber",
                "decl": group["decl"],
                "module": group["module"],
                "rawBvarId": raw_bvar_ids[0] if raw_bvar_ids else "",
                "rawBvarIds": raw_bvar_ids,
                "occurrenceCount": len(raw_bvar_ids),
                "binderRawId": group["binderRawId"],
                "binderExpr": group["binderExpr"],
                "deBruijnIdx": de_bruijn_idx_values[0] if len(de_bruijn_idx_values) == 1 else None,
                "deBruijnIdxs": de_bruijn_idx_values,
                "deBruijnHash": de_bruijn_hashes[0] if len(de_bruijn_hashes) == 1 else "",
                "deBruijnHashes": de_bruijn_hashes,
                "incidenceHash": incidence_hashes[0] if len(incidence_hashes) == 1 else "",
                "incidenceHashes": incidence_hashes,
                "wireHash": wire_hash,
                "quality": group["quality"],
            }
        )

    for pattern_key, pattern in sorted(pattern_groups.items()):
        decls = sorted({d for d in pattern["decls"] if d})
        modules = sorted({m for m in pattern["modules"] if m})
        raw_bvar_ids = sorted(set(pattern["rawBvarIds"]))
        wire_hash = stable_hash(
            "wire-pattern",
            pattern["binderKind"],
            pattern["deBruijnIdx"],
            pattern["rolePath"],
            pattern["localShape"],
        )
        wire_key = stable_key(
            "wire_pat",
            pattern["binderKind"],
            pattern["deBruijnIdx"],
            pattern["rolePath"],
            pattern["localShape"],
        )
        wire_id = f"ig_wires/{wire_key}"
        wire_id_by_pattern[pattern_key] = wire_id
        wire_hash_by_pattern[pattern_key] = wire_hash
        wires.append(
            {
                "_key": wire_key,
                "wireKey": wire_key,
                "kind": "wire",
                "type": "causal_string_pattern",
                "wireLevel": "pattern",
                "decl": decls[0] if len(decls) == 1 else "",
                "decls": decls,
                "module": modules[0] if len(modules) == 1 else "",
                "modules": modules,
                "rawBvarId": raw_bvar_ids[0] if raw_bvar_ids else "",
                "rawBvarIds": raw_bvar_ids,
                "occurrenceCount": len(raw_bvar_ids),
                "binderKind": pattern["binderKind"],
                "rolePath": pattern["rolePath"],
                "localShape": pattern["localShape"],
                "deBruijnIdx": pattern["deBruijnIdx"],
                "deBruijnIdxs": [pattern["deBruijnIdx"]] if pattern["deBruijnIdx"] is not None else [],
                "wireHash": wire_hash,
                "quality": "derived",
            }
        )

    for edge in edges:
        if not (edge.get("kind") == "bind" and edge.get("role") == "bound_by"):
            continue
        raw_bvar_id = parse_doc_id(edge.get("_from"))
        binder_raw_id = parse_doc_id(edge.get("_to"))
        bvar_node = nodes.get(raw_bvar_id, {})
        binder_node = nodes.get(binder_raw_id, {})
        de_bruijn_idx = edge.get("deBruijnIdx", bvar_node.get("deBruijnIdx"))
        incidence_hash = str(edge.get("incidenceHash") or stable_hash("bound_by", raw_bvar_id, binder_raw_id, de_bruijn_idx))
        decl = str(bvar_node.get("decl", edge.get("decl", "")) or "")
        group_key = (decl, binder_raw_id)
        wire_id = wire_id_by_group[group_key]
        wire_hash = wire_hash_by_group[group_key]
        occurrence_wire_id = wire_id_by_occurrence[incidence_hash]
        occurrence_wire_hash = wire_hash_by_occurrence[incidence_hash]
        role_path = ".".join(sorted({role for _, role in ast_parent_by_child.get(raw_bvar_id, []) if role})) or "root"
        binder_kind_value = gate_kind(binder_node) if binder_node else "missing"
        local_shape = str(bvar_node.get("shapeHash", ""))
        pattern_key = (binder_kind_value, de_bruijn_idx, role_path, local_shape)
        pattern_wire_id = wire_id_by_pattern[pattern_key]
        pattern_wire_hash = wire_hash_by_pattern[pattern_key]

        binder_gate = raw_to_gate.get(binder_raw_id)
        if binder_gate:
            wire_edges.append(
                {
                    "_key": stable_key("we", "binder_controls_wire", binder_gate, wire_id, incidence_hash),
                    "_from": binder_gate,
                    "_to": wire_id,
                    "kind": "binds_wire",
                    "role": "binder_controls_wire",
                    "source": "bound_by",
                    "rawEdgeId": f"ig_edges/{edge.get('_key', '')}",
                    "incidenceHash": incidence_hash,
                    "wireHash": wire_hash,
                }
            )

        wire_edges.append(
            {
                "_key": stable_key("we", "occurrence_collapses_to_fiber", occurrence_wire_id, wire_id, incidence_hash),
                "_from": occurrence_wire_id,
                "_to": wire_id,
                "kind": "wire_quotient",
                "role": "occurrence_collapses_to_fiber",
                "source": "derived_wire_level",
                "rawEdgeId": f"ig_edges/{edge.get('_key', '')}",
                "rawBvarId": raw_bvar_id,
                "binderRawId": binder_raw_id,
                "incidenceHash": incidence_hash,
                "wireHash": occurrence_wire_hash,
                "targetWireHash": wire_hash,
            }
        )

        wire_edges.append(
            {
                "_key": stable_key("we", "fiber_instantiates_pattern", wire_id, pattern_wire_id, incidence_hash),
                "_from": wire_id,
                "_to": pattern_wire_id,
                "kind": "wire_quotient",
                "role": "fiber_instantiates_pattern",
                "source": "derived_wire_level",
                "rawEdgeId": f"ig_edges/{edge.get('_key', '')}",
                "rawBvarId": raw_bvar_id,
                "binderRawId": binder_raw_id,
                "incidenceHash": incidence_hash,
                "wireHash": wire_hash,
                "targetWireHash": pattern_wire_hash,
            }
        )

        wire_edges.append(
            {
                "_key": stable_key("we", "wire_occurs_at", occurrence_wire_id, raw_bvar_id, incidence_hash),
                "_from": occurrence_wire_id,
                "_to": raw_bvar_id,
                "kind": "wire_occurs_at",
                "role": "wire_occurs_at",
                "source": "bound_by",
                "rawEdgeId": f"ig_edges/{edge.get('_key', '')}",
                "rawBvarId": raw_bvar_id,
                "binderRawId": binder_raw_id,
                "incidenceHash": incidence_hash,
                "wireHash": occurrence_wire_hash,
            }
        )

        for parent_raw_id, parent_role in ast_parent_by_child.get(raw_bvar_id, []):
            parent_gate = raw_to_gate.get(parent_raw_id)
            if parent_gate:
                wire_edges.append(
                    {
                        "_key": stable_key("we", "wire_enters_gate", occurrence_wire_id, parent_gate, incidence_hash, parent_role),
                        "_from": occurrence_wire_id,
                        "_to": parent_gate,
                        "kind": "wire_enters_gate",
                        "role": parent_role or "wire_argument_to_gate",
                        "wireRole": "wire_argument_to_gate",
                        "source": "ast_parent",
                        "rawBvarId": raw_bvar_id,
                        "rawGateExprId": parent_raw_id,
                        "incidenceHash": incidence_hash,
                        "wireHash": occurrence_wire_hash,
                    }
                )
    return wires, wire_edges


def graph_label(node_id: str, wires_by_id: dict[str, dict[str, Any]], gates_by_id: dict[str, dict[str, Any]]) -> str:
    if node_id in wires_by_id:
        wire = wires_by_id[node_id]
        return "|".join(
            [
                "wire",
                str(wire.get("wireLevel", "")),
                str(wire.get("binderKind", "")),
                str(wire.get("deBruijnIdx", "")),
                str(wire.get("rolePath", "")),
                str(wire.get("localShape", "")),
            ]
        )
    gate = gates_by_id.get(node_id, {})
    return "|".join(["gate", str(gate.get("gateKind", "")), const_class(str(gate.get("operatorName", "") or ""))])


def strongly_connected_components(vertices: set[str], edges: list[tuple[str, str]]) -> list[list[str]]:
    adjacency: dict[str, list[str]] = defaultdict(list)
    for source, target in edges:
        adjacency[source].append(target)

    index = 0
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    components: list[list[str]] = []

    def connect(vertex: str) -> None:
        nonlocal index
        indices[vertex] = index
        lowlinks[vertex] = index
        index += 1
        stack.append(vertex)
        on_stack.add(vertex)

        for target in adjacency.get(vertex, []):
            if target not in indices:
                connect(target)
                lowlinks[vertex] = min(lowlinks[vertex], lowlinks[target])
            elif target in on_stack:
                lowlinks[vertex] = min(lowlinks[vertex], indices[target])

        if lowlinks[vertex] == indices[vertex]:
            component: list[str] = []
            while True:
                target = stack.pop()
                on_stack.remove(target)
                component.append(target)
                if target == vertex:
                    break
            components.append(sorted(component))

    for vertex in sorted(vertices):
        if vertex not in indices:
            connect(vertex)
    return components


def build_wire_scc_overlay(
    wires: list[dict[str, Any]],
    gates: list[dict[str, Any]],
    wire_edges: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    wires_by_id = {f"ig_wires/{wire['_key']}": wire for wire in wires}
    gates_by_id = {f"ig_gates/{gate['_key']}": gate for gate in gates}
    vertices = set(wires_by_id) | set(gates_by_id)
    graph_edges = [
        (str(edge.get("_from", "")), str(edge.get("_to", "")))
        for edge in wire_edges
        if str(edge.get("_from", "")) in vertices and str(edge.get("_to", "")) in vertices
    ]
    components = strongly_connected_components(vertices, graph_edges)
    scc_id_by_member: dict[str, str] = {}
    scc_rows: list[dict[str, Any]] = []
    scc_edges: list[dict[str, Any]] = []

    for idx, members in enumerate(components):
        labels = sorted(graph_label(member, wires_by_id, gates_by_id) for member in members)
        modules = sorted(
            {
                str((wires_by_id.get(member) or gates_by_id.get(member) or {}).get("module", "") or "")
                for member in members
                if str((wires_by_id.get(member) or gates_by_id.get(member) or {}).get("module", "") or "")
            }
        )
        decls = sorted(
            {
                str((wires_by_id.get(member) or gates_by_id.get(member) or {}).get("decl", "") or "")
                for member in members
                if str((wires_by_id.get(member) or gates_by_id.get(member) or {}).get("decl", "") or "")
            }
        )
        gate_classes = sorted(
            {
                const_class(str(gates_by_id[member].get("operatorName", "") or ""))
                for member in members
                if member in gates_by_id
            }
        )
        scc_hash = stable_hash("wire-scc", json.dumps(labels, sort_keys=True))
        scc_key = stable_key("scc", scc_hash, idx)
        scc_id = f"ig_scc/{scc_key}"
        for member in members:
            scc_id_by_member[member] = scc_id
            scc_edges.append(
                {
                    "_key": stable_key("se", "member_of_scc", member, scc_id),
                    "_from": member,
                    "_to": scc_id,
                    "kind": "member_of_scc",
                    "role": "member_of_scc",
                    "source": "wire_topology_transform",
                }
            )
        scc_rows.append(
            {
                "_key": scc_key,
                "kind": "wire_scc",
                "memberCount": len(members),
                "members": members,
                "sccPatternHash": scc_hash,
                "dominantGateClasses": gate_classes,
                "modules": modules,
                "decls": decls,
                "quality": "derived",
            }
        )

    quotient_seen: set[tuple[str, str]] = set()
    for source, target in graph_edges:
        source_scc = scc_id_by_member.get(source)
        target_scc = scc_id_by_member.get(target)
        if not source_scc or not target_scc or source_scc == target_scc:
            continue
        key = (source_scc, target_scc)
        if key in quotient_seen:
            continue
        quotient_seen.add(key)
        scc_edges.append(
            {
                "_key": stable_key("se", "scc_quotient", source_scc, target_scc),
                "_from": source_scc,
                "_to": target_scc,
                "kind": "scc_quotient",
                "role": "scc_quotient",
                "source": "wire_topology_transform",
            }
        )

    return scc_rows, scc_edges


def occurrence_bucket(count: int) -> str:
    if count <= 1:
        return "1"
    if count <= 3:
        return "2-3"
    if count <= 8:
        return "4-8"
    return "9+"


def const_class(name: str) -> str:
    lower = name.lower()
    if "hmul" in lower or lower.endswith(".mul") or "mul" == lower:
        return "mul"
    if "hadd" in lower or lower.endswith(".add") or "add" == lower:
        return "add"
    if "hsub" in lower or lower.endswith(".sub") or "sub" == lower:
        return "sub"
    if "neg" in lower:
        return "neg"
    if "eq" in lower:
        return "eq"
    if "projector" in lower or "projection" in lower:
        return "projector"
    if "smul" in lower or "hsmul" in lower:
        return "scalar-mul"
    if "pow" in lower:
        return "pow"
    if "inv" in lower:
        return "inverse"
    return "other"


def decl_from_doc_id(raw_id: str, nodes: dict[str, dict[str, Any]]) -> str:
    return str(nodes.get(raw_id, {}).get("decl", "") or "")


def build_decl_topologies(
    nodes: dict[str, dict[str, Any]],
    gates: list[dict[str, Any]],
    wires: list[dict[str, Any]],
    wire_edges: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    by_decl: dict[str, dict[str, set[str]]] = defaultdict(lambda: {kind: set() for kind in HASH_KINDS})
    modules: dict[str, str] = {}

    for gate in gates:
        decl = str(gate.get("decl", "") or "")
        if not decl:
            continue
        modules.setdefault(decl, str(gate.get("module", "") or ""))
        gate_kind_value = str(gate.get("gateKind", "") or "")
        expr_tag = str(gate.get("exprTag", "") or "")
        operator_name = str(gate.get("operatorName", "") or "")
        by_decl[decl]["ownerAwareHash"].add(f"gate.kind:{gate_kind_value}")
        by_decl[decl]["ownerAwareHash"].add(f"gate.exprTag:{expr_tag}")
        if gate_kind_value == "const":
            by_decl[decl]["ownerAwareHash"].add(f"gate.const:{operator_name}")
        by_decl[decl]["patternHash"].add(f"gate.kind:{gate_kind_value}")
        by_decl[decl]["patternHash"].add(f"gate.exprTag:{expr_tag}")
        if gate_kind_value == "const":
            by_decl[decl]["patternHash"].add(f"constClass:{const_class(operator_name)}")
        by_decl[decl]["roleHash"].add(f"gate.role:{gate_kind_value}")
        if gate_kind_value == "const":
            by_decl[decl]["roleHash"].add(f"operatorClass:{const_class(operator_name)}")

    for wire in wires:
        decl = str(wire.get("decl", "") or "")
        if not decl:
            continue
        modules.setdefault(decl, str(wire.get("module", "") or ""))
        count = int(wire.get("occurrenceCount", 0) or 0)
        by_decl[decl]["ownerAwareHash"].add(f"wire.binder:{wire.get('binderRawId', '')}")
        by_decl[decl]["ownerAwareHash"].add(f"wire.occurrenceBucket:{occurrence_bucket(count)}")
        by_decl[decl]["patternHash"].add(f"wire.occurrenceBucket:{occurrence_bucket(count)}")
        by_decl[decl]["roleHash"].add(f"wire.occurrenceBucket:{occurrence_bucket(count)}")
        for idx in wire.get("deBruijnIdxs", []):
            by_decl[decl]["ownerAwareHash"].add(f"wire.deBruijnIdx:{idx}")
            by_decl[decl]["patternHash"].add(f"wire.deBruijnIdx:{idx}")

    for edge in wire_edges:
        decl = decl_from_doc_id(str(edge.get("rawBvarId", "") or ""), nodes)
        if not decl:
            source_id = str(edge.get("_from", "") or "")
            target_id = str(edge.get("_to", "") or "")
            if source_id.startswith("ig_nodes/"):
                decl = decl_from_doc_id(source_id, nodes)
            elif target_id.startswith("ig_nodes/"):
                decl = decl_from_doc_id(target_id, nodes)
        if not decl:
            continue
        role = str(edge.get("role", "") or "")
        by_decl[decl]["ownerAwareHash"].add(f"edge.role:{role}")
        by_decl[decl]["patternHash"].add(f"edge.role:{role}")
        by_decl[decl]["roleHash"].add(f"edge.role:{role}")

    topologies: list[dict[str, Any]] = []
    hash_rows: list[dict[str, Any]] = []
    token_rows: list[dict[str, Any]] = []
    for decl, token_by_kind in sorted(by_decl.items()):
        topology: dict[str, Any] = {
            "_key": stable_key("topo", decl),
            "kind": "wireTopology",
            "decl": decl,
            "module": modules.get(decl, ""),
            "quality": "derived",
            "truthBoundary": "derived projection; raw Lean evidence remains ig_nodes/ig_edges",
        }
        for hash_kind in HASH_KINDS:
            tokens = sorted(token_by_kind[hash_kind])
            hash_value = stable_hash(hash_kind, decl if hash_kind == "ownerAwareHash" else "", json.dumps(tokens, sort_keys=True))
            topology[hash_kind] = hash_value
            topology[hash_kind + "Tokens"] = tokens
            hash_key = stable_key("hash", hash_kind, hash_value)
            hash_rows.append(
                {
                    "_key": hash_key,
                    "hash": hash_value,
                    "hashKind": hash_kind,
                    "decl": decl,
                    "module": modules.get(decl, ""),
                    "normalization": hash_kind,
                    "source": "wire_topology_transform",
                    "quality": "derived",
                }
            )
            for token, multiplicity in sorted(Counter(tokens).items()):
                token_rows.append(
                    {
                        "_key": stable_key("tok", decl, hash_kind, token),
                        "kind": "logic_token",
                        "decl": decl,
                        "module": modules.get(decl, ""),
                        "hashKind": hash_kind,
                        "value": token,
                        "multiplicity": multiplicity,
                        "source": "wire_topology_transform",
                    }
                )
        topologies.append(topology)

    return topologies, hash_rows, token_rows


def transform(input_dir: Path, output_dir: Path) -> dict[str, Any]:
    nodes, edges = load_expr_graph(input_dir)
    gates, raw_to_gate = build_gates(nodes, edges)
    wires, wire_edges = build_wires_and_edges(nodes, edges, raw_to_gate)
    scc_rows, scc_edges = build_wire_scc_overlay(wires, gates, wire_edges)
    decl_topologies, hashes, logic_tokens = build_decl_topologies(nodes, gates, wires, wire_edges)

    counts = {
        "ig_wires": write_jsonl(output_dir / "ig_wires.jsonl", wires),
        "ig_gates": write_jsonl(output_dir / "ig_gates.jsonl", gates),
        "ig_wire_edges": write_jsonl(output_dir / "ig_wire_edges.jsonl", wire_edges),
        "ig_scc": write_jsonl(output_dir / "ig_scc.jsonl", scc_rows),
        "ig_scc_edges": write_jsonl(output_dir / "ig_scc_edges.jsonl", scc_edges),
        "ig_decl_topologies": write_jsonl(output_dir / "ig_decl_topologies.jsonl", decl_topologies),
        "ig_hashes": write_jsonl(output_dir / "ig_hashes.jsonl", hashes),
        "ig_logic_tokens": write_jsonl(output_dir / "ig_logic_tokens.jsonl", logic_tokens),
    }
    metadata = {
        "schema": "info_geometry.wire_topology_transform.v1",
        "generated_at": utc_now_iso(),
        "input_dir": str(input_dir),
        "output_dir": str(output_dir),
        "raw_node_count": len(nodes),
        "raw_edge_count": len(edges),
        "counts": counts,
        "truth_boundary": "derived projection; raw Lean evidence remains ig_nodes/ig_edges",
    }
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "metadata.json").write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return metadata


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=DEFAULT_INPUT_DIR)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    metadata = transform(args.input_dir, args.output_dir)
    print(json.dumps(metadata, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
