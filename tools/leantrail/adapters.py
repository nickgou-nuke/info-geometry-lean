#!/usr/bin/env python3
from __future__ import annotations

import csv
import hashlib
import json
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any

from leantrail.backend.models import EdgeRecord, GraphSnapshot, NodeRecord

GRAPHML_NS = "http://graphml.graphdrawing.org/xmlns"
_NS = {"g": GRAPHML_NS}


def load_snapshot(path: Path) -> GraphSnapshot:
    payload = json.loads(path.read_text(encoding="utf-8"))
    return GraphSnapshot.from_dict(payload)


def save_snapshot(snapshot: GraphSnapshot, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(snapshot.to_dict(), indent=2, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )


def _json_text(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, separators=(",", ":"))


def _parse_json_text(value: str | None, default: Any) -> Any:
    if not value:
        return default
    try:
        return json.loads(value)
    except Exception:
        return default


def _iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            s = line.strip()
            if not s:
                continue
            try:
                obj = json.loads(s)
            except Exception:
                continue
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def _stable_key(node_id: str) -> str:
    digest = hashlib.sha1(node_id.encode("utf-8")).hexdigest()
    return f"n_{digest[:24]}"


def export_graphml(snapshot: GraphSnapshot, out_path: Path) -> None:
    ET.register_namespace("", GRAPHML_NS)
    root = ET.Element(f"{{{GRAPHML_NS}}}graphml")

    key_specs: list[tuple[str, str, str, str]] = [
        ("k_graph_metadata_json", "graph", "metadata_json", "string"),
        ("k_node_id", "node", "id", "string"),
        ("k_node_name", "node", "name", "string"),
        ("k_node_kind", "node", "kind", "string"),
        ("k_node_module", "node", "module", "string"),
        ("k_node_file", "node", "file", "string"),
        ("k_node_line", "node", "line", "string"),
        ("k_node_rep_depth", "node", "rep_depth", "string"),
        ("k_node_role", "node", "role", "string"),
        ("k_node_module_family", "node", "module_family", "string"),
        ("k_node_commit_sha", "node", "commit_sha", "string"),
        ("k_node_toolchain", "node", "toolchain", "string"),
        ("k_node_artifact_version", "node", "artifact_version", "string"),
        ("k_node_attrs_json", "node", "attrs_json", "string"),
        ("k_edge_src", "edge", "src", "string"),
        ("k_edge_dst", "edge", "dst", "string"),
        ("k_edge_kind", "edge", "kind", "string"),
        ("k_edge_weight", "edge", "weight", "string"),
        ("k_edge_evidence_ref", "edge", "evidence_ref", "string"),
        ("k_edge_attrs_json", "edge", "attrs_json", "string"),
    ]

    for key_id, for_kind, attr_name, attr_type in key_specs:
        ET.SubElement(
            root,
            f"{{{GRAPHML_NS}}}key",
            {
                "id": key_id,
                "for": for_kind,
                "attr.name": attr_name,
                "attr.type": attr_type,
            },
        )

    graph = ET.SubElement(root, f"{{{GRAPHML_NS}}}graph", {"id": "G", "edgedefault": "directed"})
    data_meta = ET.SubElement(graph, f"{{{GRAPHML_NS}}}data", {"key": "k_graph_metadata_json"})
    data_meta.text = _json_text(snapshot.metadata)

    xml_id_by_node_id: dict[str, str] = {}
    for idx, node in enumerate(snapshot.nodes):
        xml_id = f"n{idx}"
        xml_id_by_node_id[node.id] = xml_id
        elem = ET.SubElement(graph, f"{{{GRAPHML_NS}}}node", {"id": xml_id})
        fields = {
            "k_node_id": node.id,
            "k_node_name": node.name,
            "k_node_kind": node.kind,
            "k_node_module": node.module,
            "k_node_file": node.file or "",
            "k_node_line": "" if node.line is None else str(node.line),
            "k_node_rep_depth": node.rep_depth or "",
            "k_node_role": node.role or "",
            "k_node_module_family": node.module_family or "",
            "k_node_commit_sha": node.commit_sha,
            "k_node_toolchain": node.toolchain,
            "k_node_artifact_version": str(node.artifact_version),
            "k_node_attrs_json": _json_text(node.attrs),
        }
        for key, value in fields.items():
            data = ET.SubElement(elem, f"{{{GRAPHML_NS}}}data", {"key": key})
            data.text = value

    for idx, edge in enumerate(snapshot.edges):
        src_xml = xml_id_by_node_id.get(edge.src)
        dst_xml = xml_id_by_node_id.get(edge.dst)
        if src_xml is None or dst_xml is None:
            continue
        elem = ET.SubElement(
            graph,
            f"{{{GRAPHML_NS}}}edge",
            {"id": f"e{idx}", "source": src_xml, "target": dst_xml},
        )
        fields = {
            "k_edge_src": edge.src,
            "k_edge_dst": edge.dst,
            "k_edge_kind": edge.kind,
            "k_edge_weight": str(edge.weight),
            "k_edge_evidence_ref": edge.evidence_ref,
            "k_edge_attrs_json": _json_text(edge.attrs),
        }
        for key, value in fields.items():
            data = ET.SubElement(elem, f"{{{GRAPHML_NS}}}data", {"key": key})
            data.text = value

    out_path.parent.mkdir(parents=True, exist_ok=True)
    tree = ET.ElementTree(root)
    tree.write(out_path, encoding="utf-8", xml_declaration=True)


def import_graphml(path: Path) -> GraphSnapshot:
    tree = ET.parse(path)
    root = tree.getroot()

    key_to_attr: dict[str, str] = {}
    for key in root.findall("g:key", _NS):
        key_id = key.get("id", "")
        attr_name = key.get("attr.name", "")
        if key_id and attr_name:
            key_to_attr[key_id] = attr_name

    graph = root.find("g:graph", _NS)
    if graph is None:
        return GraphSnapshot(metadata={}, nodes=[], edges=[])

    metadata: dict[str, Any] = {}
    for data in graph.findall("g:data", _NS):
        key_id = data.get("key", "")
        attr_name = key_to_attr.get(key_id)
        if attr_name == "metadata_json":
            metadata = _parse_json_text(data.text, {})
            break

    node_id_by_xml_id: dict[str, str] = {}
    nodes: list[NodeRecord] = []
    for node_elem in graph.findall("g:node", _NS):
        xml_id = node_elem.get("id", "")
        fields: dict[str, str] = {}
        for data in node_elem.findall("g:data", _NS):
            key_id = data.get("key", "")
            attr_name = key_to_attr.get(key_id)
            if attr_name:
                fields[attr_name] = data.text or ""

        node_id = fields.get("id", "") or xml_id
        node_id_by_xml_id[xml_id] = node_id

        line_raw = fields.get("line", "").strip()
        artifact_raw = fields.get("artifact_version", "").strip()

        nodes.append(
            NodeRecord(
                id=node_id,
                name=fields.get("name", node_id),
                kind=fields.get("kind", "Declaration"),
                module=fields.get("module", ""),
                file=fields.get("file") or None,
                line=int(line_raw) if line_raw else None,
                rep_depth=fields.get("rep_depth") or None,
                role=fields.get("role") or None,
                module_family=fields.get("module_family") or None,
                commit_sha=fields.get("commit_sha", "unknown"),
                toolchain=fields.get("toolchain", "unknown"),
                artifact_version=int(artifact_raw) if artifact_raw else 0,
                attrs=_parse_json_text(fields.get("attrs_json"), {}),
            )
        )

    edges: list[EdgeRecord] = []
    for edge_elem in graph.findall("g:edge", _NS):
        source_xml = edge_elem.get("source", "")
        target_xml = edge_elem.get("target", "")
        fields: dict[str, str] = {}
        for data in edge_elem.findall("g:data", _NS):
            key_id = data.get("key", "")
            attr_name = key_to_attr.get(key_id)
            if attr_name:
                fields[attr_name] = data.text or ""

        src = fields.get("src", "") or node_id_by_xml_id.get(source_xml, source_xml)
        dst = fields.get("dst", "") or node_id_by_xml_id.get(target_xml, target_xml)
        if not src or not dst:
            continue
        weight_raw = fields.get("weight", "").strip()

        edges.append(
            EdgeRecord(
                src=src,
                dst=dst,
                kind=fields.get("kind", "depends_value"),
                weight=float(weight_raw) if weight_raw else 1.0,
                evidence_ref=fields.get("evidence_ref", ""),
                attrs=_parse_json_text(fields.get("attrs_json"), {}),
            )
        )

    return GraphSnapshot(metadata=metadata, nodes=nodes, edges=edges)


def export_neo4j_csv(snapshot: GraphSnapshot, out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)

    nodes_csv = out_dir / "nodes.csv"
    edges_csv = out_dir / "edges.csv"
    meta_json = out_dir / "metadata.json"

    node_fields = [
        "id:ID",
        "name",
        "kind",
        "module",
        "file",
        "line:int",
        "rep_depth",
        "role",
        "module_family",
        "commit_sha",
        "toolchain",
        "artifact_version:int",
        "attrs_json",
        ":LABEL",
    ]
    with nodes_csv.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=node_fields, quoting=csv.QUOTE_ALL)
        writer.writeheader()
        for node in snapshot.nodes:
            writer.writerow(
                {
                    "id:ID": node.id,
                    "name": node.name,
                    "kind": node.kind,
                    "module": node.module,
                    "file": node.file or "",
                    "line:int": "" if node.line is None else str(node.line),
                    "rep_depth": node.rep_depth or "",
                    "role": node.role or "",
                    "module_family": node.module_family or "",
                    "commit_sha": node.commit_sha,
                    "toolchain": node.toolchain,
                    "artifact_version:int": str(node.artifact_version),
                    "attrs_json": _json_text(node.attrs),
                    ":LABEL": node.kind or "Node",
                }
            )

    edge_fields = [
        ":START_ID",
        ":END_ID",
        "kind",
        "weight:float",
        "evidence_ref",
        "attrs_json",
        ":TYPE",
    ]
    with edges_csv.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=edge_fields, quoting=csv.QUOTE_ALL)
        writer.writeheader()
        for edge in snapshot.edges:
            writer.writerow(
                {
                    ":START_ID": edge.src,
                    ":END_ID": edge.dst,
                    "kind": edge.kind,
                    "weight:float": str(edge.weight),
                    "evidence_ref": edge.evidence_ref,
                    "attrs_json": _json_text(edge.attrs),
                    ":TYPE": edge.kind or "REL",
                }
            )

    meta_json.write_text(_json_text(snapshot.metadata) + "\n", encoding="utf-8")


def import_neo4j_csv(path: Path) -> GraphSnapshot:
    if path.is_file():
        out_dir = path.parent
    else:
        out_dir = path

    nodes_csv = out_dir / "nodes.csv"
    edges_csv = out_dir / "edges.csv"
    meta_json = out_dir / "metadata.json"

    metadata = _parse_json_text(meta_json.read_text(encoding="utf-8"), {}) if meta_json.exists() else {}

    nodes: list[NodeRecord] = []
    if nodes_csv.exists():
        with nodes_csv.open("r", encoding="utf-8", newline="") as handle:
            reader = csv.DictReader(handle)
            for row in reader:
                node_id = str(row.get("id:ID", "")).strip()
                if not node_id:
                    continue
                line_raw = str(row.get("line:int", "")).strip()
                artifact_raw = str(row.get("artifact_version:int", "")).strip()
                nodes.append(
                    NodeRecord(
                        id=node_id,
                        name=str(row.get("name", node_id)),
                        kind=str(row.get("kind", row.get(":LABEL", "Declaration"))),
                        module=str(row.get("module", "")),
                        file=(str(row.get("file", "")).strip() or None),
                        line=int(line_raw) if line_raw else None,
                        rep_depth=(str(row.get("rep_depth", "")).strip() or None),
                        role=(str(row.get("role", "")).strip() or None),
                        module_family=(str(row.get("module_family", "")).strip() or None),
                        commit_sha=str(row.get("commit_sha", "unknown")),
                        toolchain=str(row.get("toolchain", "unknown")),
                        artifact_version=int(artifact_raw) if artifact_raw else 0,
                        attrs=_parse_json_text(str(row.get("attrs_json", "")), {}),
                    )
                )

    edges: list[EdgeRecord] = []
    if edges_csv.exists():
        with edges_csv.open("r", encoding="utf-8", newline="") as handle:
            reader = csv.DictReader(handle)
            for row in reader:
                src = str(row.get(":START_ID", "")).strip()
                dst = str(row.get(":END_ID", "")).strip()
                if not src or not dst:
                    continue
                weight_raw = str(row.get("weight:float", "")).strip()
                edges.append(
                    EdgeRecord(
                        src=src,
                        dst=dst,
                        kind=str(row.get("kind", row.get(":TYPE", "depends_value"))),
                        weight=float(weight_raw) if weight_raw else 1.0,
                        evidence_ref=str(row.get("evidence_ref", "")),
                        attrs=_parse_json_text(str(row.get("attrs_json", "")), {}),
                    )
                )

    return GraphSnapshot(metadata=metadata, nodes=nodes, edges=edges)


def export_arango_json(snapshot: GraphSnapshot, out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    nodes_path = out_dir / "ig_nodes.jsonl"
    edges_path = out_dir / "ig_edges.jsonl"
    meta_path = out_dir / "metadata.json"

    key_by_node_id: dict[str, str] = {}
    with nodes_path.open("w", encoding="utf-8") as handle:
        for node in snapshot.nodes:
            key = _stable_key(node.id)
            key_by_node_id[node.id] = key
            row = {
                "_key": key,
                "id": node.id,
                "name": node.name,
                "kind": node.kind,
                "module": node.module,
                "file": node.file,
                "line": node.line,
                "rep_depth": node.rep_depth,
                "role": node.role,
                "module_family": node.module_family,
                "commit_sha": node.commit_sha,
                "toolchain": node.toolchain,
                "artifact_version": node.artifact_version,
                "attrs": node.attrs,
            }
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")

    with edges_path.open("w", encoding="utf-8") as handle:
        for idx, edge in enumerate(snapshot.edges):
            src_key = key_by_node_id.get(edge.src)
            dst_key = key_by_node_id.get(edge.dst)
            if src_key is None or dst_key is None:
                continue
            row = {
                "_key": f"e_{idx}",
                "_from": f"ig_nodes/{src_key}",
                "_to": f"ig_nodes/{dst_key}",
                "src": edge.src,
                "dst": edge.dst,
                "kind": edge.kind,
                "weight": edge.weight,
                "evidence_ref": edge.evidence_ref,
                "attrs": edge.attrs,
            }
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")

    meta_path.write_text(_json_text(snapshot.metadata) + "\n", encoding="utf-8")


def import_arango_json(path: Path) -> GraphSnapshot:
    out_dir = path if path.is_dir() else path.parent
    nodes_path = out_dir / "ig_nodes.jsonl"
    edges_path = out_dir / "ig_edges.jsonl"
    meta_path = out_dir / "metadata.json"

    metadata = _parse_json_text(meta_path.read_text(encoding="utf-8"), {}) if meta_path.exists() else {}

    nodes: list[NodeRecord] = []
    key_to_node_id: dict[str, str] = {}
    schema_version = metadata.get("schemaVersion", 0)
    artifact_version_default = int(schema_version) if isinstance(schema_version, int) else 0
    for row in _iter_jsonl(nodes_path):
        node_id = str(row.get("id", "")).strip()
        if not node_id:
            node_id = str(row.get("_key", "")).strip()
        if not node_id:
            continue
        key = str(row.get("_key", "")).strip()
        if key:
            key_to_node_id[key] = node_id
        line_raw = row.get("line")
        artifact_raw = row.get("artifact_version")
        attrs = row.get("attrs", {}) if isinstance(row.get("attrs", {}), dict) else {}
        # Preserve richer Lean ExprArangoExport attributes in a backward-compatible way.
        for extra_key in (
            "graphKind",
            "decl",
            "sectionTag",
            "path",
            "exprTag",
            "info",
            "doc",
            "deBruijnIdx",
            "shapeHash",
            "quality",
        ):
            if extra_key in row and extra_key not in attrs:
                attrs[extra_key] = row.get(extra_key)
        nodes.append(
            NodeRecord(
                id=node_id,
                name=str(row.get("name", row.get("decl", node_id))),
                kind=str(row.get("kind", "Declaration")),
                module=str(row.get("module", "")),
                file=row.get("file"),
                line=int(line_raw) if isinstance(line_raw, int) else None,
                rep_depth=(str(row.get("rep_depth", "")).strip() or None),
                role=(str(row.get("role", row.get("graphKind", ""))).strip() or None),
                module_family=(str(row.get("module_family", "")).strip() or None),
                commit_sha=str(row.get("commit_sha", "unknown")),
                toolchain=str(row.get("toolchain", "unknown")),
                artifact_version=(
                    int(artifact_raw) if isinstance(artifact_raw, int) else artifact_version_default
                ),
                attrs=attrs,
            )
        )

    edges: list[EdgeRecord] = []
    for row in _iter_jsonl(edges_path):
        src = str(row.get("src", "")).strip()
        dst = str(row.get("dst", "")).strip()

        if not src or not dst:
            from_raw = str(row.get("_from", "")).strip()
            to_raw = str(row.get("_to", "")).strip()
            if "/" in from_raw and "/" in to_raw:
                src_key = from_raw.split("/", 1)[1]
                dst_key = to_raw.split("/", 1)[1]
                src = key_to_node_id.get(src_key, src)
                dst = key_to_node_id.get(dst_key, dst)

        if not src or not dst:
            continue

        weight_raw = row.get("weight")
        edge_attrs = row.get("attrs", {}) if isinstance(row.get("attrs", {}), dict) else {}
        for extra_key in ("role", "quality", "notes", "decl", "sectionTag"):
            if extra_key in row and extra_key not in edge_attrs:
                edge_attrs[extra_key] = row.get(extra_key)
        edges.append(
            EdgeRecord(
                src=src,
                dst=dst,
                kind=str(row.get("kind", "depends_value")),
                weight=float(weight_raw) if isinstance(weight_raw, (int, float)) else 1.0,
                evidence_ref=str(row.get("evidence_ref", row.get("decl", ""))),
                attrs=edge_attrs,
            )
        )

    return GraphSnapshot(metadata=metadata, nodes=nodes, edges=edges)
