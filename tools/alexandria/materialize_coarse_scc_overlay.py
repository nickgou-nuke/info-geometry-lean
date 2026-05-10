#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.alexandria.graph_context_rank import build_graph, chunk_key_from_doc_id, read_jsonl, tokenize
from tools.alexandria.schema import stable_key


def edge_preview(chunk: dict[str, Any]) -> str:
    return str(chunk.get("text", "")).replace("\n", " ")[:180]


def collect_entities_for_chunk(
    entities: list[dict[str, Any]],
    chunk_entities: list[dict[str, Any]],
) -> dict[str, list[dict[str, Any]]]:
    entity_by_key = {row["_key"]: row for row in entities}
    out: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in chunk_entities:
        chunk_key = chunk_key_from_doc_id(edge["_from"])
        entity_key = chunk_key_from_doc_id(edge["_to"])
        entity = entity_by_key.get(entity_key)
        if entity:
            out[chunk_key].append(entity)
    return out


def representative_terms(members: list[str], entities_for_chunk: dict[str, list[dict[str, Any]]]) -> list[str]:
    counts: dict[str, int] = defaultdict(int)
    for member in members:
        for entity in entities_for_chunk.get(member, []):
            term = entity.get("normalized") or entity.get("surface")
            if term:
                counts[str(term)] += 1
    return [term for term, _ in sorted(counts.items(), key=lambda item: (item[1], item[0]), reverse=True)[:16]]


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
    return len(rows)


def materialize(input_dir: Path, output_dir: Path, *, query: str, conductive: bool) -> dict[str, Any]:
    try:
        import networkx as nx  # type: ignore
    except Exception as exc:
        raise SystemExit(f"networkx is required: {exc}") from exc

    chunks = read_jsonl(input_dir / "alexandria_chunks.jsonl")
    entities = read_jsonl(input_dir / "alexandria_entities.jsonl")
    chunk_entities = read_jsonl(input_dir / "alexandria_chunk_entity_edges.jsonl")
    adjacent = read_jsonl(input_dir / "alexandria_chunk_adjacent_edges.jsonl")
    debruijn_edges = read_jsonl(input_dir / "automath_debruijn_edges.jsonl")
    entity_relations = read_jsonl(input_dir / "alexandria_entity_relation_edges.jsonl")
    query_tokens = tokenize(query)
    graph = build_graph(
        nx,
        chunks,
        entities,
        chunk_entities,
        adjacent,
        debruijn_edges,
        entity_relations,
        query_tokens=query_tokens,
        conductive=conductive,
    )
    chunk_by_key = {row["_key"]: row for row in chunks}
    entities_for_chunk = collect_entities_for_chunk(entities, chunk_entities)

    nodes: list[dict[str, Any]] = []
    membership_edges: list[dict[str, Any]] = []
    quotient_edges_by_pair: dict[tuple[str, str], dict[str, Any]] = {}
    node_to_scc: dict[str, str] = {}

    for index, members_raw in enumerate(nx.strongly_connected_components(graph), start=1):
        members = sorted(member for member in members_raw if member in chunk_by_key)
        if not members:
            continue
        scc_key = stable_key("scc", input_dir.as_posix(), index, members)
        for member in members:
            node_to_scc[member] = scc_key
        nodes.append(
            {
                "_key": scc_key,
                "schema": "info_geometry.alexandria.coarse_scc.v1",
                "componentKind": "strongly_connected_component",
                "memberCount": len(members),
                "representativeTerms": representative_terms(members, entities_for_chunk),
                "memberChunkKeys": members,
                "ancestralDepth": max(len(chunk_by_key[member].get("ancestry_path", [])) for member in members),
                "query": query,
                "conductive": conductive,
                "authority": "derived_overlay_only",
            }
        )
        for member in members:
            membership_edges.append(
                {
                    "_key": stable_key("sccmem", scc_key, member),
                    "_from": f"alexandria_coarse_scc_nodes/{scc_key}",
                    "_to": f"alexandria_chunks/{member}",
                    "schema": "info_geometry.alexandria.coarse_scc_membership.v1",
                    "role": "scc_member",
                    "chunkPreview": edge_preview(chunk_by_key[member]),
                    "authority": "derived_overlay_descent",
                }
            )

    for src, dst, data in graph.edges(data=True):
        qsrc = node_to_scc.get(src)
        qdst = node_to_scc.get(dst)
        if not qsrc or not qdst or qsrc == qdst:
            continue
        pair = (qsrc, qdst)
        weight = float(data.get("weight", 1.0))
        current = quotient_edges_by_pair.get(pair)
        if current is None or weight > float(current.get("weight", 0.0)):
            quotient_edges_by_pair[pair] = {
                "_key": stable_key("sccedge", qsrc, qdst),
                "_from": f"alexandria_coarse_scc_nodes/{qsrc}",
                "_to": f"alexandria_coarse_scc_nodes/{qdst}",
                "schema": "info_geometry.alexandria.coarse_scc_edge.v1",
                "role": "scc_quotient_flow",
                "weight": weight,
                "witnessEdgeKind": data.get("kind"),
                "authority": "derived_overlay_only",
            }

    counts = {
        "coarse_scc_nodes": write_jsonl(output_dir / "alexandria_coarse_scc_nodes.jsonl", nodes),
        "coarse_scc_membership_edges": write_jsonl(output_dir / "alexandria_coarse_scc_membership_edges.jsonl", membership_edges),
        "coarse_scc_quotient_edges": write_jsonl(output_dir / "alexandria_coarse_scc_quotient_edges.jsonl", list(quotient_edges_by_pair.values())),
    }
    summary = {
        "schema": "info_geometry.alexandria.coarse_scc_summary.v1",
        "inputDir": input_dir.as_posix(),
        "outputDir": output_dir.as_posix(),
        "query": query,
        "conductive": conductive,
        "counts": counts,
        "authority": "derived_overlay_only",
    }
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "coarse_scc_summary.json").write_text(json.dumps(summary, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description="Materialize SCC coarse-graining overlay JSONL from Alexandria artifacts.")
    parser.add_argument("--input-dir", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--query", default="")
    parser.add_argument("--conductive", action="store_true")
    args = parser.parse_args()
    print(json.dumps(materialize(args.input_dir, args.output_dir, query=args.query, conductive=bool(args.conductive)), ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
