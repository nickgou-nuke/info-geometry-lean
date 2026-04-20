#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

ANCHOR_ENTITY_TYPES = {"theorem", "theorem_name", "module"}
WEAK_ENTITY_TYPES = {"tooling", "symbol"}


def maybe_enable_gpu_backend(use_gpu: bool) -> None:
    if not use_gpu:
        return
    os.environ.setdefault("NETWORKX_BACKEND_PRIORITY_ALGOS", "cugraph")
    os.environ.setdefault("NETWORKX_BACKEND_PRIORITY_GENERATORS", "cugraph")
    os.environ.setdefault("NETWORKX_FALLBACK_TO_NX", "true")
    os.environ.setdefault("NETWORKX_CACHE_CONVERTED_GRAPHS", "true")


def tokenize(text: str) -> set[str]:
    return {tok.lower() for tok in re.findall(r"[A-Za-z][A-Za-z0-9_]{2,}", text)}


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def lexical_score(query_tokens: set[str], chunk: dict[str, Any]) -> int:
    return len(query_tokens & set(chunk.get("tokens", [])))


def chunk_key_from_doc_id(doc_id: str) -> str:
    return doc_id.split("/", 1)[1] if "/" in doc_id else doc_id


def entity_bonus(entity: dict[str, Any]) -> float:
    confidence = float(entity.get("confidence", 0.5))
    entity_type = str(entity.get("entityType", ""))
    if entity_type in ANCHOR_ENTITY_TYPES:
        return 1.2 * confidence
    if entity_type in WEAK_ENTITY_TYPES:
        return 0.7 * confidence
    return 0.95 * confidence


def build_graph(
    nx: Any,
    chunks: list[dict[str, Any]],
    entities: list[dict[str, Any]],
    chunk_entities: list[dict[str, Any]],
    adjacent: list[dict[str, Any]],
    entity_relations: list[dict[str, Any]],
):
    graph = nx.DiGraph()
    for chunk in chunks:
        graph.add_node(chunk["_key"], kind="chunk", **chunk)

    for edge in adjacent:
        src = chunk_key_from_doc_id(edge["_from"])
        dst = chunk_key_from_doc_id(edge["_to"])
        weight = float(edge.get("weight", 1.0))
        if src in graph and dst in graph:
            graph.add_edge(src, dst, kind="adjacent", weight=weight)
            graph.add_edge(dst, src, kind="adjacent", weight=weight)

    entity_by_key = {row["_key"]: row for row in entities}
    entity_to_chunks: dict[str, list[str]] = defaultdict(list)
    for edge in chunk_entities:
        chunk_key = chunk_key_from_doc_id(edge["_from"])
        entity_key = chunk_key_from_doc_id(edge["_to"])
        entity_to_chunks[entity_key].append(chunk_key)

    for entity_key, linked_chunks in entity_to_chunks.items():
        unique = list(dict.fromkeys(linked_chunks))
        entity = entity_by_key.get(entity_key, {})
        shared_weight = entity_bonus(entity)
        for i, src in enumerate(unique):
            for dst in unique[i + 1:]:
                if src in graph and dst in graph:
                    graph.add_edge(src, dst, kind="shared_entity", weight=shared_weight)
                    graph.add_edge(dst, src, kind="shared_entity", weight=shared_weight)

    for relation in entity_relations:
        src_entity = entity_by_key.get(chunk_key_from_doc_id(relation["_from"]), {})
        dst_entity = entity_by_key.get(chunk_key_from_doc_id(relation["_to"]), {})
        src_chunks = entity_to_chunks.get(src_entity.get("_key", ""), [])
        dst_chunks = entity_to_chunks.get(dst_entity.get("_key", ""), [])
        weight = float(relation.get("weight", 0.4))
        for src_chunk in src_chunks[:4]:
            for dst_chunk in dst_chunks[:4]:
                if src_chunk == dst_chunk or src_chunk not in graph or dst_chunk not in graph:
                    continue
                current = float(graph[src_chunk][dst_chunk]["weight"]) if graph.has_edge(src_chunk, dst_chunk) else 0.0
                merged = max(current, weight)
                graph.add_edge(src_chunk, dst_chunk, kind="entity_relation", weight=merged)

    return graph


def personalized_scores(graph, seeds: dict[str, float], *, steps: int = 12, alpha: float = 0.85) -> dict[str, float]:
    scores = {node: 0.0 for node in graph.nodes}
    total = sum(float(value) for value in seeds.values())
    if total <= 0:
        return {}
    base = {
        node: (float(seeds.get(node, 0.0)) / total) if node in graph else 0.0
        for node in graph.nodes
    }
    scores.update(base)
    for _ in range(steps):
        next_scores = {node: (1.0 - alpha) * base[node] for node in graph.nodes}
        for node in graph.nodes:
            outgoing = list(graph.successors(node))
            if not outgoing:
                next_scores[node] += alpha * scores[node]
                continue
            total_weight = sum(float(graph[node][dst].get("weight", 1.0)) for dst in outgoing)
            if total_weight <= 0:
                next_scores[node] += alpha * scores[node]
                continue
            for dst in outgoing:
                weight = float(graph[node][dst].get("weight", 1.0))
                next_scores[dst] += alpha * scores[node] * (weight / total_weight)
        scores = next_scores
    return scores


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Rank Alexandria context with lexical seeds plus graph expansion")
    ap.add_argument("--query", required=True)
    ap.add_argument("--input-dir", required=True)
    ap.add_argument("--top-k", type=int, default=8)
    ap.add_argument("--seed-k", type=int, default=5)
    ap.add_argument("--use-gpu", action="store_true")
    ap.add_argument("--json-out", type=Path)
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    maybe_enable_gpu_backend(bool(args.use_gpu))

    try:
        import networkx as nx  # type: ignore
    except Exception as exc:
        print(json.dumps({"error": f"failed to import networkx: {exc}"}, indent=2), file=sys.stderr)
        return 1

    root = Path(args.input_dir)
    chunks = read_jsonl(root / "alexandria_chunks.jsonl")
    entities = read_jsonl(root / "alexandria_entities.jsonl")
    chunk_entities = read_jsonl(root / "alexandria_chunk_entity_edges.jsonl")
    adjacent = read_jsonl(root / "alexandria_chunk_adjacent_edges.jsonl")
    entity_relations = read_jsonl(root / "alexandria_entity_relation_edges.jsonl")

    graph = build_graph(nx, chunks, entities, chunk_entities, adjacent, entity_relations)
    query_tokens = tokenize(args.query)
    lexical_ranked = sorted(chunks, key=lambda row: (lexical_score(query_tokens, row), len(row.get("tokens", []))), reverse=True)
    seeds = {
        row["_key"]: float(lexical_score(query_tokens, row))
        for row in lexical_ranked[: args.seed_k]
        if lexical_score(query_tokens, row) > 0
    }
    pr = personalized_scores(graph, seeds)

    entity_by_key = {row["_key"]: row for row in entities}
    entities_for_chunk: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in chunk_entities:
        chunk_key = chunk_key_from_doc_id(edge["_from"])
        entity_key = chunk_key_from_doc_id(edge["_to"])
        entity = entity_by_key.get(entity_key)
        if entity:
            entities_for_chunk[chunk_key].append(entity)

    results = sorted(
        chunks,
        key=lambda row: (pr.get(row["_key"], 0.0), lexical_score(query_tokens, row), len(row.get("tokens", []))),
        reverse=True,
    )

    packet = {
        "query": args.query,
        "queryTokens": sorted(query_tokens),
        "graph": {
            "nodeCount": graph.number_of_nodes(),
            "edgeCount": graph.number_of_edges(),
            "useGpuRequested": bool(args.use_gpu),
            "backendPriorityAlgos": list(getattr(getattr(nx.config, "backend_priority", object()), "algos", [])) if hasattr(nx, "config") else [],
            "backendPriorityGenerators": list(getattr(getattr(nx.config, "backend_priority", object()), "generators", [])) if hasattr(nx, "config") else [],
        },
        "seeds": [{"chunkKey": key, "lexicalScore": value} for key, value in sorted(seeds.items(), key=lambda item: item[1], reverse=True)],
        "hits": [
            {
                "chunk": row,
                "graphScore": pr.get(row["_key"], 0.0),
                "lexicalScore": lexical_score(query_tokens, row),
                "entities": sorted(entities_for_chunk.get(row["_key"], []), key=lambda ent: (ent.get("confidence", 0.0), ent.get("entityType", "")), reverse=True),
                "neighbors": [graph.nodes[n] for n in list(graph.successors(row["_key"]))[:6] if n in graph.nodes],
            }
            for row in results[: args.top_k]
            if pr.get(row["_key"], 0.0) > 0 or lexical_score(query_tokens, row) > 0
        ],
    }

    rendered = json.dumps(packet, ensure_ascii=False, indent=2)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(rendered + "\n", encoding="utf-8")
    else:
        print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
