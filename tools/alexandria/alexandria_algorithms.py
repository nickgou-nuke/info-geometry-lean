#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any

SCHEMA = "info_geometry.alexandria_algorithms.v1"
ANCHOR_TYPES = {"theorem", "theorem_name", "module", "identifier"}
WEAK_TYPES = {"tooling", "symbol"}
DEFECT_SEVERITY = {
    "weak_anchor_chain": 4,
    "tooling_overweight": 3,
    "rhetorical_drift": 3,
    "notation_without_anchor": 2,
    "cross_document_bleed": 2,
}


@dataclass(frozen=True)
class AlexandriaGraph:
    chunks: list[dict[str, Any]]
    chunk_index: dict[str, int]
    chunk_keys: list[str]
    forward: list[list[int]]
    preds: list[list[int]]
    edge_weights: dict[tuple[int, int], float]
    entities_by_chunk: dict[str, list[dict[str, Any]]]
    canonical_entities: dict[str, list[dict[str, Any]]]
    canonical_to_chunks: dict[str, list[str]]


def stable_hash(obj: Any) -> str:
    payload = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.blake2b(payload.encode("utf-8"), digest_size=16).hexdigest()


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


def chunk_key_from_doc_id(doc_id: str) -> str:
    return doc_id.split("/", 1)[1] if "/" in doc_id else doc_id


def canonical_entity_key(entity: dict[str, Any]) -> str:
    return f"{entity.get('entityType','entity')}::{str(entity.get('normalized','')).lower()}"


def build_graph(root: Path) -> AlexandriaGraph:
    chunks = read_jsonl(root / "alexandria_chunks.jsonl")
    chunk_entities = read_jsonl(root / "alexandria_chunk_entity_edges.jsonl")
    entities = read_jsonl(root / "alexandria_entities.jsonl")
    adjacent = read_jsonl(root / "alexandria_chunk_adjacent_edges.jsonl")
    relations = read_jsonl(root / "alexandria_entity_relation_edges.jsonl")

    chunk_index = {row["_key"]: i for i, row in enumerate(chunks)}
    chunk_keys = [row["_key"] for row in chunks]
    forward_sets: list[set[int]] = [set() for _ in chunks]
    pred_sets: list[set[int]] = [set() for _ in chunks]
    edge_weights: dict[tuple[int, int], float] = {}

    for edge in adjacent:
        src = chunk_index.get(chunk_key_from_doc_id(edge["_from"]))
        dst = chunk_index.get(chunk_key_from_doc_id(edge["_to"]))
        if src is None or dst is None or src == dst:
            continue
        weight = float(edge.get("weight", 1.0))
        forward_sets[src].add(dst)
        pred_sets[dst].add(src)
        edge_weights[(src, dst)] = max(edge_weights.get((src, dst), 0.0), weight)
        forward_sets[dst].add(src)
        pred_sets[src].add(dst)
        edge_weights[(dst, src)] = max(edge_weights.get((dst, src), 0.0), weight)

    entity_by_key = {row["_key"]: row for row in entities}
    entities_by_chunk: dict[str, list[dict[str, Any]]] = defaultdict(list)
    entity_to_chunks: dict[str, list[str]] = defaultdict(list)
    canonical_entities: dict[str, list[dict[str, Any]]] = defaultdict(list)
    canonical_to_chunks: dict[str, list[str]] = defaultdict(list)

    for edge in chunk_entities:
        chunk_key = chunk_key_from_doc_id(edge["_from"])
        entity_key = chunk_key_from_doc_id(edge["_to"])
        entity = entity_by_key.get(entity_key)
        if not entity:
            continue
        entities_by_chunk[chunk_key].append(entity)
        entity_to_chunks[entity_key].append(chunk_key)
        canonical = canonical_entity_key(entity)
        canonical_entities[canonical].append(entity)
        canonical_to_chunks[canonical].append(chunk_key)

    for canonical, bucket in canonical_entities.items():
        linked_chunks = sorted(set(canonical_to_chunks.get(canonical, [])))
        if len(linked_chunks) < 2:
            continue
        representative = max(bucket, key=lambda row: float(row.get("confidence", 0.0)))
        base_weight = 0.35 + float(representative.get("confidence", 0.0))
        if representative.get("entityType") in ANCHOR_TYPES:
            base_weight += 0.35
        if representative.get("entityType") in WEAK_TYPES:
            base_weight -= 0.15
        for i, src_key in enumerate(linked_chunks):
            src = chunk_index.get(src_key)
            if src is None:
                continue
            for dst_key in linked_chunks[i + 1:]:
                dst = chunk_index.get(dst_key)
                if dst is None or src == dst:
                    continue
                forward_sets[src].add(dst)
                pred_sets[dst].add(src)
                forward_sets[dst].add(src)
                pred_sets[src].add(dst)
                edge_weights[(src, dst)] = max(edge_weights.get((src, dst), 0.0), base_weight)
                edge_weights[(dst, src)] = max(edge_weights.get((dst, src), 0.0), base_weight)

    entity_chunk_lookup = {entity["_key"]: sorted(set(entity_to_chunks.get(entity["_key"], []))) for entity in entities}
    for relation in relations:
        src_entity = chunk_key_from_doc_id(relation["_from"])
        dst_entity = chunk_key_from_doc_id(relation["_to"])
        src_chunks = entity_chunk_lookup.get(src_entity, [])
        dst_chunks = entity_chunk_lookup.get(dst_entity, [])
        weight = float(relation.get("weight", 0.0))
        for src_key in src_chunks[:4]:
            src = chunk_index.get(src_key)
            if src is None:
                continue
            for dst_key in dst_chunks[:4]:
                dst = chunk_index.get(dst_key)
                if dst is None or src == dst:
                    continue
                forward_sets[src].add(dst)
                pred_sets[dst].add(src)
                edge_weights[(src, dst)] = max(edge_weights.get((src, dst), 0.0), weight)

    return AlexandriaGraph(
        chunks=chunks,
        chunk_index=chunk_index,
        chunk_keys=chunk_keys,
        forward=[sorted(xs) for xs in forward_sets],
        preds=[sorted(xs) for xs in pred_sets],
        edge_weights=edge_weights,
        entities_by_chunk=dict(entities_by_chunk),
        canonical_entities=dict(canonical_entities),
        canonical_to_chunks={key: sorted(set(value)) for key, value in canonical_to_chunks.items()},
    )


def anchor_seed_indices(graph: AlexandriaGraph) -> list[int]:
    scored: list[tuple[float, int]] = []
    for idx, chunk in enumerate(graph.chunks):
        entities = graph.entities_by_chunk.get(chunk["_key"], [])
        score = 0.0
        for entity in entities:
            conf = float(entity.get("confidence", 0.0))
            etype = str(entity.get("entityType", ""))
            if etype in ANCHOR_TYPES:
                score += 1.5 * conf
            elif etype == "math_notation":
                score += 0.5 * conf
        if score > 0:
            scored.append((score, idx))
    return [idx for _score, idx in sorted(scored, reverse=True)]


def neighbor_affinity(graph: AlexandriaGraph, src: int, dst: int) -> float:
    direct = max(graph.edge_weights.get((src, dst), 0.0), graph.edge_weights.get((dst, src), 0.0))
    src_entities = graph.entities_by_chunk.get(graph.chunk_keys[src], [])
    dst_entities = graph.entities_by_chunk.get(graph.chunk_keys[dst], [])
    src_anchor = {canonical_entity_key(entity) for entity in src_entities if entity.get("entityType") in ANCHOR_TYPES}
    dst_anchor = {canonical_entity_key(entity) for entity in dst_entities if entity.get("entityType") in ANCHOR_TYPES}
    shared_anchor = len(src_anchor & dst_anchor)
    return direct + 0.6 * shared_anchor


def anchor_seeded_basins(graph: AlexandriaGraph, *, absorb_threshold: float = 1.1) -> list[list[int]]:
    seeds = anchor_seed_indices(graph)
    if not seeds:
        return [list(range(len(graph.chunks)))] if graph.chunks else []

    basin_of: dict[int, int] = {}
    basins: list[set[int]] = []
    seed_to_basin: dict[int, int] = {}

    for seed in seeds:
        if seed in basin_of:
            continue
        basin_id = len(basins)
        seed_to_basin[seed] = basin_id
        basins.append({seed})
        basin_of[seed] = basin_id
        queue: deque[int] = deque([seed])
        while queue:
            u = queue.popleft()
            for v in set(graph.forward[u] + graph.preds[u]):
                if v in basin_of:
                    continue
                if neighbor_affinity(graph, u, v) < absorb_threshold:
                    continue
                basin_of[v] = basin_id
                basins[basin_id].add(v)
                queue.append(v)

    for idx in range(len(graph.chunks)):
        if idx in basin_of:
            continue
        best_basin: int | None = None
        best_score = 0.0
        for basin_id, members in enumerate(basins):
            score = max((neighbor_affinity(graph, idx, member) for member in members), default=0.0)
            if score > best_score:
                best_score = score
                best_basin = basin_id
        if best_basin is not None and best_score >= 0.9:
            basin_of[idx] = best_basin
            basins[best_basin].add(idx)
        else:
            basin_id = len(basins)
            basin_of[idx] = basin_id
            basins.append({idx})

    return [sorted(basin) for basin in basins if basin]


def basin_seed_score(chunk: dict[str, Any], entities: list[dict[str, Any]]) -> float:
    lexical = len(set(chunk.get("tokens", []))) / 50.0
    entity_score = 0.0
    for entity in entities:
        conf = float(entity.get("confidence", 0.0))
        etype = str(entity.get("entityType", ""))
        if etype in ANCHOR_TYPES:
            entity_score += 1.2 * conf
        elif etype in WEAK_TYPES:
            entity_score += 0.4 * conf
        else:
            entity_score += 0.8 * conf
    return lexical + entity_score


def detect_defects(component_chunks: list[dict[str, Any]], component_entities: list[dict[str, Any]]) -> list[str]:
    tags: list[str] = []
    counts = Counter(entity.get("entityType") for entity in component_entities)
    anchor_count = sum(counts.get(kind, 0) for kind in ANCHOR_TYPES)
    weak_count = sum(counts.get(kind, 0) for kind in WEAK_TYPES)
    notation_count = counts.get("math_notation", 0)
    docs = {chunk.get("documentKey") for chunk in component_chunks}
    theoremish = sum(1 for chunk in component_chunks if chunk.get("chunkKind") in {"theorem", "proof", "hypothesis", "definition"})

    if anchor_count == 0:
        tags.append("weak_anchor_chain")
    if weak_count > max(3, anchor_count * 2):
        tags.append("tooling_overweight")
    if notation_count > 0 and anchor_count == 0:
        tags.append("notation_without_anchor")
    if len(docs) >= 3 and anchor_count <= 1:
        tags.append("cross_document_bleed")
    if theoremish == 0:
        tags.append("rhetorical_drift")
    return tags


def defect_cost(tags: list[str]) -> int:
    return sum(DEFECT_SEVERITY.get(tag, 1) for tag in tags)


def component_docs(graph: AlexandriaGraph, components: list[list[int]], *, run_id: str) -> list[dict[str, Any]]:
    docs: list[dict[str, Any]] = []
    for order, comp in enumerate(sorted(components, key=len, reverse=True), start=1):
        chunk_rows = [graph.chunks[i] for i in comp]
        entity_rows = [entity for chunk in chunk_rows for entity in graph.entities_by_chunk.get(chunk["_key"], [])]
        defects = detect_defects(chunk_rows, entity_rows)
        dominant_entities = Counter(canonical_entity_key(entity) for entity in entity_rows).most_common(8)
        anchor_chunks = [chunk for chunk in chunk_rows if any(entity.get("entityType") in ANCHOR_TYPES for entity in graph.entities_by_chunk.get(chunk["_key"], []))]
        representative = max(chunk_rows, key=lambda row: basin_seed_score(row, graph.entities_by_chunk.get(row["_key"], [])))
        docs.append(
            {
                "_key": f"basin_{order:04d}",
                "schema": SCHEMA,
                "run_id": run_id,
                "basin_rank": order,
                "member_chunk_keys": [chunk["_key"] for chunk in chunk_rows],
                "member_count": len(chunk_rows),
                "document_keys": sorted({str(chunk.get("documentKey")) for chunk in chunk_rows}),
                "representative_chunk_key": representative["_key"],
                "representative_title": representative.get("title"),
                "dominant_entities": [{"canonical": name, "count": count} for name, count in dominant_entities],
                "anchor_chunk_keys": [chunk["_key"] for chunk in anchor_chunks[:12]],
                "anchor_count": len(anchor_chunks),
                "defect_tags": defects,
                "defect_cost": defect_cost(defects),
                "labels": ["overlay:alexandria_basin", "truth_status:derived_navigation"],
            }
        )
    return docs


def entity_overlay_docs(graph: AlexandriaGraph, *, run_id: str) -> list[dict[str, Any]]:
    docs: list[dict[str, Any]] = []
    for canonical, bucket in sorted(graph.canonical_entities.items(), key=lambda item: (-len(item[1]), item[0])):
        representative = max(bucket, key=lambda row: float(row.get("confidence", 0.0)))
        docs.append(
            {
                "_key": stable_hash([canonical, representative.get("entityType")]),
                "schema": SCHEMA,
                "run_id": run_id,
                "canonical": canonical,
                "entity_type": representative.get("entityType"),
                "normalized": representative.get("normalized"),
                "confidence": representative.get("confidence"),
                "support_count": len(bucket),
                "chunk_keys": sorted({entity.get("chunkKey") for entity in bucket}),
                "domain": representative.get("domain"),
                "labels": ["overlay:alexandria_entity_cluster"],
            }
        )
    return docs


def basin_edge_docs(graph: AlexandriaGraph, basins: list[dict[str, Any]], *, run_id: str) -> list[dict[str, Any]]:
    chunk_to_basin: dict[str, str] = {}
    for basin in basins:
        for chunk_key in basin.get("member_chunk_keys", []):
            chunk_to_basin[chunk_key] = basin["_key"]
    weights: dict[tuple[str, str], float] = defaultdict(float)
    for (src, dst), weight in graph.edge_weights.items():
        src_basin = chunk_to_basin.get(graph.chunk_keys[src])
        dst_basin = chunk_to_basin.get(graph.chunk_keys[dst])
        if not src_basin or not dst_basin or src_basin == dst_basin:
            continue
        weights[(src_basin, dst_basin)] = max(weights[(src_basin, dst_basin)], weight)
    docs: list[dict[str, Any]] = []
    for (src_basin, dst_basin), weight in sorted(weights.items()):
        docs.append(
            {
                "_key": f"{src_basin}__to__{dst_basin}",
                "_from": f"alexandria_basins/{src_basin}",
                "_to": f"alexandria_basins/{dst_basin}",
                "schema": SCHEMA,
                "run_id": run_id,
                "weight": weight,
                "labels": ["overlay:alexandria_basin_link"],
            }
        )
    return docs


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Build Alexandria retrieval overlay algorithms from local JSONL artifacts")
    ap.add_argument("--input-dir", required=True)
    ap.add_argument("--output-dir", help="defaults to <input-dir>/overlay")
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    input_dir = Path(args.input_dir)
    output_dir = Path(args.output_dir) if args.output_dir else input_dir / "overlay"
    graph = build_graph(input_dir)
    components = anchor_seeded_basins(graph)
    run_id = stable_hash({"input": str(input_dir), "components": len(components), "chunks": len(graph.chunks)})

    basin_rows = component_docs(graph, components, run_id=run_id)
    entity_rows = entity_overlay_docs(graph, run_id=run_id)
    basin_edge_rows = basin_edge_docs(graph, basin_rows, run_id=run_id)
    summary = {
        "schema": SCHEMA,
        "run_id": run_id,
        "chunk_count": len(graph.chunks),
        "component_count": len(components),
        "canonical_entity_count": len(graph.canonical_entities),
        "top_basins": [
            {
                "basin": row["_key"],
                "member_count": row["member_count"],
                "representative_title": row["representative_title"],
                "defect_tags": row["defect_tags"],
            }
            for row in basin_rows[:12]
        ],
    }

    write_jsonl(output_dir / "alexandria_basins.jsonl", basin_rows)
    write_jsonl(output_dir / "alexandria_entity_clusters.jsonl", entity_rows)
    write_jsonl(output_dir / "alexandria_basin_edges.jsonl", basin_edge_rows)
    (output_dir / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
