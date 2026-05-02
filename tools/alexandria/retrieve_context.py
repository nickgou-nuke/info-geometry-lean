#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path


def tokenize(text: str) -> set[str]:
    return {tok.lower() for tok in re.findall(r"[A-Za-z][A-Za-z0-9_]{2,}", text)}


def read_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    rows: list[dict] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def score(query_tokens: set[str], chunk: dict) -> tuple[int, int]:
    tokens = set(chunk.get("tokens", []))
    overlap = query_tokens & tokens
    return (len(overlap), len(tokens))


def main() -> int:
    ap = argparse.ArgumentParser(description="Build a raw Alexandria context packet from local JSONL artifacts")
    ap.add_argument("--query", required=True)
    ap.add_argument("--input-dir", required=True)
    ap.add_argument("--top-k", type=int, default=8)
    args = ap.parse_args()

    root = Path(args.input_dir)
    chunks = read_jsonl(root / "alexandria_chunks.jsonl")
    entities = read_jsonl(root / "alexandria_entities.jsonl")
    chunk_entities = read_jsonl(root / "alexandria_chunk_entity_edges.jsonl")
    adjacent = read_jsonl(root / "alexandria_chunk_adjacent_edges.jsonl")

    query_tokens = tokenize(args.query)
    ranked = sorted(chunks, key=lambda row: score(query_tokens, row), reverse=True)
    top = [row for row in ranked if score(query_tokens, row)[0] > 0][: args.top_k]

    entity_by_key = {row["_key"]: row for row in entities}
    entities_for_chunk: dict[str, list[dict]] = defaultdict(list)
    for edge in chunk_entities:
        chunk_key = edge["_from"].split("/", 1)[1]
        entity_key = edge["_to"].split("/", 1)[1]
        entity = entity_by_key.get(entity_key)
        if entity:
            entities_for_chunk[chunk_key].append(entity)

    neighbor_map: dict[str, list[str]] = defaultdict(list)
    for edge in adjacent:
        src = edge["_from"].split("/", 1)[1]
        dst = edge["_to"].split("/", 1)[1]
        neighbor_map[src].append(dst)
        neighbor_map[dst].append(src)

    chunk_by_key = {row["_key"]: row for row in chunks}
    packet = {
        "query": args.query,
        "queryTokens": sorted(query_tokens),
        "hits": [
            {
                "chunk": chunk,
                "source": chunk.get("provenance", {}),
                "score": score(query_tokens, chunk)[0],
                "scoreBreakdown": {
                    "lexical": score(query_tokens, chunk)[0],
                    "title": 1 if any(t in chunk.get("title", "").lower() for t in query_tokens) else 0,
                },
                "entities": entities_for_chunk.get(chunk["_key"], []),
                "neighbors": [chunk_by_key[n] for n in neighbor_map.get(chunk["_key"], []) if n in chunk_by_key][:4],
            }
            for chunk in top
        ],
    }
    print(json.dumps(packet, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
