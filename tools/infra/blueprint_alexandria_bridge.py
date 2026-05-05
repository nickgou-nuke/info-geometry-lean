#!/usr/bin/env python3
"""Build Blueprint-style formalization nodes from Alexandria paper artifacts.

This turns semantic paper chunks into a small theorem/definition roadmap.  It is
not autoformalization and not proof authority; it is the planning layer that can
later be matched against the Lean DAG and queued for Hive.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.leansearch_local import DEFAULT_RECORDS, search_records


SCHEMA = "info_geometry.blueprint_alexandria_node.v1"
SUMMARY_SCHEMA = "info_geometry.blueprint_alexandria_bridge.summary.v1"
KINDS = {"theorem", "definition", "hypothesis", "proof", "remark", "chunk"}


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
    return hashlib.sha1(text.encode("utf-8")).hexdigest()


def slug(text: str) -> str:
    out = re.sub(r"[^A-Za-z0-9]+", "_", text.strip()).strip("_")
    return out[:80] or "node"


def suggested_lean_name(title: str, idx: int) -> str:
    base = slug(title)
    if not base:
        base = f"blueprint_node_{idx}"
    if not base[0].isalpha():
        base = "node_" + base
    return base[0].lower() + base[1:]


def load_entities(input_dir: Path) -> dict[str, list[dict[str, Any]]]:
    by_chunk: dict[str, list[dict[str, Any]]] = {}
    entity_by_key = {row.get("_key"): row for row in iter_jsonl(input_dir / "alexandria_entities.jsonl")}
    for edge in iter_jsonl(input_dir / "alexandria_chunk_entity_edges.jsonl"):
        chunk_key = str(edge.get("_from") or "").split("/", 1)[-1]
        entity_key = str(edge.get("_to") or "").split("/", 1)[-1]
        entity = entity_by_key.get(entity_key)
        if chunk_key and entity:
            by_chunk.setdefault(chunk_key, []).append(entity)
    return by_chunk


def candidate_decls(query: str, *, records: Path, top_k: int) -> list[dict[str, Any]]:
    if not records.exists() or top_k <= 0:
        return []
    result = search_records(records_path=records, query=query, top_k=top_k)
    out = []
    for hit in result.get("hits") or []:
        if not isinstance(hit, dict):
            continue
        out.append(
            {
                "name": hit.get("name"),
                "kind": hit.get("kind"),
                "module": hit.get("module"),
                "file": hit.get("file"),
                "line": hit.get("line"),
                "score": hit.get("score"),
                "type": hit.get("type"),
            }
        )
    return out


def build_nodes(*, input_dir: Path, records: Path, top_k: int, include_kinds: set[str], max_nodes: int | None) -> list[dict[str, Any]]:
    entities_by_chunk = load_entities(input_dir)
    nodes: list[dict[str, Any]] = []
    for idx, chunk in enumerate(iter_jsonl(input_dir / "alexandria_chunks.jsonl")):
        kind = str(chunk.get("chunkKind") or "chunk")
        if kind not in include_kinds:
            continue
        title = str(chunk.get("title") or f"Chunk {idx}")
        text = str(chunk.get("text") or "")
        entities = entities_by_chunk.get(str(chunk.get("_key") or chunk.get("key") or ""), [])
        query = " ".join([title, text[:500], " ".join(str(e.get("normalized") or e.get("surface") or "") for e in entities[:8])])
        node = {
            "schema": SCHEMA,
            "id": "blueprint:" + stable_hash(chunk.get("_key"), title, text[:200]),
            "kind": kind,
            "title": title,
            "informal_statement": text,
            "suggested_lean_name": suggested_lean_name(title, idx),
            "source_chunk": chunk.get("_key") or chunk.get("key"),
            "source": chunk.get("provenance") or {},
            "entities": [
                {
                    "type": e.get("entityType"),
                    "surface": e.get("surface"),
                    "normalized": e.get("normalized"),
                    "confidence": e.get("confidence"),
                }
                for e in entities
            ],
            "dependencies": [],
            "candidate_repo_decls": candidate_decls(query, records=records, top_k=top_k),
            "authority": {
                "blueprint_planning_only": True,
                "not_a_proof": True,
                "lean_remains_proof_authority": True,
            },
        }
        nodes.append(node)
        if max_nodes is not None and len(nodes) >= max_nodes:
            break
    return nodes


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
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--records", type=Path, default=DEFAULT_RECORDS)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--summary-out", type=Path)
    parser.add_argument("--top-k", type=int, default=5)
    parser.add_argument("--include-kind", action="append", choices=sorted(KINDS), default=["theorem", "definition", "hypothesis"])
    parser.add_argument("--max-nodes", type=int)
    args = parser.parse_args()

    nodes = build_nodes(
        input_dir=args.input_dir,
        records=args.records,
        top_k=args.top_k,
        include_kinds=set(args.include_kind),
        max_nodes=args.max_nodes,
    )
    count = write_jsonl(args.out, nodes)
    summary = {
        "schema": SUMMARY_SCHEMA,
        "input_dir": str(args.input_dir),
        "records": str(args.records),
        "out": str(args.out),
        "nodes": count,
    }
    if args.summary_out:
        args.summary_out.parent.mkdir(parents=True, exist_ok=True)
        args.summary_out.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
