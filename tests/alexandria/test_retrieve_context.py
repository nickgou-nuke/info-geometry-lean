from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
TOOL = REPO / "tools" / "alexandria" / "retrieve_context.py"


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.write_text("".join(json.dumps(record) + "\n" for record in records), encoding="utf-8")


def test_retrieve_context_includes_source_and_score_breakdown(tmp_path: Path) -> None:
    write_jsonl(
        tmp_path / "alexandria_documents.jsonl",
        [
            {
                "_key": "doc_1",
                "title": "paper",
                "path": "paper.tex.md",
                "sourceKind": "paper",
                "sourceFormat": "latex",
            }
        ],
    )
    write_jsonl(
        tmp_path / "alexandria_sections.jsonl",
        [{"_key": "sec_1", "documentKey": "doc_1", "title": "Main Results", "level": 1, "ordinal": 1}],
    )
    write_jsonl(
        tmp_path / "alexandria_chunks.jsonl",
        [
            {
                "_key": "chunk_1",
                "documentKey": "doc_1",
                "sectionKey": "sec_1",
                "ordinal": 1,
                "chunkKind": "theorem",
                "title": "Main Results",
                "text": "Theorem. A local Weyl symmetry statement.",
                "tokens": ["theorem", "local", "weyl", "symmetry", "statement"],
                "provenance": {"path": "paper.tex.md", "sourceUri": "file:///paper.tex.md", "sourceKind": "paper", "sourceFormat": "latex"},
            },
            {
                "_key": "chunk_2",
                "documentKey": "doc_1",
                "sectionKey": "sec_1",
                "ordinal": 2,
                "chunkKind": "proof",
                "title": "Main Results",
                "text": "Proof. Assume the candidate commutes.",
                "tokens": ["proof", "assume", "candidate", "commutes"],
                "provenance": {"path": "paper.tex.md", "sourceUri": "file:///paper.tex.md", "sourceKind": "paper", "sourceFormat": "latex"},
            },
        ],
    )
    write_jsonl(
        tmp_path / "alexandria_entities.jsonl",
        [
            {"_key": "ent_1", "chunkKey": "chunk_1", "entityType": "theorem", "surface": "Theorem", "normalized": "Theorem", "confidence": 1.0, "domain": "default"},
            {"_key": "ent_2", "chunkKey": "chunk_2", "entityType": "proof", "surface": "Proof", "normalized": "Proof", "confidence": 1.0, "domain": "default"},
        ],
    )
    write_jsonl(
        tmp_path / "alexandria_chunk_entity_edges.jsonl",
        [
            {"_key": "edge_1", "_from": "alexandria_chunks/chunk_1", "_to": "alexandria_entities/ent_1", "entityType": "theorem", "confidence": 1.0},
            {"_key": "edge_2", "_from": "alexandria_chunks/chunk_2", "_to": "alexandria_entities/ent_2", "entityType": "proof", "confidence": 1.0},
        ],
    )
    write_jsonl(
        tmp_path / "alexandria_chunk_adjacent_edges.jsonl",
        [{"_key": "adj_1", "_from": "alexandria_chunks/chunk_1", "_to": "alexandria_chunks/chunk_2", "kind": "adjacent", "weight": 1.0}],
    )

    result = subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--query",
            "main results local weyl theorem",
            "--input-dir",
            str(tmp_path),
            "--top-k",
            "1",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    packet = json.loads(result.stdout)

    hit = packet["hits"][0]
    assert hit["source"]["sourceKind"] == "paper"
    assert hit["source"]["sourceUri"] == "file:///paper.tex.md"
    assert hit["scoreBreakdown"]["lexical"] >= 2
    assert hit["scoreBreakdown"]["title"] >= 1
    assert hit["entities"]
