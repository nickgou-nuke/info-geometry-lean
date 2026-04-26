from __future__ import annotations

import hashlib
from pathlib import Path

SCHEMA_VERSION = "info_geometry.alexandria.semantic_ingest.v2"

DOCUMENT_COLLECTIONS = [
    "alexandria_documents",
    "alexandria_sections",
    "alexandria_chunks",
    "alexandria_entities",
    "alexandria_embeddings",
    "alexandria_communities",
    "alexandria_repair_attempts",
    "alexandria_repair_gate_results",
]

EDGE_COLLECTIONS = [
    "alexandria_document_section_edges",
    "alexandria_section_chunk_edges",
    "alexandria_chunk_entity_edges",
    "alexandria_chunk_adjacent_edges",
    "alexandria_entity_relation_edges",
    "alexandria_chunk_embedding_edges",
    "alexandria_chunk_community_edges",
    "alexandria_repair_lineage_edges",
]


def stable_key(prefix: str, *parts: object) -> str:
    h = hashlib.sha1()
    for part in parts:
        h.update(str(part).encode("utf-8"))
        h.update(b"\0")
    return f"{prefix}_{h.hexdigest()[:16]}"


def content_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def infer_source_kind(path: Path) -> str:
    lower = path.as_posix().lower()
    suffix = path.suffix.lower()
    if "docs/black_books/" in lower or "black_book" in lower:
        return "book_note"
    if "arxiv" in lower or suffix == ".tex" or lower.endswith(".tex.md"):
        return "paper"
    if suffix in {".md", ".markdown"}:
        return "note"
    if suffix in {".py", ".lean", ".js", ".ts", ".rs", ".go", ".cpp", ".c", ".h", ".java", ".scala", ".lua"}:
        return "code"
    if suffix in {".txt", ".rst"}:
        return "note"
    return "file"


def source_uri(path: Path) -> str:
    return path.resolve().as_uri()
