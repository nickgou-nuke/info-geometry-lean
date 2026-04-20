#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

HEADER_RE = re.compile(r"^(#{1,6})\s+(.*\S)\s*$")
ENTITY_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("theorem", re.compile(r"\b(theorem|lemma|proposition|corollary)\b", re.IGNORECASE)),
    ("proof", re.compile(r"\bproof\b", re.IGNORECASE)),
    ("hypothesis", re.compile(r"\b(if|assume|suppose|given|hypothesis|assumption)\b", re.IGNORECASE)),
    ("definition", re.compile(r"\bdefinition\b", re.IGNORECASE)),
]


@dataclass
class Section:
    key: str
    documentKey: str
    title: str
    level: int
    ordinal: int


@dataclass
class Chunk:
    key: str
    documentKey: str
    sectionKey: str
    ordinal: int
    chunkKind: str
    title: str
    text: str
    tokens: list[str]
    provenance: dict[str, object]


@dataclass
class Entity:
    key: str
    chunkKey: str
    entityType: str
    surface: str


def stable_key(prefix: str, *parts: object) -> str:
    h = hashlib.sha1()
    for part in parts:
        h.update(str(part).encode("utf-8"))
        h.update(b"\0")
    return f"{prefix}_{h.hexdigest()[:16]}"


def tokenize(text: str) -> list[str]:
    return sorted({tok.lower() for tok in re.findall(r"[A-Za-z][A-Za-z0-9_]{2,}", text)})


def classify_chunk(title: str, text: str) -> str:
    blob = f"{title}\n{text}".lower()
    if any(word in blob for word in ["theorem", "lemma", "proposition", "corollary"]):
        return "theorem"
    if "proof" in blob:
        return "proof"
    if any(word in blob for word in ["hypothesis", "assume", "suppose", "given"]):
        return "hypothesis"
    if "definition" in blob:
        return "definition"
    if "remark" in blob:
        return "remark"
    return "chunk"


def split_sections(text: str) -> list[tuple[int, str, list[str]]]:
    sections: list[tuple[int, str, list[str]]] = []
    current_title = "Front Matter"
    current_level = 1
    current_lines: list[str] = []
    for line in text.splitlines():
        match = HEADER_RE.match(line)
        if match:
            if current_lines or not sections:
                sections.append((current_level, current_title, current_lines))
            current_level = len(match.group(1))
            current_title = match.group(2).strip()
            current_lines = []
        else:
            current_lines.append(line)
    sections.append((current_level, current_title, current_lines))
    return [section for section in sections if section[2] or section[1]]


def chunk_section_lines(lines: Iterable[str]) -> list[str]:
    blocks: list[str] = []
    current: list[str] = []
    for line in lines:
        if not line.strip():
            if current:
                blocks.append("\n".join(current).strip())
                current = []
            continue
        current.append(line)
    if current:
        blocks.append("\n".join(current).strip())
    return [block for block in blocks if block]


def extract_entities(chunk: Chunk) -> list[Entity]:
    entities: list[Entity] = []
    seen: set[tuple[str, str]] = set()
    text = f"{chunk.title}\n{chunk.text}"
    for entity_type, pattern in ENTITY_PATTERNS:
        for match in pattern.finditer(text):
            surface = match.group(0)
            signature = (entity_type, surface.lower())
            if signature in seen:
                continue
            seen.add(signature)
            entities.append(
                Entity(
                    key=stable_key("entity", chunk.key, entity_type, surface.lower()),
                    chunkKey=chunk.key,
                    entityType=entity_type,
                    surface=surface,
                )
            )
    return entities


def digest_document(path: Path) -> tuple[dict, list[Section], list[Chunk], list[Entity], list[dict]]:
    text = path.read_text(encoding="utf-8")
    document_key = stable_key("doc", path.as_posix())
    document = {
        "_key": document_key,
        "path": path.as_posix(),
        "title": path.stem,
        "sourceType": path.suffix.lower().lstrip(".") or "text",
    }
    sections: list[Section] = []
    chunks: list[Chunk] = []
    entities: list[Entity] = []
    adjacent_edges: list[dict] = []
    chunk_ordinal = 0
    prev_chunk_key: str | None = None
    for section_ordinal, (level, title, lines) in enumerate(split_sections(text), start=1):
        section = Section(
            key=stable_key("section", document_key, section_ordinal, title),
            documentKey=document_key,
            title=title,
            level=level,
            ordinal=section_ordinal,
        )
        sections.append(section)
        for block_index, block in enumerate(chunk_section_lines(lines), start=1):
            chunk_ordinal += 1
            chunk = Chunk(
                key=stable_key("chunk", section.key, block_index, block[:80]),
                documentKey=document_key,
                sectionKey=section.key,
                ordinal=chunk_ordinal,
                chunkKind=classify_chunk(title, block),
                title=title,
                text=block,
                tokens=tokenize(block),
                provenance={"path": path.as_posix(), "section": title, "ordinal": chunk_ordinal},
            )
            chunks.append(chunk)
            entities.extend(extract_entities(chunk))
            if prev_chunk_key is not None:
                adjacent_edges.append(
                    {
                        "_key": stable_key("adj", prev_chunk_key, chunk.key),
                        "fromChunkKey": prev_chunk_key,
                        "toChunkKey": chunk.key,
                        "kind": "adjacent",
                    }
                )
            prev_chunk_key = chunk.key
    return document, sections, chunks, entities, adjacent_edges


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser(description="Digest markdown/text into Alexandria semantic chunks")
    ap.add_argument("--input", action="append", required=True, help="input file or directory")
    ap.add_argument("--output", required=True, help="output directory for JSONL artifacts")
    args = ap.parse_args()

    inputs: list[Path] = []
    for raw in args.input:
        path = Path(raw)
        if path.is_dir():
            inputs.extend(sorted(p for p in path.rglob("*") if p.is_file() and p.suffix.lower() in {".md", ".txt"}))
        else:
            inputs.append(path)

    documents: list[dict] = []
    sections: list[dict] = []
    chunks: list[dict] = []
    entities: list[dict] = []
    document_section_edges: list[dict] = []
    section_chunk_edges: list[dict] = []
    chunk_entity_edges: list[dict] = []
    chunk_adjacent_edges: list[dict] = []

    for path in inputs:
        document, doc_sections, doc_chunks, doc_entities, adjacent_edges = digest_document(path)
        documents.append(document)
        for section in doc_sections:
            sections.append({"_key": section.key, **asdict(section)})
            document_section_edges.append(
                {
                    "_key": stable_key("docsec", document["_key"], section.key),
                    "_from": f"alexandria_documents/{document['_key']}",
                    "_to": f"alexandria_sections/{section.key}",
                    "ordinal": section.ordinal,
                }
            )
        for chunk in doc_chunks:
            chunks.append({"_key": chunk.key, **asdict(chunk)})
            section_chunk_edges.append(
                {
                    "_key": stable_key("secchunk", chunk.sectionKey, chunk.key),
                    "_from": f"alexandria_sections/{chunk.sectionKey}",
                    "_to": f"alexandria_chunks/{chunk.key}",
                    "ordinal": chunk.ordinal,
                    "chunkKind": chunk.chunkKind,
                }
            )
        for entity in doc_entities:
            entities.append({"_key": entity.key, **asdict(entity)})
            chunk_entity_edges.append(
                {
                    "_key": stable_key("chunkent", entity.chunkKey, entity.key),
                    "_from": f"alexandria_chunks/{entity.chunkKey}",
                    "_to": f"alexandria_entities/{entity.key}",
                    "entityType": entity.entityType,
                }
            )
        for edge in adjacent_edges:
            chunk_adjacent_edges.append(
                {
                    "_key": edge["_key"],
                    "_from": f"alexandria_chunks/{edge['fromChunkKey']}",
                    "_to": f"alexandria_chunks/{edge['toChunkKey']}",
                    "kind": edge["kind"],
                }
            )

    out = Path(args.output)
    write_jsonl(out / "alexandria_documents.jsonl", documents)
    write_jsonl(out / "alexandria_sections.jsonl", sections)
    write_jsonl(out / "alexandria_chunks.jsonl", chunks)
    write_jsonl(out / "alexandria_entities.jsonl", entities)
    write_jsonl(out / "alexandria_document_section_edges.jsonl", document_section_edges)
    write_jsonl(out / "alexandria_section_chunk_edges.jsonl", section_chunk_edges)
    write_jsonl(out / "alexandria_chunk_entity_edges.jsonl", chunk_entity_edges)
    write_jsonl(out / "alexandria_chunk_adjacent_edges.jsonl", chunk_adjacent_edges)
    write_jsonl(out / "alexandria_entity_relation_edges.jsonl", [])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
