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
IDENTIFIER_RE = re.compile(r"`([^`]+)`|\b([A-Z][A-Za-z0-9_.]+(?:\.[A-Z][A-Za-z0-9_.]+)*)\b|\b([a-z][A-Za-z0-9_]+(?:_[A-Za-z0-9_]+)+)\b")
MODULE_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)+)\b")
RELATION_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("uses", re.compile(r"\b(using|uses|via|through)\b", re.IGNORECASE)),
    ("implies", re.compile(r"\b(implies|therefore|thus|hence)\b", re.IGNORECASE)),
    ("assumes", re.compile(r"\b(assume|suppose|given|under)\b", re.IGNORECASE)),
    ("defines", re.compile(r"\b(defines|is defined as|denote by)\b", re.IGNORECASE)),
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
    normalized: str


@dataclass
class Relation:
    key: str
    fromEntityKey: str
    toEntityKey: str
    relationType: str
    chunkKey: str
    evidence: str


def stable_key(prefix: str, *parts: object) -> str:
    h = hashlib.sha1()
    for part in parts:
        h.update(str(part).encode("utf-8"))
        h.update(b"\0")
    return f"{prefix}_{h.hexdigest()[:16]}"


def normalize_surface(text: str) -> str:
    return re.sub(r"\s+", " ", text.strip().strip("`"))


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


def add_entity(entities: list[Entity], seen: set[tuple[str, str]], chunk_key: str, entity_type: str, surface: str) -> None:
    normalized = normalize_surface(surface)
    if not normalized:
        return
    signature = (entity_type, normalized.lower())
    if signature in seen:
        return
    seen.add(signature)
    entities.append(
        Entity(
            key=stable_key("entity", chunk_key, entity_type, normalized.lower()),
            chunkKey=chunk_key,
            entityType=entity_type,
            surface=surface,
            normalized=normalized,
        )
    )


def extract_entities(chunk: Chunk) -> list[Entity]:
    entities: list[Entity] = []
    seen: set[tuple[str, str]] = set()
    text = f"{chunk.title}\n{chunk.text}"

    if chunk.chunkKind in {"theorem", "proof", "hypothesis", "definition", "remark"}:
        add_entity(entities, seen, chunk.key, chunk.chunkKind, chunk.chunkKind)

    theorem_like = re.findall(r"\b(Theorem|Lemma|Proposition|Corollary)\b", text, flags=re.IGNORECASE)
    for surface in theorem_like:
        add_entity(entities, seen, chunk.key, "theorem", surface)

    proof_like = re.findall(r"\b(Proof)\b", text, flags=re.IGNORECASE)
    for surface in proof_like:
        add_entity(entities, seen, chunk.key, "proof", surface)

    hypothesis_like = re.findall(r"\b(Assume|Suppose|Given|Hypothesis|Assumption)\b", text, flags=re.IGNORECASE)
    for surface in hypothesis_like:
        add_entity(entities, seen, chunk.key, "hypothesis", surface)

    definition_like = re.findall(r"\b(Definition)\b", text, flags=re.IGNORECASE)
    for surface in definition_like:
        add_entity(entities, seen, chunk.key, "definition", surface)

    for match in IDENTIFIER_RE.finditer(text):
        surface = next(group for group in match.groups() if group)
        normalized = normalize_surface(surface)
        if "." in normalized and normalized[0].isupper():
            add_entity(entities, seen, chunk.key, "module", normalized)
        elif normalized and normalized[0].isupper():
            add_entity(entities, seen, chunk.key, "symbol", normalized)
        else:
            add_entity(entities, seen, chunk.key, "identifier", normalized)

    for match in MODULE_RE.finditer(text):
        add_entity(entities, seen, chunk.key, "module", match.group(1))

    return entities


def extract_relations(chunk: Chunk, entities: list[Entity]) -> list[Relation]:
    relations: list[Relation] = []
    seen: set[tuple[str, str, str]] = set()
    by_type: dict[str, list[Entity]] = {}
    for entity in entities:
        by_type.setdefault(entity.entityType, []).append(entity)

    theorem_entities = by_type.get("theorem", [])
    proof_entities = by_type.get("proof", [])
    hypothesis_entities = by_type.get("hypothesis", [])
    symbol_entities = by_type.get("symbol", []) + by_type.get("identifier", [])
    module_entities = by_type.get("module", [])

    for theorem in theorem_entities:
        for proof in proof_entities:
            signature = (theorem.key, proof.key, "supported_by")
            if signature not in seen:
                seen.add(signature)
                relations.append(Relation(stable_key("rel", *signature), theorem.key, proof.key, "supported_by", chunk.key, "theorem/proof co-occurrence"))
        for hyp in hypothesis_entities:
            signature = (theorem.key, hyp.key, "assumes")
            if signature not in seen:
                seen.add(signature)
                relations.append(Relation(stable_key("rel", *signature), theorem.key, hyp.key, "assumes", chunk.key, "theorem/hypothesis co-occurrence"))
        for symbol in symbol_entities:
            signature = (theorem.key, symbol.key, "mentions")
            if signature not in seen:
                seen.add(signature)
                relations.append(Relation(stable_key("rel", *signature), theorem.key, symbol.key, "mentions", chunk.key, "theorem/symbol co-occurrence"))
        for module in module_entities:
            signature = (theorem.key, module.key, "references_module")
            if signature not in seen:
                seen.add(signature)
                relations.append(Relation(stable_key("rel", *signature), theorem.key, module.key, "references_module", chunk.key, "theorem/module co-occurrence"))

    for relation_type, pattern in RELATION_PATTERNS:
        if not pattern.search(chunk.text):
            continue
        all_entities = theorem_entities or proof_entities or hypothesis_entities or symbol_entities
        targets = symbol_entities + module_entities
        for src in all_entities[:4]:
            for dst in targets[:6]:
                if src.key == dst.key:
                    continue
                signature = (src.key, dst.key, relation_type)
                if signature in seen:
                    continue
                seen.add(signature)
                relations.append(Relation(stable_key("rel", *signature), src.key, dst.key, relation_type, chunk.key, pattern.pattern))

    return relations


def digest_document(path: Path) -> tuple[dict, list[Section], list[Chunk], list[Entity], list[dict], list[Relation]]:
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
    relations: list[Relation] = []
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
            chunk_entities = extract_entities(chunk)
            entities.extend(chunk_entities)
            relations.extend(extract_relations(chunk, chunk_entities))
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
    return document, sections, chunks, entities, adjacent_edges, relations


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
    entity_relation_edges: list[dict] = []

    for path in inputs:
        document, doc_sections, doc_chunks, doc_entities, adjacent_edges, relations = digest_document(path)
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
        for relation in relations:
            entity_relation_edges.append(
                {
                    "_key": relation.key,
                    "_from": f"alexandria_entities/{relation.fromEntityKey}",
                    "_to": f"alexandria_entities/{relation.toEntityKey}",
                    "relationType": relation.relationType,
                    "chunkKey": relation.chunkKey,
                    "evidence": relation.evidence,
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
    write_jsonl(out / "alexandria_entity_relation_edges.jsonl", entity_relation_edges)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
