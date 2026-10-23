#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
for _p in (REPO_ROOT, REPO_ROOT / "src"):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

from tools.alexandria.schema import content_hash, infer_source_kind  # noqa: E402
from tools.alexandria.structural_chunking import (  # noqa: E402
    chunk_section_lines,
    chunk_source_text,
    classify_markdown_chunk as classify_chunk,
    split_sections,
    tokenize,
)

DEFAULT_SUFFIXES = (".md", ".txt")
SUPPORTED_SUFFIXES = (".md", ".markdown", ".txt", ".rst", ".lean", ".tex", ".py", ".jsonl")
SKIP_DIR_NAMES = {".git", ".lake", "build", "node_modules", "__pycache__", ".venv", "venv", "dist"}

HEADER_RE = re.compile(r"^(#{1,6})\s+(.*\S)\s*$")
IDENTIFIER_RE = re.compile(r"`([^`]+)`|\b([A-Z][A-Za-z0-9_.]+(?:\.[A-Z][A-Za-z0-9_.]+)*)\b|\b([a-z][A-Za-z0-9_]+(?:_[A-Za-z0-9_]+)+)\b")
MODULE_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)+)\b")
THEOREM_NAME_RE = re.compile(r"\b(?:theorem|lemma|proposition|corollary)\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.IGNORECASE)
MATH_NOTATION_RE = re.compile(r"\b([A-Z](?:_[A-Za-z0-9]+)+|[A-Z]{2,5}|[a-z]+_[A-Za-z0-9_]+)\b")
RELATION_PATTERNS: list[tuple[str, re.Pattern[str], float]] = [
    ("uses", re.compile(r"\b(using|uses|via|through)\b", re.IGNORECASE), 0.55),
    ("implies", re.compile(r"\b(implies|therefore|thus|hence)\b", re.IGNORECASE), 0.7),
    ("assumes", re.compile(r"\b(assume|suppose|given|under)\b", re.IGNORECASE), 0.75),
    ("defines", re.compile(r"\b(defines|is defined as|denote by)\b", re.IGNORECASE), 0.65),
]
BASE_STOPLIST = {
    "The", "This", "That", "These", "Those", "It", "We", "As", "Conclusion", "Chapter", "Front", "Matter",
    "Scale", "Invariance", "Gauge", "Proof", "Theorem", "Lemma", "Proposition", "Corollary", "Definition", "Remark",
}
CORPUS_STOPLISTS: dict[str, set[str]] = {
    "black_books": {"Python", "SymPy", "Front", "Matter", "Chapter"},
}
SYMBOL_PREFIX_BLOCKLIST = ("Figure", "Section", "Chapter")
TOOLING_TOKENS = {"Python", "SymPy", "NumPy", "Lean", "ArangoDB", "NetworkX", "cuGraph"}
ANCHOR_TYPES = {"theorem", "theorem_name", "module"}
ENTITY_CONFIDENCE: dict[str, float] = {
    "theorem": 1.0,
    "theorem_name": 0.98,
    "proof": 0.92,
    "hypothesis": 0.9,
    "definition": 0.88,
    "module": 0.94,
    "identifier": 0.78,
    "math_notation": 0.82,
    "tooling": 0.5,
    "symbol": 0.62,
    "remark": 0.45,
}


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
    confidence: float
    domain: str


@dataclass
class Relation:
    key: str
    fromEntityKey: str
    toEntityKey: str
    relationType: str
    chunkKey: str
    evidence: str
    weight: float


def stable_key(prefix: str, *parts: object) -> str:
    h = hashlib.sha1()
    for part in parts:
        h.update(str(part).encode("utf-8"))
        h.update(b"\0")
    return f"{prefix}_{h.hexdigest()[:16]}"


def normalize_surface(text: str) -> str:
    return re.sub(r"\s+", " ", text.strip().strip("`"))


def detect_domain(path: Path) -> str:
    lower = path.as_posix().lower()
    if "docs/black_books/" in lower:
        return "black_books"
    return "default"


# tokenize / classify_chunk / split_sections / chunk_section_lines were
# line-for-line copies of tools.alexandria.structural_chunking; they are now
# imported from that owner module (see the imports above).


def corpus_stoplist(domain: str) -> set[str]:
    return BASE_STOPLIST | CORPUS_STOPLISTS.get(domain, set())


def classify_surface(normalized: str, *, domain: str) -> tuple[str | None, float]:
    stoplist = corpus_stoplist(domain)
    if not normalized or normalized in stoplist:
        return None, 0.0
    if any(normalized.startswith(prefix) for prefix in SYMBOL_PREFIX_BLOCKLIST):
        return None, 0.0
    if normalized in TOOLING_TOKENS:
        return "tooling", ENTITY_CONFIDENCE["tooling"]
    if "." in normalized and normalized[0].isupper():
        return "module", ENTITY_CONFIDENCE["module"]
    if re.fullmatch(r"[A-Z](?:_[A-Za-z0-9]+)+", normalized) or normalized in {"BPS", "QFT", "SO", "SE", "E_C", "P_D", "D_4"}:
        return "math_notation", ENTITY_CONFIDENCE["math_notation"]
    if ("_" in normalized or "." in normalized) and len(normalized) >= 6:
        return "identifier", ENTITY_CONFIDENCE["identifier"]
    if normalized.isupper() and len(normalized) > 6:
        return None, 0.0
    if normalized[0].isupper() and normalized[1:].islower() and len(normalized) <= 4:
        return None, 0.0
    if re.fullmatch(r"[A-Z][a-z]+", normalized) and normalized not in {"Weyl", "Drazin", "Penrose", "Moore", "Souriau", "DeWitt"}:
        return None, 0.0
    return "symbol", ENTITY_CONFIDENCE["symbol"]


def add_entity(
    entities: list[Entity],
    seen: set[tuple[str, str]],
    chunk_key: str,
    entity_type: str,
    surface: str,
    *,
    confidence: float | None = None,
    domain: str,
) -> None:
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
            confidence=float(confidence if confidence is not None else ENTITY_CONFIDENCE.get(entity_type, 0.5)),
            domain=domain,
        )
    )


def extract_entities(chunk: Chunk, *, domain: str) -> list[Entity]:
    entities: list[Entity] = []
    seen: set[tuple[str, str]] = set()
    text = f"{chunk.title}\n{chunk.text}"

    if chunk.chunkKind in {"theorem", "proof", "hypothesis", "definition", "remark"}:
        add_entity(entities, seen, chunk.key, chunk.chunkKind, chunk.chunkKind, domain=domain)

    for match in THEOREM_NAME_RE.finditer(text):
        theorem_name = normalize_surface(match.group(1))
        if theorem_name in corpus_stoplist(domain):
            continue
        add_entity(entities, seen, chunk.key, "theorem_name", theorem_name, domain=domain)

    theorem_like = re.findall(r"\b(Theorem|Lemma|Proposition|Corollary)\b", text, flags=re.IGNORECASE)
    for surface in theorem_like:
        add_entity(entities, seen, chunk.key, "theorem", surface, domain=domain)

    proof_like = re.findall(r"\b(Proof)\b", text, flags=re.IGNORECASE)
    for surface in proof_like:
        add_entity(entities, seen, chunk.key, "proof", surface, domain=domain)

    hypothesis_like = re.findall(r"\b(Assume|Suppose|Given|Hypothesis|Assumption)\b", text, flags=re.IGNORECASE)
    for surface in hypothesis_like:
        add_entity(entities, seen, chunk.key, "hypothesis", surface, domain=domain)

    definition_like = re.findall(r"\b(Definition)\b", text, flags=re.IGNORECASE)
    for surface in definition_like:
        add_entity(entities, seen, chunk.key, "definition", surface, domain=domain)

    for match in MODULE_RE.finditer(text):
        normalized = normalize_surface(match.group(1))
        if normalized.count(".") >= 1:
            add_entity(entities, seen, chunk.key, "module", normalized, domain=domain)

    for match in MATH_NOTATION_RE.finditer(text):
        normalized = normalize_surface(match.group(1))
        entity_type, confidence = classify_surface(normalized, domain=domain)
        if entity_type == "math_notation":
            add_entity(entities, seen, chunk.key, entity_type, normalized, confidence=confidence, domain=domain)

    for match in IDENTIFIER_RE.finditer(text):
        surface = next(group for group in match.groups() if group)
        normalized = normalize_surface(surface)
        entity_type, confidence = classify_surface(normalized, domain=domain)
        if entity_type is not None:
            add_entity(entities, seen, chunk.key, entity_type, normalized, confidence=confidence, domain=domain)

    return entities


def relation_weight(src: Entity, dst: Entity, base_weight: float) -> float:
    structural_bonus = 1.15 if src.entityType in ANCHOR_TYPES or dst.entityType in ANCHOR_TYPES else 1.0
    notation_penalty = 0.9 if src.entityType == "tooling" or dst.entityType == "tooling" else 1.0
    return round(base_weight * structural_bonus * notation_penalty * src.confidence * dst.confidence, 6)


def extract_relations(chunk: Chunk, entities: list[Entity]) -> list[Relation]:
    relations: list[Relation] = []
    seen: set[tuple[str, str, str]] = set()
    by_type: dict[str, list[Entity]] = {}
    for entity in entities:
        by_type.setdefault(entity.entityType, []).append(entity)

    theorem_entities = by_type.get("theorem", []) + by_type.get("theorem_name", [])
    proof_entities = by_type.get("proof", [])
    hypothesis_entities = by_type.get("hypothesis", [])
    symbol_entities = by_type.get("symbol", []) + by_type.get("identifier", []) + by_type.get("math_notation", [])
    module_entities = by_type.get("module", [])

    for theorem in theorem_entities:
        for proof in proof_entities:
            signature = (theorem.key, proof.key, "supported_by")
            if signature not in seen:
                seen.add(signature)
                relations.append(Relation(stable_key("rel", *signature), theorem.key, proof.key, "supported_by", chunk.key, "theorem/proof co-occurrence", relation_weight(theorem, proof, 0.92)))
        for hyp in hypothesis_entities:
            signature = (theorem.key, hyp.key, "assumes")
            if signature not in seen:
                seen.add(signature)
                relations.append(Relation(stable_key("rel", *signature), theorem.key, hyp.key, "assumes", chunk.key, "theorem/hypothesis co-occurrence", relation_weight(theorem, hyp, 0.88)))
        for symbol in symbol_entities[:6]:
            signature = (theorem.key, symbol.key, "mentions")
            if signature not in seen:
                seen.add(signature)
                relations.append(Relation(stable_key("rel", *signature), theorem.key, symbol.key, "mentions", chunk.key, "theorem/symbol co-occurrence", relation_weight(theorem, symbol, 0.56)))
        for module in module_entities[:5]:
            signature = (theorem.key, module.key, "references_module")
            if signature not in seen:
                seen.add(signature)
                relations.append(Relation(stable_key("rel", *signature), theorem.key, module.key, "references_module", chunk.key, "theorem/module co-occurrence", relation_weight(theorem, module, 0.84)))

    preferred_sources = theorem_entities or proof_entities or hypothesis_entities or symbol_entities
    preferred_targets = symbol_entities + module_entities
    for relation_type, pattern, base_weight in RELATION_PATTERNS:
        if not pattern.search(chunk.text):
            continue
        for src in preferred_sources[:3]:
            for dst in preferred_targets[:4]:
                if src.key == dst.key:
                    continue
                signature = (src.key, dst.key, relation_type)
                if signature in seen:
                    continue
                seen.add(signature)
                relations.append(Relation(stable_key("rel", *signature), src.key, dst.key, relation_type, chunk.key, pattern.pattern, relation_weight(src, dst, base_weight)))

    return relations


def digest_document(path: Path) -> tuple[dict, list[Section], list[Chunk], list[Entity], list[dict], list[Relation]]:
    """Chunk one file via ``structural_chunking.chunk_source_text``.

    Markdown/text keys and texts are identical to the historical in-module
    chunker; ``.lean``/``.tex``/``.py``/``.jsonl`` get structural chunks.
    Chunk provenance carries ``lineStart``/``lineEnd`` where available.
    """
    text = path.read_text(encoding="utf-8", errors="replace")
    document_key = stable_key("doc", path.as_posix())
    domain = detect_domain(path)
    document = {
        "_key": document_key,
        "path": path.as_posix(),
        "title": path.stem,
        "sourceType": path.suffix.lower().lstrip(".") or "text",
        "domain": domain,
        "contentHash": content_hash(text),
        "sourceKind": infer_source_kind(path),
    }
    result = chunk_source_text(path, text, document, path.resolve(), domain)
    sections = [
        Section(key=s.key, documentKey=s.documentKey, title=s.title, level=s.level, ordinal=s.ordinal)
        for s in result.sections
    ]
    chunks: list[Chunk] = []
    entities: list[Entity] = []
    relations: list[Relation] = []
    for sc in result.chunks:
        provenance = dict(sc.provenance)
        provenance["ordinal"] = sc.ordinal
        chunk = Chunk(
            key=sc.key,
            documentKey=sc.documentKey,
            sectionKey=sc.sectionKey,
            ordinal=sc.ordinal,
            chunkKind=sc.chunkKind,
            title=sc.title,
            text=sc.text,
            tokens=sc.tokens,
            provenance=provenance,
        )
        chunks.append(chunk)
        chunk_entities = extract_entities(chunk, domain=domain)
        entities.extend(chunk_entities)
        relations.extend(extract_relations(chunk, chunk_entities))
    return document, sections, chunks, entities, list(result.adjacent_edges), relations


def iter_input_files(raw_inputs: list[str], suffixes: set[str], max_bytes: int) -> list[Path]:
    """Expand inputs; directories are walked skipping VCS/build/cache dirs."""
    out: list[Path] = []
    for raw in raw_inputs:
        root = Path(raw)
        if not root.is_dir():
            out.append(root)
            continue
        for path in sorted(root.rglob("*")):
            rel_parts = path.relative_to(root).parts[:-1]
            if any(part in SKIP_DIR_NAMES or part.startswith(".") for part in rel_parts):
                continue
            if path.is_file() and path.suffix.lower() in suffixes and path.stat().st_size <= max_bytes:
                out.append(path)
    return out


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def main() -> int:
    ap = argparse.ArgumentParser(description="Digest markdown/text into Alexandria semantic chunks")
    ap.add_argument("--input", action="append", required=True, help="input file or directory")
    ap.add_argument("--output", required=True, help="output directory for JSONL artifacts")
    ap.add_argument(
        "--suffix",
        action="append",
        choices=SUPPORTED_SUFFIXES,
        help=f"file suffix to include when walking directories (repeatable; default: {' '.join(DEFAULT_SUFFIXES)})",
    )
    ap.add_argument("--max-file-mb", type=float, default=16.0, help="skip larger files when walking directories")
    args = ap.parse_args()

    suffixes = set(args.suffix or DEFAULT_SUFFIXES)
    inputs = iter_input_files(args.input, suffixes, int(args.max_file_mb * 1024 * 1024))

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
                    "confidence": entity.confidence,
                }
            )
        for edge in adjacent_edges:
            chunk_adjacent_edges.append(
                {
                    "_key": edge["_key"],
                    "_from": f"alexandria_chunks/{edge['fromChunkKey']}",
                    "_to": f"alexandria_chunks/{edge['toChunkKey']}",
                    "kind": edge["kind"],
                    "weight": edge.get("weight", 1.0),
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
                    "weight": relation.weight,
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
