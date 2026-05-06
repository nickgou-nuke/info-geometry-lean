#!/usr/bin/env python3
"""Digest text libraries into retrieval-only KG triples and Hive tasks.

This is the repo-native adaptation of the NVIDIA txt2kg pattern:

    documents -> chunks -> triples -> predigestion claims -> Hive tasks

The output is explicitly non-authoritative.  It can feed Alexandria/Arango
navigation and Hive scheduling, but it cannot promote a mathematical claim
without the normal Lean/build/audit gates.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable
from urllib.request import Request, urlopen

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.alexandria.schema import content_hash, infer_source_kind, source_uri
from tools.alexandria.arango_ingest import (
    ensure_collection,
    ensure_database,
    ensure_index,
    import_rows,
)
from tools.alexandria.structural_chunking import tokenize
from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.build_predigestion_packets import (
    build_packets,
    summary_for as claim_summary_for,
    write_jsonl as write_claim_jsonl,
)
from tools.infra.hive_predigestion_ingest import (
    build_tasks,
    summary_for as task_summary_for,
    write_jsonl as write_task_jsonl,
)

SOURCE_SCHEMA = "info_geometry.alexandria.txt2kg.source.v1"
CHUNK_SCHEMA = "info_geometry.alexandria.txt2kg.chunk.v1"
TRIPLE_SCHEMA = "info_geometry.alexandria.txt2kg.triple.v1"
LIGHT_CONE_SEED_SCHEMA = "info_geometry.context_light_cone.seed.v1"
SUMMARY_SCHEMA = "info_geometry.alexandria.txt2kg_hive_ingest.summary.v1"

AUTHORITY_BOUNDARY = {
    "graph_is_retrieval_only": True,
    "triples_are_not_proofs": True,
    "hive_tasks_are_not_authority": True,
    "lean_remains_proof_authority": True,
    "audits_remain_admission_authority": True,
}

TXT2KG_DOCUMENT_COLLECTIONS = [
    "txt2kg_sources",
    "txt2kg_chunks",
    "txt2kg_triples",
    "txt2kg_entities",
]

TXT2KG_EDGE_COLLECTIONS = [
    "txt2kg_relationships",
]

TXT2KG_INDEXES: dict[str, list[list[str]]] = {
    "txt2kg_sources": [["path"], ["source_kind"], ["title"]],
    "txt2kg_chunks": [["source_id"], ["tokens[*]"]],
    "txt2kg_triples": [["subject"], ["predicate"], ["object"], ["authority"], ["layer"]],
    "txt2kg_entities": [["name"], ["authority"], ["layer"]],
    "txt2kg_relationships": [["type"], ["authority"], ["layer"]],
}

SUPPORTED_SUFFIXES = {
    ".md",
    ".markdown",
    ".txt",
    ".rst",
    ".tex",
    ".lean",
    ".py",
    ".json",
    ".jsonl",
    ".pdf",
}

ENTITY_RE = re.compile(
    r"`([^`]{2,120})`"
    r"|\b([A-Z][A-Za-z0-9_.]*(?:\.[A-Z][A-Za-z0-9_.]+)+)\b"
    r"|\b([A-Z][A-Za-z][A-Za-z0-9_-]{2,})\b"
    r"|\b([a-z][A-Za-z0-9_]+(?:_[A-Za-z0-9_]+)+)\b"
)

RELATION_PATTERNS: list[tuple[str, re.Pattern[str], float]] = [
    ("defines", re.compile(r"\b(defines|defined as|is called|denote by)\b", re.IGNORECASE), 0.74),
    ("implies", re.compile(r"\b(implies|therefore|hence|thus|yields|gives)\b", re.IGNORECASE), 0.70),
    ("uses", re.compile(r"\b(uses|using|via|through|by means of)\b", re.IGNORECASE), 0.62),
    ("supports", re.compile(r"\b(supports|proves|shows|establishes)\b", re.IGNORECASE), 0.66),
    ("guards", re.compile(r"\b(guard|prevents|forbids|quarantine|not automatic)\b", re.IGNORECASE), 0.60),
    ("belongs_to_lane", re.compile(r"\b(lane|owner|corridor|surface|module)\b", re.IGNORECASE), 0.58),
]

STOP_SURFACES = {
    "The",
    "This",
    "That",
    "These",
    "Those",
    "There",
    "For",
    "With",
    "From",
    "Proof",
    "Definition",
    "Theorem",
    "Lemma",
    "Proposition",
    "Corollary",
    "Remark",
    "Chapter",
    "Section",
}

SENTENCE_ENDINGS = ".!?"


@dataclass(frozen=True)
class SourceRecord:
    id: str
    path: str
    title: str
    source_kind: str
    source_format: str
    content_hash: str
    source_uri: str


@dataclass(frozen=True)
class ChunkRecord:
    id: str
    source_id: str
    ordinal: int
    title: str
    text: str
    tokens: list[str]
    provenance: dict[str, Any]


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


def stable_hash(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def short_key(prefix: str, value: str) -> str:
    return f"{prefix}_{hashlib.md5(value.encode('utf-8')).hexdigest()[:16]}"


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(canonical_json(row) + "\n")
            count += 1
    return count


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if line:
                payload = json.loads(line)
                if isinstance(payload, dict):
                    rows.append(payload)
    return rows


def iter_input_files(inputs: list[Path]) -> list[Path]:
    files: list[Path] = []
    for path in inputs:
        if path.is_dir():
            files.extend(
                sorted(
                    p
                    for p in path.rglob("*")
                    if p.is_file() and p.suffix.lower() in SUPPORTED_SUFFIXES
                )
            )
        elif path.is_file():
            if path.suffix.lower() in SUPPORTED_SUFFIXES:
                files.append(path)
        else:
            raise SystemExit(f"input path does not exist: {path}")
    return files


def decode_text_file(path: Path) -> str:
    raw = path.read_bytes()
    for encoding in ("utf-8", "utf-8-sig", "latin-1"):
        try:
            return raw.decode(encoding)
        except UnicodeDecodeError:
            continue
    return raw.decode("utf-8", errors="replace")


def extract_pdf_text(path: Path) -> tuple[str, str]:
    """Extract PDF text through local tools only.

    `pdftotext` is preferred when installed.  If unavailable, try `pypdf`.
    Failure does not abort the library scan; it emits a small placeholder with
    provenance so the missing extractor is visible to Hive.
    """
    try:
        with tempfile.TemporaryDirectory(prefix="txt2kg_pdf_") as tmp:
            out = Path(tmp) / "out.txt"
            subprocess.run(
                ["pdftotext", "-layout", str(path), str(out)],
                check=True,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            return out.read_text(encoding="utf-8", errors="replace"), "pdf_pdftotext"
    except Exception:
        pass
    try:
        from pypdf import PdfReader  # type: ignore

        reader = PdfReader(str(path))
        pages = [page.extract_text() or "" for page in reader.pages]
        return "\n\n".join(pages), "pdf_pypdf"
    except Exception as exc:  # noqa: BLE001
        return f"[PDF text extraction unavailable for {path}: {exc}]", "pdf_unextracted"


def extract_text(path: Path) -> tuple[str, str]:
    suffix = path.suffix.lower()
    if suffix == ".pdf":
        return extract_pdf_text(path)
    return decode_text_file(path), suffix.lstrip(".") or "text"


def chunk_text_txt2kg(text: str, *, chunk_size: int, overlap_size: int) -> list[str]:
    """Sentence-aware chunking adapted from NVIDIA txt2kg/PyG utilities."""
    if not text:
        return []
    if chunk_size <= 0:
        raise ValueError("chunk_size must be positive")
    if overlap_size < 0:
        raise ValueError("overlap_size must be non-negative")

    chunks: list[str] = []
    start_index = 0
    while start_index < len(text):
        end_index = min(start_index + chunk_size, len(text))
        if end_index >= len(text):
            final_chunk = text[start_index:].strip()
            if final_chunk:
                chunks.append(final_chunk)
            break

        candidate = text[start_index:end_index]
        best_split = end_index
        best_sentence_split: int | None = None
        for ending in SENTENCE_ENDINGS:
            last_ending = candidate.rfind(ending)
            if last_ending != -1:
                absolute_pos = start_index + last_ending + 1
                has_space = absolute_pos < len(text) and text[absolute_pos].isspace()
                split = absolute_pos + (1 if has_space else 0)
                if best_sentence_split is None or split > best_sentence_split:
                    best_sentence_split = split
        if best_sentence_split is not None:
            best_split = best_sentence_split

        if best_split < len(text) and text[best_split].isalpha():
            space_split = text[start_index:best_split].rfind(" ")
            if space_split != -1:
                best_split = start_index + space_split

        current_chunk = text[start_index:best_split].strip()
        if current_chunk:
            chunks.append(current_chunk)

        if overlap_size == 0:
            start_index = best_split
            while start_index < len(text) and text[start_index].isspace():
                start_index += 1
        else:
            step = max(1, chunk_size - overlap_size)
            start_index += step
    return chunks


def source_kind_for(path: Path, override: str) -> str:
    if override != "auto":
        return override
    inferred = infer_source_kind(path)
    if inferred == "book_note":
        return "blackbook"
    if inferred == "paper":
        return "paper"
    if inferred in {"note", "file", "code"}:
        return "doc"
    return "doc"


def normalize_surface(surface: str) -> str:
    return re.sub(r"\s+", " ", surface.strip().strip("`")).strip(".,;:()[]{}")


def extract_surfaces(text: str, *, limit: int = 14) -> list[str]:
    surfaces: list[str] = []
    seen: set[str] = set()
    for match in ENTITY_RE.finditer(text):
        raw = next(group for group in match.groups() if group)
        surface = normalize_surface(raw)
        key = surface.lower()
        if not surface or surface in STOP_SURFACES or key in seen:
            continue
        if len(surface) < 3 or len(surface) > 120:
            continue
        seen.add(key)
        surfaces.append(surface)
        if len(surfaces) >= limit:
            break
    return surfaces


def surface_source(surface: str) -> str:
    if surface.startswith("InfoGeometry.") or "." in surface:
        return "module_path"
    if "_" in surface:
        return "snake_case"
    if surface.isupper() and len(surface) <= 8:
        return "acronym"
    if surface[:1].isupper():
        return "capitalized_phrase"
    return "plain"


def normalization_confidence(surface: str) -> float:
    kind = surface_source(surface)
    if kind == "module_path":
        return 0.95
    if kind == "snake_case":
        return 0.88
    if kind == "acronym":
        return 0.78
    if kind == "capitalized_phrase":
        return 0.56
    return 0.45


def relation_type_for(text: str) -> tuple[str, float]:
    for relation_type, pattern, confidence in RELATION_PATTERNS:
        if pattern.search(text):
            return relation_type, confidence
    return "associated_with", 0.42


def heuristic_triples(chunk: ChunkRecord, *, max_triples: int) -> list[dict[str, Any]]:
    surfaces = extract_surfaces(chunk.text)
    if len(surfaces) < 2:
        return []
    relation_type, base_confidence = relation_type_for(chunk.text)
    triples: list[dict[str, Any]] = []
    subject = surfaces[0]
    for idx, obj in enumerate(surfaces[1 : max_triples + 1], start=1):
        payload = {
            "schema": TRIPLE_SCHEMA,
            "id": "",
            "layer": "unconscious",
            "authority": "retrieval_only",
            "subject": subject,
            "predicate": relation_type,
            "object": obj,
            "confidence": round(max(0.1, base_confidence - 0.03 * (idx - 1)), 3),
            "entity_metadata": {
                "subject_surface_source": surface_source(subject),
                "object_surface_source": surface_source(obj),
                "subject_normalization_confidence": normalization_confidence(subject),
                "object_normalization_confidence": normalization_confidence(obj),
            },
            "evidence": chunk.text[:1000],
            "source_ref": {
                "chunk_id": chunk.id,
                "source_id": chunk.source_id,
                "ordinal": chunk.ordinal,
                "title": chunk.title,
                "path": chunk.provenance.get("path"),
            },
            "authority_boundary": dict(AUTHORITY_BOUNDARY),
        }
        payload["id"] = stable_hash(payload)
        triples.append(payload)
    return triples


def chat_completion_triples(
    chunk: ChunkRecord,
    *,
    model: str,
    base_url: str,
    max_triples: int,
    timeout: float,
) -> list[dict[str, Any]]:
    system = (
        "You are a knowledge graph builder. Extract only factual "
        "subject-predicate-object triples present in the text. Return only JSON."
    )
    user = (
        "Return a JSON array of objects with keys subject, predicate, object, confidence. "
        "Normalize entity names. These triples are retrieval-only, not proof authority.\n\n"
        f"TEXT:\n{chunk.text[:64000]}"
    )
    body = {
        "model": model,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
        "temperature": 0.1,
        "max_tokens": 8192,
    }
    req = Request(base_url.rstrip("/") + "/chat/completions", data=json.dumps(body).encode("utf-8"))
    req.add_header("Content-Type", "application/json")
    with urlopen(req, timeout=timeout) as resp:
        payload = json.loads(resp.read().decode("utf-8"))
    raw = str(((payload.get("choices") or [{}])[0].get("message") or {}).get("content") or "").strip()
    match = re.search(r"\[[\s\S]*\]", raw)
    if match:
        raw = match.group(0)
    parsed = json.loads(raw)
    if not isinstance(parsed, list):
        return []
    triples: list[dict[str, Any]] = []
    for item in parsed[:max_triples]:
        if not isinstance(item, dict):
            continue
        subject = normalize_surface(str(item.get("subject") or ""))
        predicate = normalize_surface(str(item.get("predicate") or "associated_with"))
        obj = normalize_surface(str(item.get("object") or ""))
        if not subject or not obj:
            continue
        try:
            confidence = float(item.get("confidence", 0.55))
        except Exception:
            confidence = 0.55
        row = {
            "schema": TRIPLE_SCHEMA,
            "id": "",
            "layer": "unconscious",
            "authority": "retrieval_only",
            "subject": subject,
            "predicate": predicate,
            "object": obj,
            "confidence": round(min(1.0, max(0.0, confidence)), 3),
            "entity_metadata": {
                "subject_surface_source": surface_source(subject),
                "object_surface_source": surface_source(obj),
                "subject_normalization_confidence": normalization_confidence(subject),
                "object_normalization_confidence": normalization_confidence(obj),
            },
            "evidence": chunk.text[:1000],
            "source_ref": {
                "chunk_id": chunk.id,
                "source_id": chunk.source_id,
                "ordinal": chunk.ordinal,
                "title": chunk.title,
                "path": chunk.provenance.get("path"),
            },
            "authority_boundary": dict(AUTHORITY_BOUNDARY),
        }
        row["id"] = stable_hash(row)
        triples.append(row)
    return triples


def build_source_and_chunks(
    path: Path,
    *,
    source_kind_override: str,
    max_chars: int,
    overlap_chars: int,
) -> tuple[dict[str, Any], list[ChunkRecord]]:
    text, source_format = extract_text(path)
    resolved = path.resolve()
    source_id = stable_hash({"path": resolved.as_posix(), "content_hash": content_hash(text)})
    source = SourceRecord(
        id=source_id,
        path=path.as_posix(),
        title=path.stem,
        source_kind=source_kind_for(path, source_kind_override),
        source_format=source_format,
        content_hash=content_hash(text),
        source_uri=source_uri(resolved),
    )
    segments = chunk_text_txt2kg(text, chunk_size=max_chars, overlap_size=overlap_chars)
    chunks: list[ChunkRecord] = []
    for ordinal, segment in enumerate(segments, start=1):
        chunk_id = stable_hash({"source_id": source_id, "ordinal": ordinal, "text": segment})
        chunks.append(
            ChunkRecord(
                id=chunk_id,
                source_id=source_id,
                ordinal=ordinal,
                title=f"{path.stem} chunk {ordinal}",
                text=segment,
                tokens=tokenize(segment),
                provenance={
                    "path": path.as_posix(),
                    "sourceUri": source.source_uri,
                    "sourceKind": source.source_kind,
                    "sourceFormat": source.source_format,
                    "contentHash": source.content_hash,
                    "chunkingStrategy": "txt2kg_sentence_aware_overlap",
                },
            )
        )
    return {
        "schema": SOURCE_SCHEMA,
        "id": source.id,
        "path": source.path,
        "title": source.title,
        "source_kind": source.source_kind,
        "source_format": source.source_format,
        "content_hash": source.content_hash,
        "source_uri": source.source_uri,
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }, chunks


def chunk_to_row(chunk: ChunkRecord) -> dict[str, Any]:
    return {
        "schema": CHUNK_SCHEMA,
        "id": chunk.id,
        "chunk_id": chunk.id,
        "source_id": chunk.source_id,
        "title": chunk.title,
        "text": chunk.text,
        "tokens": chunk.tokens,
        "provenance": chunk.provenance,
        "path": chunk.provenance.get("path"),
        "source": chunk.provenance.get("path"),
        "authority": "retrieval_only",
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }


def triples_for_chunk(
    chunk: ChunkRecord,
    *,
    extractor: str,
    max_triples: int,
    ollama_model: str,
    ollama_endpoint: str,
    ollama_timeout: float,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    if extractor == "heuristic":
        return heuristic_triples(chunk, max_triples=max_triples), {
            "chunk_id": chunk.id,
            "extractor_attempted": "heuristic",
            "extractor_used": "heuristic",
            "fallback_reason": None,
        }
    if extractor == "ollama":
        rows = chat_completion_triples(
            chunk,
            model=ollama_model,
            base_url=ollama_endpoint,
            max_triples=max_triples,
            timeout=ollama_timeout,
        )
        return rows, {
            "chunk_id": chunk.id,
            "extractor_attempted": "ollama",
            "extractor_used": "ollama",
            "fallback_reason": None,
        }
    if extractor == "auto":
        try:
            rows = chat_completion_triples(
                chunk,
                model=ollama_model,
                base_url=ollama_endpoint,
                max_triples=max_triples,
                timeout=ollama_timeout,
            )
            if rows:
                return rows, {
                    "chunk_id": chunk.id,
                    "extractor_attempted": "ollama",
                    "extractor_used": "ollama",
                    "fallback_reason": None,
                }
            fallback_reason = "ollama_returned_no_triples"
        except Exception as exc:  # noqa: BLE001
            fallback_reason = str(exc)
        return heuristic_triples(chunk, max_triples=max_triples), {
            "chunk_id": chunk.id,
            "extractor_attempted": "ollama",
            "extractor_used": "heuristic",
            "fallback_reason": fallback_reason,
        }
    raise SystemExit(f"unknown extractor: {extractor}")


def dedupe_triples(rows: list[dict[str, Any]], *, min_confidence: float) -> list[dict[str, Any]]:
    best: dict[tuple[str, str, str], dict[str, Any]] = {}
    for row in rows:
        try:
            confidence = float(row.get("confidence", 0.0))
        except Exception:
            confidence = 0.0
        if confidence < min_confidence:
            continue
        key = (
            str(row.get("subject") or "").strip().lower(),
            str(row.get("predicate") or "").strip().lower(),
            str(row.get("object") or "").strip().lower(),
        )
        if not all(key):
            continue
        current = best.get(key)
        if current is None or confidence > float(current.get("confidence", 0.0)):
            best[key] = row
    return sorted(best.values(), key=lambda item: float(item.get("confidence", 0.0)), reverse=True)


def graph_rows_from_triples(triples: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    entities: dict[str, dict[str, Any]] = {}
    relationships: dict[str, dict[str, Any]] = {}
    for triple in triples:
        subject = str(triple.get("subject") or "").strip()
        predicate = str(triple.get("predicate") or "").strip()
        obj = str(triple.get("object") or "").strip()
        if not subject or not predicate or not obj:
            continue
        subject_key = short_key("entity", subject.lower())
        object_key = short_key("entity", obj.lower())
        edge_key = short_key("rel", f"{subject_key}|{predicate.lower()}|{object_key}")
        entities.setdefault(
            subject_key,
            {
                "_key": subject_key,
                "name": subject,
                "layer": "unconscious",
                "authority": "retrieval_only",
                "authority_boundary": dict(AUTHORITY_BOUNDARY),
            },
        )
        entities.setdefault(
            object_key,
            {
                "_key": object_key,
                "name": obj,
                "layer": "unconscious",
                "authority": "retrieval_only",
                "authority_boundary": dict(AUTHORITY_BOUNDARY),
            },
        )
        relationships[edge_key] = {
            "_key": edge_key,
            "_from": f"txt2kg_entities/{subject_key}",
            "_to": f"txt2kg_entities/{object_key}",
            "type": predicate,
            "confidence": triple.get("confidence"),
            "source_ref": triple.get("source_ref"),
            "layer": "unconscious",
            "authority": "retrieval_only",
            "authority_boundary": dict(AUTHORITY_BOUNDARY),
        }
    return list(entities.values()), list(relationships.values())


def prepare_arango_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    prepared: list[dict[str, Any]] = []
    for row in rows:
        copied = dict(row)
        if "_key" not in copied:
            copied["_key"] = str(copied.get("id") or stable_hash(copied))[:64]
        prepared.append(copied)
    return prepared


def ingest_txt2kg_arango(
    *,
    endpoint: str,
    database: str,
    username: str,
    password: str,
    sources: list[dict[str, Any]],
    chunks: list[dict[str, Any]],
    triples: list[dict[str, Any]],
    entities: list[dict[str, Any]],
    relationships: list[dict[str, Any]],
) -> dict[str, Any]:
    ensure_database(endpoint, database, username, password)
    for collection in TXT2KG_DOCUMENT_COLLECTIONS:
        ensure_collection(endpoint, database, username, password, collection, edge=False)
    for collection in TXT2KG_EDGE_COLLECTIONS:
        ensure_collection(endpoint, database, username, password, collection, edge=True)
    for collection, index_fields in TXT2KG_INDEXES.items():
        for fields in index_fields:
            ensure_index(endpoint, database, username, password, collection, fields)

    batches = {
        "txt2kg_sources": prepare_arango_rows(sources),
        "txt2kg_chunks": prepare_arango_rows(chunks),
        "txt2kg_triples": prepare_arango_rows(triples),
        "txt2kg_entities": prepare_arango_rows(entities),
        "txt2kg_relationships": prepare_arango_rows(relationships),
    }
    for collection, rows in batches.items():
        import_rows(endpoint, database, username, password, collection, rows)
    return {
        "endpoint": endpoint,
        "database": database,
        "collections": {collection: len(rows) for collection, rows in batches.items()},
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }


def make_predigestion_rows(chunks: list[dict[str, Any]], triples: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_chunk: dict[str, list[dict[str, Any]]] = {}
    for triple in triples:
        source_ref = triple.get("source_ref") if isinstance(triple.get("source_ref"), dict) else {}
        chunk_id = str(source_ref.get("chunk_id") or "")
        by_chunk.setdefault(chunk_id, []).append(triple)

    rows: list[dict[str, Any]] = []
    for chunk in chunks:
        chunk_id = str(chunk.get("id") or chunk.get("chunk_id") or "")
        chunk_triples = by_chunk.get(chunk_id, [])
        symbols: list[str] = []
        for triple in chunk_triples:
            symbols.extend([str(triple.get("subject") or ""), str(triple.get("object") or "")])
        claim = ""
        if chunk_triples:
            first = chunk_triples[0]
            claim = f"{first['subject']} {first['predicate']} {first['object']}"
        row = {
            "id": chunk_id,
            "path": chunk.get("path") or chunk.get("source"),
            "title": chunk.get("title"),
            "text": chunk.get("text"),
            "claim": claim,
            "symbols": sorted({symbol for symbol in symbols if symbol}),
            "authority": "semantic",
            "repo_owner_candidates": [],
            "lean_target_candidates": [],
            "authority": "source_text",
        }
        rows.append(row)
    return rows


def make_light_cone_seed_rows(chunks: list[dict[str, Any]], triples: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_chunk: dict[str, list[dict[str, Any]]] = {}
    for triple in triples:
        source_ref = triple.get("source_ref") if isinstance(triple.get("source_ref"), dict) else {}
        chunk_id = str(source_ref.get("chunk_id") or "")
        by_chunk.setdefault(chunk_id, []).append(triple)

    rows: list[dict[str, Any]] = []
    for chunk in chunks:
        chunk_id = str(chunk.get("id") or chunk.get("chunk_id") or "")
        chunk_triples = by_chunk.get(chunk_id, [])
        entities = sorted(
            {
                str(value)
                for triple in chunk_triples
                for value in (triple.get("subject"), triple.get("object"))
                if value
            }
        )
        query_terms = entities[:12] or list(chunk.get("tokens") or [])[:12]
        row = {
            "schema": LIGHT_CONE_SEED_SCHEMA,
            "id": "",
            "authority": "navigation",
            "layer": "unconscious",
            "source_chunk_id": chunk_id,
            "source_ref": {
                "path": chunk.get("path") or chunk.get("source"),
                "title": chunk.get("title"),
            },
            "query_terms": query_terms,
            "entities": entities,
            "triple_ids": [str(triple.get("id")) for triple in chunk_triples if triple.get("id")],
            "suggested_anchor_mode": "scc_anchor_first",
            "required_descent": "raw_lean_witness",
            "forbidden_authority_claims": [
                "graph_is_proof",
                "triple_is_theorem",
                "hive_task_is_admission",
            ],
            "authority_boundary": dict(AUTHORITY_BOUNDARY),
        }
        row["id"] = stable_hash(row)
        rows.append(row)
    return rows


def source_kind_for_predigestion(source_rows: list[dict[str, Any]], override: str) -> str:
    if override != "auto":
        return override
    kinds = {str(row.get("source_kind") or "") for row in source_rows}
    if kinds == {"blackbook"}:
        return "blackbook"
    if kinds == {"paper"}:
        return "paper"
    if "blackbook" in kinds:
        return "blackbook"
    if "paper" in kinds:
        return "paper"
    return "doc"


def run_pipeline(args: argparse.Namespace) -> dict[str, Any]:
    load_repo_arango_env(REPO_ROOT)
    arango_endpoint_resolved = args.arango_endpoint or arango_endpoint()
    arango_database_resolved = args.arango_database or arango_database()
    arango_username_resolved = args.arango_username or arango_username()
    arango_password_resolved = args.arango_password or arango_password()

    input_files = iter_input_files([Path(raw) for raw in args.input])
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    source_rows: list[dict[str, Any]] = []
    chunk_records: list[ChunkRecord] = []
    for path in input_files:
        source, chunks = build_source_and_chunks(
            path,
            source_kind_override=args.source_kind,
            max_chars=args.chunk_max_chars,
            overlap_chars=args.chunk_overlap_chars,
        )
        source_rows.append(source)
        chunk_records.extend(chunks)

    chunk_rows = [chunk_to_row(chunk) for chunk in chunk_records]
    triple_rows_raw: list[dict[str, Any]] = []
    extraction_errors: list[dict[str, Any]] = []
    extractor_events: list[dict[str, Any]] = []
    for chunk in chunk_records:
        try:
            rows, event = triples_for_chunk(
                chunk,
                extractor=args.extractor,
                max_triples=args.max_triples_per_chunk,
                ollama_model=args.ollama_model,
                ollama_endpoint=args.ollama_endpoint,
                ollama_timeout=args.ollama_timeout,
            )
            triple_rows_raw.extend(rows)
            extractor_events.append(event)
        except Exception as exc:  # noqa: BLE001
            extraction_errors.append({"chunk_id": chunk.id, "error": str(exc)})

    triple_rows = dedupe_triples(triple_rows_raw, min_confidence=args.min_triple_confidence)
    entity_rows, relationship_rows = graph_rows_from_triples(triple_rows)

    sources_path = output_dir / "txt2kg_sources.jsonl"
    chunks_path = output_dir / "txt2kg_chunks.jsonl"
    triples_path = output_dir / "txt2kg_triples.jsonl"
    entities_path = output_dir / "txt2kg_entities.jsonl"
    relationships_path = output_dir / "txt2kg_relationships.jsonl"
    light_cone_seeds_path = output_dir / "context_light_cone_seed.jsonl"
    predigestion_input_path = output_dir / "predigestion_input.jsonl"
    claims_path = output_dir / "claims.jsonl"
    claims_summary_path = output_dir / "claims_summary.json"
    tasks_path = output_dir / "hive_predigestion_tasks.jsonl"
    tasks_summary_path = output_dir / "hive_predigestion_tasks_summary.json"
    summary_path = output_dir / "txt2kg_hive_ingest_summary.json"

    write_jsonl(sources_path, source_rows)
    write_jsonl(chunks_path, chunk_rows)
    write_jsonl(triples_path, triple_rows)
    write_jsonl(entities_path, entity_rows)
    write_jsonl(relationships_path, relationship_rows)

    predigestion_rows = make_predigestion_rows(chunk_rows, triple_rows)
    write_jsonl(predigestion_input_path, predigestion_rows)
    light_cone_seed_rows = make_light_cone_seed_rows(chunk_rows, triple_rows)
    write_jsonl(light_cone_seeds_path, light_cone_seed_rows)

    predigestion_source_kind = source_kind_for_predigestion(source_rows, args.predigestion_source_kind)
    claim_rows = build_packets(predigestion_input_path, source_kind=predigestion_source_kind, risk=args.risk)
    write_claim_jsonl(claims_path, claim_rows)
    claim_summary = claim_summary_for(claim_rows, input_path=predigestion_input_path, out=claims_path)
    write_json(claims_summary_path, claim_summary)

    task_rows: list[dict[str, Any]] = []
    if args.emit_hive_tasks:
        task_rows = build_tasks(claims_path, task_kind=args.task_kind)
        write_task_jsonl(tasks_path, task_rows)
        task_summary = task_summary_for(task_rows, claims_path=claims_path, out=tasks_path)
        write_json(tasks_summary_path, task_summary)
    else:
        task_summary = {
            "schema": "hive.packet.predigestion_task.summary.v1",
            "records": 0,
            "skipped": True,
        }

    arango_report: dict[str, Any] | None = None
    if args.ingest_arango:
        arango_report = ingest_txt2kg_arango(
            endpoint=arango_endpoint_resolved,
            database=arango_database_resolved,
            username=arango_username_resolved,
            password=arango_password_resolved,
            sources=source_rows,
            chunks=chunk_rows,
            triples=triple_rows,
            entities=entity_rows,
            relationships=relationship_rows,
        )

    summary = {
        "schema": SUMMARY_SCHEMA,
        "inputs": [str(path) for path in input_files],
        "extractor": args.extractor,
        "artifacts": {
            "sources": str(sources_path),
            "chunks": str(chunks_path),
            "triples": str(triples_path),
            "entities": str(entities_path),
            "relationships": str(relationships_path),
            "context_light_cone_seeds": str(light_cone_seeds_path),
            "predigestion_input": str(predigestion_input_path),
            "claims": str(claims_path),
            "claims_summary": str(claims_summary_path),
            "hive_tasks": str(tasks_path) if args.emit_hive_tasks else None,
            "hive_tasks_summary": str(tasks_summary_path) if args.emit_hive_tasks else None,
        },
        "counts": {
            "sources": len(source_rows),
            "chunks": len(chunk_rows),
            "triples": len(triple_rows),
            "raw_triples": len(triple_rows_raw),
            "entities": len(entity_rows),
            "relationships": len(relationship_rows),
            "context_light_cone_seeds": len(light_cone_seed_rows),
            "claims": len(claim_rows),
            "hive_tasks": len(task_rows),
            "extraction_errors": len(extraction_errors),
            "extractor_fallbacks": sum(1 for event in extractor_events if event.get("extractor_used") == "heuristic" and event.get("extractor_attempted") == "ollama"),
        },
        "extractor_events_sample": extractor_events[:20],
        "extraction_errors": extraction_errors[:20],
        "arango_ingest": arango_report,
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }
    write_json(summary_path, summary)
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", action="append", required=True, help="Input file or directory")
    parser.add_argument("--output-dir", default="artifacts/alexandria/txt2kg_hive")
    parser.add_argument("--source-kind", default="auto", choices=["auto", "paper", "blackbook", "doc", "old_doc"])
    parser.add_argument(
        "--predigestion-source-kind",
        default="auto",
        choices=["auto", "paper", "blackbook", "doc", "old_doc"],
    )
    parser.add_argument("--risk", default="source_text", choices=["source_text", "metaphor", "informal", "formalizable", "already_supported", "unsupported"])
    parser.add_argument("--chunk-max-chars", type=int, default=20000)
    parser.add_argument("--chunk-overlap-chars", type=int)
    parser.add_argument("--extractor", default="auto", choices=["auto", "heuristic", "ollama"])
    parser.add_argument("--max-triples-per-chunk", type=int, default=8)
    parser.add_argument("--min-triple-confidence", type=float, default=0.6)
    parser.add_argument("--ollama-model", default="llama3.1:8b")
    parser.add_argument("--ollama-endpoint", default="http://localhost:11434/v1")
    parser.add_argument("--ollama-timeout", type=float, default=30.0)
    parser.add_argument("--emit-hive-tasks", action="store_true")
    parser.add_argument("--ingest-arango", action="store_true")
    parser.add_argument("--arango-endpoint")
    parser.add_argument("--arango-database")
    parser.add_argument("--arango-username")
    parser.add_argument("--arango-password")
    parser.add_argument(
        "--task-kind",
        default="map_claim_to_owner_surface",
        choices=[
            "formalize_claim",
            "map_claim_to_owner_surface",
            "extract_hidden_hypotheses",
            "construct_counterexample_or_guard",
            "find_existing_repo_support",
        ],
    )
    args = parser.parse_args()
    if args.chunk_max_chars <= 0:
        raise SystemExit("--chunk-max-chars must be positive")
    if args.chunk_overlap_chars is None:
        args.chunk_overlap_chars = min(1000, max(0, args.chunk_max_chars // 10))
    if args.chunk_overlap_chars < 0:
        raise SystemExit("--chunk-overlap-chars must be non-negative")
    if args.chunk_overlap_chars >= args.chunk_max_chars:
        raise SystemExit("--chunk-overlap-chars must be smaller than --chunk-max-chars")
    if args.max_triples_per_chunk <= 0:
        raise SystemExit("--max-triples-per-chunk must be positive")
    run_pipeline(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
